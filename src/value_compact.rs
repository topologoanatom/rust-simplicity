// SPDX-License-Identifier: CC0-1.0

//! # Simplicity values
//!
//! Simplicity processes data in terms of [`Value`]s,
//! i.e., inputs, intermediate results and outputs.

use crate::dag::{Dag, DagLike};
use crate::types::{CompleteBound, Final};
use crate::{BitIter, Tmr};

use crate::{BitCollector, EarlyEndOfStreamError};
use core::{cmp, fmt, iter};
use std::collections::VecDeque;
use std::hash::Hash;
use std::sync::Arc;

/// A Simplicity value.
#[derive(Clone)]
pub struct ValueCompact {
    /// Stores right aligned compact bits of value
    inner: Arc<[u8]>,
    /// An offset, in bits, at which the actual data starts. This is useful
    /// because it allows constructing sub-values of a value without needing
    /// to construct a new `inner` with all the bits offset.
    compact_bits: usize,
    /// The Simplicity type of the value.
    ty: Arc<Final>,
}

impl PartialEq for ValueCompact {
    fn eq(&self, other: &Self) -> bool {
        self.ty == other.ty
            && self.compact_bits == other.compact_bits
            && self.raw_bytes() == other.raw_bytes()
    }
}
impl Eq for ValueCompact {}

/// Reference to a value, or to a sub-value of a value.
#[derive(Debug, Clone, Copy)]
pub struct ValueRef<'v> {
    inner: &'v Arc<[u8]>,
    bit_offset: usize,
    ty: &'v Arc<Final>,
}

impl<'v> ValueRef<'v> {
    /// Check if the value is a unit.
    pub fn is_unit(&self) -> bool {
        self.ty.is_unit()
    }

    /// Returns an iterator over the bits of this value.
    pub fn iter_bits(&self) -> impl Iterator<Item = bool> + 'v {
        let start_byte = self.bit_offset / 8;
        let start_bit = self.bit_offset % 8;
        let len = self.len();

        let mut iter = BitIter::new(self.inner[start_byte..].iter().copied());

        for _ in 0..start_bit {
            iter.next();
        }

        iter.take(len)
    }

    /// Helper function to read the first bit of a value
    ///
    /// If the first bit is not available (e.g. if the value has zero size)
    /// then returns None.
    fn first_bit(&self) -> Option<bool> {
        let mask = if self.bit_offset % 8 == 0 {
            0x80
        } else {
            1 << (7 - self.bit_offset % 8)
        };
        let res = self
            .inner
            .get(self.bit_offset / 8)
            .map(|x| x & mask == mask);
        res
    }

    pub fn len(&self) -> usize {
        let mut stack = vec![self.ty.bound()];

        let mut bits = BitIter::new(self.inner.iter().copied());
        for _ in 0..self.bit_offset {
            bits.next();
        }

        let mut size = 0;

        while let Some(ty) = stack.pop() {
            match ty {
                CompleteBound::Unit => continue,
                CompleteBound::Sum(left, right) => {
                    let bit = bits.next();
                    size += 1;
                    if bit == Some(true) {
                        stack.push(right.bound());
                    } else {
                        stack.push(left.bound());
                    }
                }
                CompleteBound::Product(left, right) => {
                    stack.push(right.bound());
                    stack.push(left.bound());
                }
            }
        }

        size
    }

    /// Access the inner value of a left sum value.
    pub fn as_left(&self) -> Option<Self> {
        if self.first_bit() == Some(false) {
            if let Some((lty, _)) = self.ty.as_sum() {
                Some(Self {
                    inner: self.inner,
                    bit_offset: self.bit_offset + 1,
                    ty: lty,
                })
            } else {
                None
            }
        } else {
            None
        }
    }

    /// Access the inner value of a right sum value.
    pub fn as_right(&self) -> Option<Self> {
        if self.first_bit() == Some(true) {
            if let Some((_, rty)) = self.ty.as_sum() {
                Some(Self {
                    inner: self.inner,
                    bit_offset: self.bit_offset + 1,
                    ty: rty,
                })
            } else {
                None
            }
        } else {
            None
        }
    }

    /// Access the inner values of a product value.
    pub fn as_product(&self) -> Option<(Self, Self)> {
        if let Some((lty, rty)) = self.ty.as_product() {
            let left = Self {
                inner: self.inner,
                bit_offset: self.bit_offset,
                ty: lty,
            };
            let right = Self {
                inner: self.inner,
                bit_offset: self.bit_offset + left.len(),
                ty: rty,
            };
            Some((left, right))
        } else {
            None
        }
    }

    /// Convert the reference back to a value.
    pub fn to_value(&self) -> ValueCompact {
        ValueCompact {
            inner: Arc::clone(self.inner),
            compact_bits: self.inner.len() * 8 - self.bit_offset,
            ty: Arc::clone(self.ty),
        }
    }
}

/// Helper function to copy `nbits` bits from `src`, starting at bit-offset `src_offset`,
/// into `dst`, starting at bit-offset `dst_offset`.
///
/// Thanks ChatGPT for suggesting we extract this function.
fn copy_bits(src: &[u8], src_offset: usize, dst: &mut [u8], dst_offset: usize, nbits: usize) {
    debug_assert!(src.len() * 8 >= nbits);
    debug_assert!(dst.len() * 8 >= nbits);
    // For each bit i in 0..nbits, extract the bit from `src`
    // and insert it into `dst`.
    for i in 0..nbits {
        let bit = (src[(src_offset + i) / 8] >> (7 - (src_offset + i) % 8)) & 1;
        dst[(dst_offset + i) / 8] |= bit << (7 - (dst_offset + i) % 8);
    }
}

fn set_bit(data: &mut [u8], pos: usize, val: bool) {
    debug_assert!(pos < data.len() * 8);
    let mask = 1 << (7 - (pos % 8));
    if val {
        data[pos / 8] |= mask;
    } else {
        data[pos / 8] &= !mask;
    }
}

/// TODO: formulate it elegantly
/// Main purpose of this enum is avoiding alocation after `product_bits`.
/// Original version creates `Arc` (potentially just cloning source), but then,
/// inside `left/right` is may potentially need new allocation, when trying to write sum bit
enum ConstructionBits {
    ToCopy(Arc<[u8]>),
    Owned(Box<[u8]>),
}

impl Into<Arc<[u8]>> for ConstructionBits {
    fn into(self) -> Arc<[u8]> {
        match self {
            Self::Owned(buffer) => Arc::from(buffer),
            Self::ToCopy(arc) => arc,
        }
    }
}

impl Into<Box<[u8]>> for ConstructionBits {
    fn into(self) -> Box<[u8]> {
        match self {
            Self::Owned(buffer) => buffer,
            Self::ToCopy(arc) => arc.as_ref().into(),
        }
    }
}

// TODO: maybe bit_lengths are redundant
fn product_bits(
    left: Option<(&Arc<[u8]>, usize)>,
    left_bit_length: usize,
    right: Option<(&Arc<[u8]>, usize)>,
    right_bit_length: usize,
) -> (ConstructionBits, usize) {
    match (left_bit_length, right_bit_length) {
        (0, 0) => (ConstructionBits::Owned(Vec::new().into_boxed_slice()), 0),

        (left_size, 0) => {
            if let Some(x) = left {
                (ConstructionBits::ToCopy(Arc::clone(x.0)), x.1)
            } else {
                (
                    ConstructionBits::Owned(vec![0; left_size.div_ceil(8)].into_boxed_slice()),
                    left_size,
                )
            }
        }

        (0, right_size) => {
            if let Some(x) = right {
                (ConstructionBits::ToCopy(Arc::clone(x.0)), x.1)
            } else {
                (
                    ConstructionBits::Owned(vec![0; right_size.div_ceil(8)].into_boxed_slice()),
                    right_size,
                )
            }
        }

        (lhs_bit_len, rhs_bit_len) => {
            let compact_len = lhs_bit_len + rhs_bit_len;
            let mut res = vec![0; compact_len.div_ceil(8)].into_boxed_slice();
            let compact_start = res.len() * 8 - compact_len;

            if let Some((source, compact_size)) = left {
                copy_bits(
                    source,
                    source.len() * 8 - compact_size,
                    &mut res,
                    compact_start,
                    lhs_bit_len,
                );
            }
            if let Some((source, compact_size)) = right {
                copy_bits(
                    &source,
                    source.len() * 8 - compact_size,
                    &mut res,
                    lhs_bit_len + compact_start,
                    rhs_bit_len,
                );
            }

            (ConstructionBits::Owned(res), compact_len)
        }
    }
}

fn shift_right(bitmap: &mut [u8], shift: usize) {
    debug_assert!(shift < 8);

    if bitmap.len() == 0 {
        return;
    }

    let mask = !(0xFF >> shift) as u8;
    let mut carry = 0;

    for byte in bitmap {
        let next_carry = *byte & mask;
        *byte <<= shift;
        *byte |= carry >> (8 - shift);
        carry = next_carry;
    }
}

fn push_bit(bit: bool, bit_len: &mut usize, buffer: &mut Vec<u8>) {
    if *bit_len % 8 == 0 {
        buffer.push(0);
    }
    if bit {
        *buffer.last_mut().unwrap() |= 1 << (7 - (*bit_len % 8));
    }
    *bit_len += 1;
}

impl ValueCompact {
    /// Make a cheap copy of the value.
    pub fn shallow_clone(&self) -> Self {
        Self {
            inner: Arc::clone(&self.inner),
            compact_bits: self.compact_bits,
            ty: Arc::clone(&self.ty),
        }
    }
    pub fn raw_len(&self) -> usize {
        self.inner.len() * 8
    }

    pub fn len(&self) -> usize {
        self.as_ref().len()
    }

    pub fn raw_bytes(&self) -> &[u8] {
        let byte_width = self.compact_bits.div_ceil(8);
        let start_index = self.inner.len() - byte_width;
        &self.inner[start_index..]
    }

    /// Access the type of the value.
    pub fn ty(&self) -> &Final {
        &self.ty
    }

    /// Create the unit value.
    pub fn unit() -> Self {
        Self {
            inner: Arc::new([]),
            compact_bits: 0,
            ty: Final::unit(),
        }
    }

    /// Create a none value.
    pub fn none(right: Arc<Final>) -> Self {
        Self::left(ValueCompact::unit(), right)
    }

    /// Create a some value.
    pub fn some(inner: Self) -> Self {
        Self::right(Final::unit(), inner)
    }

    /// Create a left value that wraps the given `inner` value.
    pub fn left(inner: Self, right: Arc<Final>) -> Self {
        let (tag_len, ty_len) = if inner.raw_len() > inner.compact_bits {
            (0, inner.compact_bits)
        } else {
            (1, inner.compact_bits)
        };

        let (new_inner, _) = product_bits(
            None,
            tag_len,
            Some((&inner.inner, inner.compact_bits)),
            ty_len,
        );

        // assume that tag bit is 0 for now

        Self {
            inner: new_inner.into(),
            compact_bits: inner.compact_bits + 1,
            ty: Final::sum(Arc::clone(&inner.ty), right),
        }
    }

    /// Create a left value that wraps the given `inner` value.
    pub fn right(left: Arc<Final>, inner: Self) -> Self {
        let (tag_len, ty_len) = if inner.raw_len() > inner.compact_bits {
            (0, inner.compact_bits)
        } else {
            (1, inner.compact_bits)
        };

        let (new_inner, _) = product_bits(
            None,
            tag_len,
            Some((&inner.inner, inner.compact_bits)),
            ty_len,
        );

        let mut new_inner: Box<[u8]> = new_inner.into();
        let inner_len = new_inner.len();
        set_bit(&mut new_inner, inner_len * 8 - inner.compact_bits - 1, true);

        Self {
            inner: new_inner.into(),
            compact_bits: inner.compact_bits + 1,
            ty: Final::sum(left, Arc::clone(&inner.ty)),
        }
    }

    /// Create a product value that wraps the given `left` and `right` values.
    pub fn product(left: Self, right: Self) -> Self {
        let (new_inner, compact_bits) = product_bits(
            Some((&left.inner, left.compact_bits)),
            left.compact_bits,
            Some((&right.inner, right.compact_bits)),
            right.compact_bits,
        );

        Self {
            inner: new_inner.into(),
            compact_bits,
            ty: Final::product(Arc::clone(&left.ty), Arc::clone(&right.ty)),
        }
    }

    /// Create a 1-bit integer.
    ///
    /// ## Panics
    ///
    /// The value is out of range.
    pub fn u1(value: u8) -> Self {
        assert!(value <= 1, "{} out of range for Value::u1", value);
        Self {
            inner: Arc::new([value]),
            compact_bits: 1,
            ty: Final::two_two_n(0),
        }
    }

    /// Create a 2-bit integer.
    ///
    /// ## Panics
    ///
    /// The value is out of range.
    pub fn u2(value: u8) -> Self {
        assert!(value <= 3, "{} out of range for Value::u2", value);
        Self {
            inner: Arc::new([value]),
            compact_bits: 2,
            ty: Final::two_two_n(1),
        }
    }

    /// Create a 4-bit integer.
    ///
    /// ## Panics
    ///
    /// The value is ouf of range.
    pub fn u4(value: u8) -> Self {
        assert!(value <= 15, "{} out of range for Value::u2", value);
        Self {
            inner: Arc::new([value]),
            compact_bits: 4,
            ty: Final::two_two_n(2),
        }
    }

    /// Create an 8-bit integer.
    pub fn u8(value: u8) -> Self {
        Self {
            inner: Arc::new([value]),
            compact_bits: 8,
            ty: Final::two_two_n(3),
        }
    }

    /// Create a 16-bit integer.
    pub fn u16(bytes: u16) -> Self {
        Self {
            inner: Arc::new(bytes.to_be_bytes()),
            compact_bits: 16,
            ty: Final::two_two_n(4),
        }
    }

    /// Create a 32-bit integer.
    pub fn u32(bytes: u32) -> Self {
        Self {
            inner: Arc::new(bytes.to_be_bytes()),
            compact_bits: 32,
            ty: Final::two_two_n(5),
        }
    }

    /// Create a 64-bit integer.
    pub fn u64(bytes: u64) -> Self {
        Self {
            inner: Arc::new(bytes.to_be_bytes()),
            compact_bits: 64,
            ty: Final::two_two_n(6),
        }
    }

    /// Create a 128-bit integer.
    pub fn u128(bytes: u128) -> Self {
        Self {
            inner: Arc::new(bytes.to_be_bytes()),
            compact_bits: 128,
            ty: Final::two_two_n(7),
        }
    }

    /// Create a 256-bit integer.
    pub fn u256(bytes: [u8; 32]) -> Self {
        Self {
            inner: Arc::new(bytes),
            compact_bits: 256,
            ty: Final::two_two_n(8),
        }
    }

    /// Create a 512-bit integer.
    pub fn u512(bytes: [u8; 64]) -> Self {
        Self {
            inner: Arc::new(bytes),
            compact_bits: 512,
            ty: Final::two_two_n(9),
        }
    }

    /// A reference to this value, which can be recursed over.
    pub fn as_ref(&self) -> ValueRef<'_> {
        ValueRef {
            inner: &self.inner,
            bit_offset: self.inner.len() * 8 - self.compact_bits,
            ty: &self.ty,
        }
    }

    /// Prune the value down to the given type.
    ///
    /// The pruned type must be _smaller than or equal to_ the current type of the value.
    /// Otherwise, this method returns `None`.
    ///
    /// ## Smallness
    ///
    /// - `T` ≤ `T` for all types `T`
    /// - `1` ≤ `T` for all types `T`
    /// - `A1 + B1` ≤ `A2 + B2` if `A1` ≤ `A2` and `B1` ≤ `B2`
    /// - `A1 × B1` ≤ `A2 × B2` if `A1` ≤ `A2` and `B1` ≤ `B2`
    ///
    /// ## Pruning
    ///
    /// - `prune( v: T, 1 )` = `(): 1`
    /// - `prune( L(l): A1 + B1, A2 + B2 )` = `prune(l: A1, A2) : A2 + B2`
    /// - `prune( R(r): A1 + B1, A2 + B2 )` = `prune(r: B1, B2) : A2 + B2`
    /// - `prune( (l, r): A1 × B1, A2 × B2 )` = `( prune(l: A1, A2), prune(r: B1, B2): A2 × B2`
    pub fn prune(&self, pruned_ty: &Final) -> Option<Self> {
        enum Task<'v, 'ty> {
            Prune(ValueRef<'v>, &'ty Final),
            MakeLeft(Arc<Final>),
            MakeRight(Arc<Final>),
            MakeProduct,
        }

        let mut stack = vec![Task::Prune(self.as_ref(), pruned_ty)];
        let mut output = vec![];

        while let Some(task) = stack.pop() {
            match task {
                Task::Prune(value, pruned_ty) if value.ty.as_ref() == pruned_ty => {
                    output.push(value.to_value())
                }
                Task::Prune(value, pruned_ty) => match pruned_ty.bound() {
                    CompleteBound::Unit => output.push(ValueCompact::unit()),
                    CompleteBound::Sum(l_ty, r_ty) => {
                        if let Some(l_value) = value.as_left() {
                            stack.push(Task::MakeLeft(Arc::clone(r_ty)));
                            stack.push(Task::Prune(l_value, l_ty));
                        } else {
                            let r_value = value.as_right()?;
                            stack.push(Task::MakeRight(Arc::clone(l_ty)));
                            stack.push(Task::Prune(r_value, r_ty));
                        }
                    }
                    CompleteBound::Product(l_ty, r_ty) => {
                        let (l_value, r_value) = value.as_product()?;
                        stack.push(Task::MakeProduct);
                        stack.push(Task::Prune(r_value, r_ty));
                        stack.push(Task::Prune(l_value, l_ty));
                    }
                },
                Task::MakeLeft(r_ty) => {
                    let l_value = output.pop().unwrap();
                    output.push(ValueCompact::left(l_value, r_ty));
                }
                Task::MakeRight(l_ty) => {
                    let r_value = output.pop().unwrap();
                    output.push(ValueCompact::right(l_ty, r_value));
                }
                Task::MakeProduct => {
                    let r_value = output.pop().unwrap();
                    let l_value = output.pop().unwrap();
                    output.push(ValueCompact::product(l_value, r_value));
                }
            }
        }

        debug_assert_eq!(output.len(), 1);
        output.pop()
    }
}

impl ValueCompact {
    /// Decode a value of the given type from its compact bit encoding.
    pub fn from_compact_bits<I: Iterator<Item = u8>>(
        bits: &mut BitIter<I>,
        ty: &Final,
    ) -> Result<Self, EarlyEndOfStreamError> {
        let mut buffer = Vec::new();
        let mut bit_len = 0;

        let mut stack = vec![ty.bound()];

        while let Some(ty) = stack.pop() {
            match ty {
                CompleteBound::Unit => continue,
                CompleteBound::Sum(left, right) => {
                    let bit = bits.next();

                    match bit {
                        None => return Err(EarlyEndOfStreamError),
                        Some(false) => {
                            push_bit(false, &mut bit_len, &mut buffer);
                            stack.push(left.bound());
                        }
                        Some(true) => {
                            push_bit(true, &mut bit_len, &mut buffer);
                            stack.push(right.bound());
                        }
                    }
                }
                CompleteBound::Product(left, right) => {
                    stack.push(right.bound());
                    stack.push(left.bound());
                }
            }
        }

        if bit_len == 0 {
            return Ok(Self {
                inner: Arc::new([]),
                compact_bits: 0,
                ty: Arc::new(ty.clone()),
            });
        }

        let unused_bits = (8 - (bit_len % 8)) % 8;

        if unused_bits > 0 {
            shift_right(&mut buffer, unused_bits);
        }

        Ok(Self {
            inner: buffer.into(),
            compact_bits: bit_len,
            ty: Arc::new(ty.clone()),
        })
    }

    /// Decode a value of the given type from its padded bit encoding.
    pub fn from_padded_bits<I: Iterator<Item = u8>>(
        bits: &mut BitIter<I>,
        ty: &Final,
    ) -> Result<Self, EarlyEndOfStreamError> {
        let mut buffer = Vec::new();
        let mut bit_len = 0;

        let mut stack = vec![ty.bound()];

        while let Some(ty) = stack.pop() {
            match ty {
                CompleteBound::Unit => continue,
                CompleteBound::Sum(left, right) => {
                    let tag = bits.next();
                    let left_size = left.bit_width();
                    let right_size = right.bit_width();
                    let max = std::cmp::max(left_size, right_size);

                    match tag {
                        None => return Err(EarlyEndOfStreamError),
                        Some(false) => {
                            if max == right_size {
                                for _ in 0..(max - left_size) {
                                    bits.next();
                                }
                            }

                            push_bit(false, &mut bit_len, &mut buffer);
                            stack.push(left.bound());
                        }
                        Some(true) => {
                            if max == left_size {
                                for _ in 0..(max - right_size) {
                                    bits.next();
                                }
                            }
                            push_bit(true, &mut bit_len, &mut buffer);
                            stack.push(right.bound());
                        }
                    }
                }
                CompleteBound::Product(left, right) => {
                    stack.push(right.bound());
                    stack.push(left.bound());
                }
            }
        }

        if bit_len == 0 {
            return Ok(Self {
                inner: Arc::new([]),
                compact_bits: 0,
                ty: Arc::new(ty.clone()),
            });
        }

        let unused_bits = (8 - (bit_len % 8)) % 8;

        if unused_bits > 0 {
            shift_right(&mut buffer, unused_bits);
        }

        Ok(Self {
            inner: buffer.into(),
            compact_bits: bit_len,
            ty: Arc::new(ty.clone()),
        })
    }
}

impl fmt::Debug for ValueCompact {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("Value")
            .field("value", &format_args!("{}", self))
            .field("ty", &self.ty)
            .field("raw_value", &self.inner)
            .field("compact_bits", &self.compact_bits)
            .finish()
    }
}

impl fmt::Display for ValueCompact {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        enum S<'v> {
            Disp(ValueRef<'v>),
            DispCh(char),
        }

        let mut stack = Vec::with_capacity(1024);
        stack.push(S::Disp(self.as_ref()));

        'main_loop: while let Some(next) = stack.pop() {
            let value = match next {
                S::Disp(ref value) => value,
                S::DispCh(ch) => {
                    write!(f, "{}", ch)?;
                    continue;
                }
            };

            if value.is_unit() {
                f.write_str("ε")?;
            } else {
                for tmr in &Tmr::TWO_TWO_N {
                    if value.ty.tmr() == *tmr {
                        if value.ty.bit_width() < 4 {
                            f.write_str("0b")?;
                            for bit in value.iter_bits() {
                                f.write_str(if bit { "1" } else { "0" })?;
                            }
                        } else {
                            f.write_str("0x")?;

                            let mut iter = value.iter_bits();
                            while let (Some(a), Some(b), Some(c), Some(d)) =
                                (iter.next(), iter.next(), iter.next(), iter.next())
                            {
                                let n = (u8::from(a) << 3)
                                    + (u8::from(b) << 2)
                                    + (u8::from(c) << 1)
                                    + u8::from(d);
                                write!(f, "{:x}", n)?;
                            }
                        }
                        continue 'main_loop;
                    }
                }

                if let Some(l_value) = value.as_left() {
                    f.write_str("L(")?;
                    stack.push(S::DispCh(')'));
                    stack.push(S::Disp(l_value));
                } else if let Some(r_value) = value.as_right() {
                    f.write_str("R(")?;
                    stack.push(S::DispCh(')'));
                    stack.push(S::Disp(r_value));
                } else if let Some((l_value, r_value)) = value.as_product() {
                    stack.push(S::DispCh(')'));
                    stack.push(S::Disp(r_value));
                    stack.push(S::DispCh(','));
                    stack.push(S::Disp(l_value));
                    stack.push(S::DispCh('('));
                } else {
                    unreachable!("Value structure must match Type structure")
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bit_encoding::{BitCollector as _, BitIter};
    use crate::jet::type_name::TypeName;

    #[test]
    fn value_compact_len() {
        let v = ValueCompact::u4(6);
        let s_v = ValueCompact::some(v.shallow_clone());
        let n_v = ValueCompact::none(Final::two_two_n(2));

        assert_eq!(v.len(), 4);
        assert_eq!(v.raw_len(), 8);
        assert_eq!(s_v.len(), 5);
        assert_eq!(s_v.raw_len(), 8);
        assert_eq!(n_v.len(), 1);
        assert_eq!(n_v.raw_len(), 8);
    }

    #[test]
    fn value_compact_display() {
        // Only test a couple values becasue we probably want to change this
        // at some point and will have to redo this test.
        assert_eq!(ValueCompact::u1(0).to_string(), "0b0",);
        assert_eq!(ValueCompact::u1(1).to_string(), "0b1",);
        assert_eq!(ValueCompact::u4(6).to_string(), "0x6",);
    }

    #[test]
    fn prune_compact_regression_1() {
        // Found this when fuzzing Elements; unsure how to reduce it further.
        let nontrivial_sum = ValueCompact::product(
            ValueCompact::right(Final::two_two_n(4), ValueCompact::u16(0)),
            ValueCompact::u8(0),
        );
        // Formatting should succeed and have no effect.
        let _ = format!("{nontrivial_sum}");
        // Pruning should succeed and have no effect.
        assert_eq!(
            nontrivial_sum.prune(nontrivial_sum.ty()),
            Some(nontrivial_sum)
        );
    }
}

//! This crate provides the `BoolVec` structure. This is basically a wrapper around a `Vec<u8>`
//! where each byte is interpreted as 8 `bool`.
//! 
//! # Example
//! ```rust
//! // Create a new `BoolVec`
//! use boolvec::BoolVec;
//! 
//! let mut vec = BoolVec::new();
//! 
//! // You can push data onto it
//! vec.push(true);
//! vec.push(false);
//! 
//! // ... retreve it
//! assert_eq!(vec.get(0), Some(true));
//! assert_eq!(vec.get(3), None);
//! 
//! // ... update it
//! vec.set(0, false);
//! assert_eq!(vec.get(0), Some(false));
//! 
//! // You can get a reference to an unaligned boolean
//! let mut boolean = vec.get_mut(1).unwrap();
//! assert_eq!(boolean.get(), false);
//! 
//! boolean.set(true);
//! assert_eq!(vec.get(1), Some(true));
//! 
//! // You can also iterate over this data (mutably or not).
//! let mut iter = vec.iter_mut();
//! 
//! iter.next().unwrap().set(true);
//! iter.next().unwrap().set(false);
//! 
//! let mut iter = vec.iter();
//! 
//! assert_eq!(iter.next(), Some(true));
//! assert_eq!(iter.next(), Some(false));
//! assert_eq!(iter.next(), None);
//! ```

use std::ptr::NonNull;
use std::marker::PhantomData;
use std::cmp::Ord;
use std::iter::Iterator;
use std::iter::ExactSizeIterator;
use std::iter::DoubleEndedIterator;
use std::iter::FromIterator;
use std::iter::FusedIterator;
use std::ops::{
    BitAnd, BitAndAssign,
    BitOr, BitOrAssign,
    BitXor, BitXorAssign,
};
use serde::{Serialize, Deserialize};

mod bool_ref;
use bool_ref::*;

pub use bool_ref::RefBool;
pub use bool_ref::RefBoolMut;

mod mask;
use mask::*;
use std::fmt::Display;

pub(crate) fn count_ones(mut value: u8) -> u8 {
    let mut result = 0;
    while value != 0 {
        result += value & 1;
        value >>= 1;
    }
    result
}

/// Deconstructs `nth` into a *index* and a *bit mask*
const fn deconstruct_nth(nth: usize) -> (usize, Mask) {
    (nth / 8, Mask::VALUES[nth % 8])
}

/// A vector of boolean values.
#[derive(Serialize, Deserialize, Clone)]
pub struct BoolVec {
    /// The data allocated for this `BoolVec`.
    vec: Vec<u8>,

    /// The bit mask that locates the last boolean that have been pushed
    /// onto the `BoolVec`.
    pub bit_mask: Mask,
}

impl BoolVec {
    
    /// Creates a new, empty `BoolVec`. The `BoolVec` will not allocate until elements
    /// are pushed onto it.
    #[inline(always)]
    pub const fn new() -> Self {
        Self {
            vec: Vec::new(),
            bit_mask: Mask::VALUES[7],
        }
    }
    
    /// Constructs a new, empty `BoolVec` with the specified capacity.
    /// The `BoolVec` will be able to hold exactly `capacity * 8` booleans without
    /// reallocating. If `capacity` is 0, the `BoolVec` will not allocate.
    #[inline(always)]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            vec: Vec::with_capacity(capacity),
            bit_mask: Mask::VALUES[7],
        }
    }

    /// Creates a random `BoolVec` containing `count` booleans.
    pub fn random(count: usize) -> Self {
        use rand::Rng;
        let (bytes, bit_mask) = if count == 0 {
            (Vec::new(), Mask::VALUES[7])
        }
        else {
            let mut rng = rand::thread_rng();
            // The bits that are not part of the vector should be set to 0.
            let bytes = (0..count/8)
                .into_iter()
                .map(|_| rng.gen::<u8>())
                .collect::<Vec<u8>>();
            (bytes, Mask::VALUES[(count - 1) % 8])
        };

        Self {
            vec: bytes,
            bit_mask,
        }
    }

    /// Creates a new `BoolVec` containing `count` booleans set to `value`.
    pub fn filled_with(count: usize, value: bool) -> Self {
        // The number of bytes we need to allocate.
        let value = if value { 255 } else { 0 };

        let (bytes, bit_mask) = if count == 0 {
            (Vec::new(), Mask::VALUES[7])
        }
        else {
            // The bits that are not part of the vector should be set to 0.
            let mut bytes = vec![value; count / 8];
            bytes.push(
                value << (7 - ((count - 1) % 8))
            );
            (bytes, Mask::VALUES[(count - 1) % 8])
        };

        Self {
            vec: bytes,
            bit_mask,
        }
    }

    /// Creates a `BitVec` from a vector of bytes.
    pub fn from_vec(vec: Vec<u8>) -> Self {
        Self {
            vec,
            bit_mask: Mask::VALUES[7],
        }
    }

    /// Concatenates two `BitVec`s into a new one.
    pub fn concatenate(&mut self, rhs: &mut BoolVec) -> Self {
        assert_eq!(self.bit_mask, rhs.bit_mask);
        Self {
            vec: self.vec.iter().chain(rhs.vec.iter()).cloned().collect(),
            bit_mask: Mask::VALUES[7],
        }
    }

    /// Get `BitVec` as Vec<u8>
    pub fn as_vec(&self) -> Vec<u8> {
        self.bytes().cloned().collect::<Vec<u8>>()
    }


    /// Returns the number of booleans that are stored inside of this `BoolVec`.
    #[inline]
    pub fn count(&self) -> usize {
        if self.vec.len() == 0 {
            0
        }
        else {
            self.vec.len() * 8 - 7 + self.bit_mask.offset()
        }
    }

    /// Is this `BoolVec` empty ?
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.count() == 0
    }

    /// Returns the capacity of this `BoolVec`, in bytes.
    #[inline(always)]
    pub fn capacity(&self) -> usize {
        self.vec.capacity()
    }

    /// Identical to `Vec::reserve`.
    /// 
    /// `additional_capacity` is in bytes.
    #[inline(always)]
    pub fn reserve(&mut self, additional_capacity: usize) {
        self.vec.reserve(additional_capacity);
    }

    /// Identical to `Vec::reserve_exact`.
    /// 
    /// `additional_capacity` is in bytes.
    #[inline(always)]
    pub fn reserve_exact(&mut self, additional_capacity: usize) {
        self.vec.reserve_exact(additional_capacity);
    }

    /// Identical to `Vec::shrink_to_fit`.
    #[inline(always)]
    pub fn shrink_to_fit(&mut self) {
        self.vec.shrink_to_fit();
    }

    /// Shortens the `BoolVec`, keeping the first `count` boolean values and
    /// dropping the rest.
    /// 
    /// If `count` is greater or equal to `self.count()`, this will have
    /// no effect.
    pub fn truncate(&mut self, count: usize) {
        if count >= self.count() {
            return;
        }
        
        let (kept_length, new_bit_mask) = if count == 0 {
            (0, Mask::VALUES[7])
        }
        else {
            (count / 8 + 1, Mask::VALUES[(count - 1) % 8])
        };

        self.vec.truncate(kept_length);
        self.bit_mask = new_bit_mask;
    }

    /// Gets a reference to the `nth` boolean stored inside of this `BoolVec`.
    /// 
    /// # Safety
    /// No bound checks are made.
    #[inline]
    pub unsafe fn get_unchecked_ref(&self, nth: usize) -> RefBool {
        let (index, bit_mask) = deconstruct_nth(nth);
        
        RefBool::new(
            self.vec.get_unchecked(index),
            bit_mask
        )
    }

    /// Gets the `nth` boolean stored inside of this `BoolVec`.
    /// 
    /// # Safety
    /// The value of `nth` must be less than `self.count()`.
    #[inline(always)]
    pub unsafe fn get_unchecked(&self, nth: usize) -> bool {
        self.get_unchecked_ref(nth).get()
    }

    /// Gets a reference to the `nth` boolean stored inside of this `BoolVec`
    /// or `None` if `nth` is out of bounds.
    #[inline]
    pub fn get_ref(&self, nth: usize) -> Option<RefBool> {
        if nth >= self.count() {
            None
        }
        else { unsafe {
            Some(self.get_unchecked_ref(nth))
        } }
    }

    /// Gets the the `nth` boolean stored inside of this `BoolVec` or `None` if
    /// `nth` is out of bounds.
    #[inline]
    pub fn get(&self, nth: usize) -> Option<bool> {
        if nth >= self.count() {
            None
        }
        else { unsafe {
            Some(self.get_unchecked(nth))
        } }
    }

    /// Gets a mutable reference to the `nth` boolean stored inside of
    /// this `BoolVec`.
    /// 
    /// # Safety
    /// The value of `nth` must be less than `self.count()`.
    #[inline]
    pub unsafe fn get_unchecked_mut(&mut self, nth: usize) -> RefBoolMut {
        let (index, bit_mask) = deconstruct_nth(nth);

        RefBoolMut::new(
            self.vec.get_unchecked_mut(index),
            bit_mask,
        )
    }

    /// Gets a mutable reference to the `nth` boolean stored inside of
    /// this `BoolVec` or `None` if `nth` is out of bounds.
    #[inline]
    pub fn get_mut(&mut self, nth: usize) -> Option<RefBoolMut> {
        if nth >= self.count() {
            None
        }
        else { unsafe {
            Some(self.get_unchecked_mut(nth))
        } }
    }

    /// Sets the value of the `nth` boolean stored inside of this `BoolVec`.
    /// 
    /// # Safety
    /// The value of `nth` must be less than `self.count()`
    #[inline(always)]
    pub unsafe fn set_unchecked(&mut self, nth: usize, value: bool) {
        self.get_unchecked_mut(nth).set(value);
    }

    /// Sets the value of the `nth` boolean stored inside of this `BoolVec`.
    /// 
    /// # Panics
    /// This function panics if `nth` is greater or equal to `self.count()`.
    #[inline]
    pub fn set(&mut self, nth: usize, value: bool) {
        if nth >= self.count() {
            panic!("nth was {} but the count was {}.", nth, self.count());
        }
        else { unsafe { 
            self.set_unchecked(nth, value)
        } }
    }

    /// Pushes a new boolean value into this `BoolVec`.
    /// 
    /// # Panics
    /// The function panics if the number of bytes allocated overflows `usize`.
    pub fn push(&mut self, value: bool) {
        self.bit_mask >>= 1;

        if self.bit_mask == Mask::VALUES[0] {
            self.vec.push(0)
        }

        unsafe {
            // Safety: `self.count() - 1 < self.count()`
            self.set_unchecked(self.count() - 1, value);
        }
    }

    /// Removes the last boolean value from this `BoolVec` and returns it.
    pub fn pop(&mut self) -> Option<bool> {
        if self.count() == 0 {
            None
        }
        else {
            let result = unsafe { self.get_unchecked(self.count() - 1) };

            self.bit_mask <<= 1;

            if self.bit_mask == Mask::VALUES[7] {
                self.vec.pop();
            }

            Some(result)
        }
    }

    /// Gets a reference to the last boolean stored in this `BoolVec` or `None`
    /// if the `BoolVec` is empty.
    pub fn last_ref(&self) -> Option<RefBool> {
        let count = self.count();
        
        if count == 0 {
            None
        }
        else { unsafe {
            Some(self.get_unchecked_ref(count - 1))
        } }
    }

    /// Gets a mutable reference to the last boolean stored in this `BoolVec`
    /// or `None` if the `BoolVec` is empty.
    pub fn last_mut(&mut self) -> Option<RefBoolMut> {
        let count = self.count();

        if count == 0 {
            None
        }
        else { unsafe { 
            Some(self.get_unchecked_mut(count - 1))
        } }
    }

    /// Gets the last boolean stored in this `BoolVec` or `None` if the vetor
    /// is empty.
    pub fn last(&self) -> Option<bool> {
        let count = self.count();

        if count == 0 {
            None
        }
        else { unsafe {
            Some(self.get_unchecked(count - 1))
        }}
    }

    /// Clears this `BoolVec`.1
    pub fn clear(&mut self) {
        self.vec.clear();
        self.bit_mask = Mask::VALUES[7];
    }

    /// Creates an unsafe iterator over the values of this `BoolVec`.
    unsafe fn unsafe_iter(&self) -> UnsafeIter {
        UnsafeIter {
            start: UnsafeBoolRef::new(
                // This cast if valid because this pointer will be used inside
                // an `Iter` that will never write.
                NonNull::new(self.vec.as_ptr() as *mut u8).unwrap(),
                Mask::VALUES[0],
            ),

            end: UnsafeBoolRef::new(
                // Safty : The data id valid between `self.vec.as_ptr` and
                // `self.vec.as_ptr + self.vec.len` (not included).
                NonNull::new(self.vec.as_ptr().add({
                    if self.count() == 0 {
                        0
                    }
                    else {
                        self.vec.len() - 1
                    }
                }) as *mut u8).unwrap(),
                self.bit_mask,
            ).next_bit()
        }
    }

    /// Creates a new iterator that iterates over the values of this `BoolVec`.
    pub fn iter(&self) -> Iter {
        Iter {
            inner: unsafe { self.unsafe_iter() },
            _marker: PhantomData,
        }
    }

    /// Creates a new iterator that iterates over mutable references of the
    /// values of this `BoolVec`.
    pub fn iter_mut(&mut self) -> IterMut {
        IterMut {
            inner: unsafe { self.unsafe_iter() },
            _marker: PhantomData,
        }
    }

    /// Returns an iterator over the bytes of this `BoolVec`.
    pub fn bytes(&self) -> impl Iterator<Item=&u8> {
        self.vec.iter()
    }

    /// Returns an iterator over the bytes of this `BoolVec`.
    pub fn bytes_mut(&mut self) -> impl Iterator<Item=&mut u8> {
        self.vec.iter_mut()
    }

    /// Returns the number of bits that are set to `1` within this vector.
    pub fn count_ones(&self) -> usize {
        self.bytes()
            .map(|&b| count_ones(b) as usize)
            .sum::<usize>()
    }
}

impl Display for BoolVec {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", format!("{:02X?}", self.as_vec()))
    }
}


impl<'s> BitAnd<&'s BoolVec> for &'s BoolVec {
    type Output = BoolVec;

    fn bitand(self: &'s BoolVec, other: &'s BoolVec) -> BoolVec {
        let mut result = BoolVec::with_capacity(
            Ord::min(self.vec.len(), other.vec.len())
        );

        // Safety : We don't care if the bytes are not initialized.
        for (&a, &b) in self.bytes().zip(other.bytes()) {
            result.vec.push(a & b);
        }

        result.bit_mask = Ord::min(self.bit_mask, other.bit_mask);

        result
    }
}

impl<'s> BitAndAssign<&'s BoolVec> for BoolVec {
    fn bitand_assign(&mut self, other: &'s BoolVec) {
        for (byte, &o_byte) in self.bytes_mut().zip(other.bytes()) {
            *byte &= o_byte;
        }
    }
}

impl<'s> BitOr<&'s BoolVec> for &'s BoolVec {
    type Output = BoolVec;

    fn bitor(self: &'s BoolVec, other: &'s BoolVec) -> BoolVec {
        let mut result = BoolVec::with_capacity(
            Ord::min(self.vec.len(), other.vec.len())
        );

        for (&a, &b) in self.bytes().zip(other.bytes()) {
            result.vec.push(a | b);
        }

        result.bit_mask = Ord::max(self.bit_mask, other.bit_mask);

        result
    }
}

impl<'s> BitOrAssign<&'s BoolVec> for BoolVec {
    fn bitor_assign(&mut self, other: &'s BoolVec) {
        for (byte, &o_byte) in self.bytes_mut().zip(other.bytes()) {
            *byte |= o_byte;
        }
    }
}

impl<'s> BitXor<&'s BoolVec> for &'s BoolVec {
    type Output = BoolVec;

    fn bitxor(self: &'s BoolVec, other: &'s BoolVec) -> BoolVec {
        let mut result = BoolVec::with_capacity(
            Ord::min(self.vec.len(), other.vec.len())
        );

        for (&a, &b) in self.bytes().zip(other.bytes()) {
            result.vec.push(a ^ b);
        }

        result.bit_mask = Ord::max(self.bit_mask, other.bit_mask);

        result
    }
}

impl<'s> BitXorAssign<&'s BoolVec> for BoolVec {
    fn bitxor_assign(&mut self, other: &'s BoolVec) {
        for (byte, &o_byte) in self.bytes_mut().zip(other.bytes()) {
            *byte ^= o_byte;
        }
    }
}

impl FromIterator<bool> for BoolVec {
    fn from_iter<S: IntoIterator<Item=bool>>(iter: S) -> Self {
        let iter = iter.into_iter();
        let mut result = Self::with_capacity(iter.size_hint().0);

        for bit in iter {
            result.push(bit);
        }

        result
    }
}

impl FromIterator<u8> for BoolVec {
    fn from_iter<S: IntoIterator<Item=u8>>(iter: S) -> Self {
        let iter = iter.into_iter();
        let mut result = Vec::with_capacity(iter.size_hint().0);

        for byte in iter {
            result.push(byte)
        }

        Self::from_vec(result)
    }
}

/// An unsafe interface for iterators.
#[derive(Clone)]
struct UnsafeIter {
    start: UnsafeBoolRef,
    end: UnsafeBoolRef,
}

impl Iterator for UnsafeIter {
    type Item = UnsafeBoolRef;

    fn next(&mut self) -> Option<UnsafeBoolRef> {
        if self.start >= self.end {
            None
        }
        else {
            let temp = self.start.clone();
            // Safety: The `UnsafeIter` must have been created with valid values.
            unsafe { self.start = self.start.next_bit() }
            Some(temp)
        }
    }

    #[inline(always)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len();
        (len, Some(len))
    }
}

impl ExactSizeIterator for UnsafeIter {
    fn len(&self) -> usize {
        let start = self.start.byte.as_ptr() as usize;
        let end = self.end.byte.as_ptr() as usize;
        let start_bit = self.start.bit_mask.offset();
        let end_bit = self.end.bit_mask.offset();

        (end - start) * 8 + (end_bit - start_bit)
    }
}

impl DoubleEndedIterator for UnsafeIter {
    fn next_back(&mut self) -> Option<UnsafeBoolRef> {
        if self.start >= self.end {
            None
        }
        else {
            unsafe { self.end = self.end.prev_bit() }
            Some(self.end.clone())
        }
    }
}

impl FusedIterator for UnsafeIter { }

#[derive(Clone)]
pub struct Iter<'s> {
    inner: UnsafeIter,
    _marker: PhantomData<&'s [u8]>,
}

impl<'s> Iterator for Iter<'s> {
    type Item = bool;

    #[inline]
    fn next(&mut self) -> Option<bool> {
        match self.inner.next() {
            // Safety: The inner iterator has to be valid.
            Some(val) => unsafe { Some(val.get()) },
            None => None,
        }
    }

    #[inline(always)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'s> ExactSizeIterator for Iter<'s> {
    #[inline(always)]
    fn len(&self) -> usize { self.inner.len() }
}

impl<'s> DoubleEndedIterator for Iter<'s> {
    #[inline]
    fn next_back(&mut self) -> Option<bool> {
        match self.inner.next_back() {
            // Safety: The inner iterator has to be valid.
            Some(val) => unsafe { Some(val.get()) },
            None => None,
        }
    }
}

impl<'s> FusedIterator for Iter<'s> { }

#[derive(Clone)]
pub struct IterMut<'s> {
    inner: UnsafeIter,
    _marker: PhantomData<&'s mut [u8]>,
}

impl<'s> Iterator for IterMut<'s> {
    type Item = RefBoolMut<'s>;

    #[inline]
    fn next(&mut self) -> Option<RefBoolMut<'s>> {
        match self.inner.next() {
            // Safety: The inner iterator has to be valid.
            Some(val) => Some(RefBoolMut::from_inner(val)),
            None => None,
        }
    }

    #[inline(always)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'s> ExactSizeIterator for IterMut<'s> {
    #[inline(always)]
    fn len(&self) -> usize { self.inner.len() }
}

impl<'s> DoubleEndedIterator for IterMut<'s> {
    #[inline]
    fn next_back(&mut self) -> Option<RefBoolMut<'s>> {
        match self.inner.next_back() {
            // Safety: The inner iterator has to be valid.
            Some(val) => Some(RefBoolMut::from_inner(val)),
            None => None,
        }
    }
}

impl<'s> FusedIterator for IterMut<'s> { }

#[cfg(test)]
mod vec_tests {
    use super::*;

    #[test]
    fn create_vector() {
        let vec = BoolVec::new();
        assert_eq!(vec.capacity(), 0);
        assert_eq!(vec.count(), 0);
        assert!(vec.is_empty());
        
        let vec = BoolVec::with_capacity(0);
        assert_eq!(vec.capacity(), 0);
        assert_eq!(vec.count(), 0);
        assert!(vec.is_empty());
        
        let vec = BoolVec::with_capacity(10);
        assert_eq!(vec.capacity(), 10);
        assert_eq!(vec.count(), 0);
        assert!(vec.is_empty());
        
        let vec = BoolVec::filled_with(4, true);
        assert_eq!(vec.capacity(), 1);
        assert_eq!(vec.count(), 4);
        assert_eq!(vec.vec.len(), 1);
        assert_eq!(vec.vec[0], 0b1111_0000);
        assert!(!vec.is_empty());
        
        let vec = BoolVec::filled_with(9, false);
        assert_eq!(vec.capacity(), 2);
        assert_eq!(vec.count(), 9);
        assert_eq!(vec.vec.len(), 2);
        assert!(!vec.is_empty());
        assert_eq!(vec.vec[0], 0);
        assert_eq!(vec.vec[1], 0);
    }

    #[test]
    fn truncate() {
        let mut vec = BoolVec::new();

        vec.push(true);
        vec.push(false);
        vec.push(false);
        vec.push(true);

        assert_eq!(vec.count(), 4);
        
        vec.truncate(2);

        assert_eq!(vec.count(), 2);

        assert_eq!(vec.get(0), Some(true));
        assert_eq!(vec.get(1), Some(false));
        assert_eq!(vec.get(2), None);
        assert_eq!(vec.get(3), None);
    }

    #[test]
    fn pop() {
        let mut vec = BoolVec::new();

        vec.push(true);
        vec.push(false);
        vec.push(true);
        vec.push(true);
        vec.push(false);
        vec.push(false);

        assert_eq!(vec.pop(), Some(false));
        assert_eq!(vec.pop(), Some(false));
        assert_eq!(vec.pop(), Some(true));
        assert_eq!(vec.pop(), Some(true));
        assert_eq!(vec.pop(), Some(false));
        assert_eq!(vec.pop(), Some(true));
        assert_eq!(vec.pop(), None);
        assert_eq!(vec.pop(), None);

        assert_eq!(vec.last(), None);
    }

    #[test]
    fn pushes() {
        let mut vec = BoolVec::new();

        assert_eq!(vec.vec.len(), 0);
        assert_eq!(vec.count(), 0);

        vec.push(false);
        vec.push(true);
        vec.push(true);
        vec.push(false);

        println!("{:#b}", vec.vec[0]);

        assert_eq!(vec.count(), 4);
        assert_eq!(vec.vec.len(), 1);

        assert_eq!(vec.get(0), Some(false));
        assert_eq!(vec.get(1), Some(true));
        assert_eq!(vec.get(2), Some(true));
        assert_eq!(vec.get(3), Some(false));
        assert_eq!(vec.get(4), None);

        assert_eq!(vec.last(), Some(false));

        vec.set(0, true);
        vec.set(1, false);
        vec.set(2, false);
        vec.set(3, true);

        assert_eq!(vec.get(0), Some(true));
        assert_eq!(vec.get(1), Some(false));
        assert_eq!(vec.get(2), Some(false));
        assert_eq!(vec.get(3), Some(true));
        assert_eq!(vec.get(4), None);

        assert_eq!(vec.last(), Some(true));
    }


    #[test]
    fn iterators() {
        let mut vec = BoolVec::new();

        vec.push(true);
        vec.push(false);
        vec.push(false);
        vec.push(false);
        vec.push(true);
        vec.push(true);
        vec.push(false);
        vec.push(true);
        vec.push(false);
        vec.push(false);
        vec.push(true);
        vec.push(false);

        let mut iter = vec.iter();

        assert_eq!(iter.len(), 12);

        assert_eq!(iter.next(), Some(true));
        assert_eq!(iter.next_back(), Some(false));
        assert_eq!(iter.len(), 10);
        assert_eq!(iter.next(), Some(false));
        assert_eq!(iter.next_back(), Some(true));
        assert_eq!(iter.next(), Some(false));
        assert_eq!(iter.next_back(), Some(false));
        assert_eq!(iter.next(), Some(false));
        assert_eq!(iter.next_back(), Some(false));
        assert_eq!(iter.next(), Some(true));
        assert_eq!(iter.next_back(), Some(true));
        assert_eq!(iter.next(), Some(true));
        assert_eq!(iter.next_back(), Some(false));
        assert_eq!(iter.len(), 0);
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next_back(), None);
        assert_eq!(iter.next_back(), None);

        let mut iter = vec.iter_mut();

        assert_eq!(iter.next().unwrap().get(), true);
        assert_eq!(iter.next_back().unwrap().get(), false);
        assert_eq!(iter.len(), 10);
        assert_eq!(iter.next().unwrap().get(), false);
        assert_eq!(iter.next_back().unwrap().get(), true);
        assert_eq!(iter.next().unwrap().get(), false);
        assert_eq!(iter.next_back().unwrap().get(), false);
        assert_eq!(iter.next().unwrap().get(), false);
        assert_eq!(iter.next_back().unwrap().get(),false);
        assert_eq!(iter.next().unwrap().get(), true);
        assert_eq!(iter.next_back().unwrap().get(), true);
        assert_eq!(iter.next().unwrap().get(), true);
        assert_eq!(iter.next_back().unwrap().get(), false);
        assert_eq!(iter.len(), 0);
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next_back(), None);
        assert_eq!(iter.next_back(), None);
    }

    #[test]
    fn operations() {
        let mut vec_a = BoolVec::new();

        vec_a.push(true);
        vec_a.push(true);
        vec_a.push(true);
        vec_a.push(true);
        vec_a.push(false);
        vec_a.push(false);
        vec_a.push(false);
        vec_a.push(false);
        vec_a.push(true);
        vec_a.push(false);
        vec_a.push(false);
        vec_a.push(true);

        let mut vec_b = BoolVec::new();

        vec_b.push(true);
        vec_b.push(true);
        vec_b.push(false);
        vec_b.push(false);
        vec_b.push(true);
        vec_b.push(true);
        vec_b.push(false);
        vec_b.push(false);
        vec_b.push(true);
        vec_b.push(true);
        vec_b.push(true);
        vec_b.push(true);

        let and = &vec_a & &vec_b;
        let or = &vec_a | &vec_b;
        let xor = &vec_a ^ &vec_b;

        let and_i = and.iter();
        let or_i = or.iter();
        let xor_i = xor.iter();

        let mut and_a = vec_a.clone();
        let mut or_a = vec_a.clone();
        let mut xor_a = vec_a.clone();

        and_a &= &vec_b;
        or_a  |= &vec_b;
        xor_a ^= &vec_b;

        let and_a = and_a.iter();
        let or_a = or_a.iter();
        let xor_a = xor_a.iter();

        for (and, or, xor)
        in [ (and_i, or_i, xor_i), (and_a, or_a, xor_a) ].iter_mut () {
            assert_eq!(and.next(), Some(true));
            assert_eq!(and.next(), Some(true));
            assert_eq!(and.next(), Some(false));
            assert_eq!(and.next(), Some(false));
            assert_eq!(and.next(), Some(false));
            assert_eq!(and.next(), Some(false));
            assert_eq!(and.next(), Some(false));
            assert_eq!(and.next(), Some(false));
            assert_eq!(and.next(), Some(true));
            assert_eq!(and.next(), Some(false));
            assert_eq!(and.next(), Some(false));
            assert_eq!(and.next(), Some(true));
    
            assert_eq!(or.next(), Some(true));
            assert_eq!(or.next(), Some(true));
            assert_eq!(or.next(), Some(true));
            assert_eq!(or.next(), Some(true));
            assert_eq!(or.next(), Some(true));
            assert_eq!(or.next(), Some(true));
            assert_eq!(or.next(), Some(false));
            assert_eq!(or.next(), Some(false));
            assert_eq!(or.next(), Some(true));
            assert_eq!(or.next(), Some(true));
            assert_eq!(or.next(), Some(true));
            assert_eq!(or.next(), Some(true));
    
            assert_eq!(xor.next(), Some(false));
            assert_eq!(xor.next(), Some(false));
            assert_eq!(xor.next(), Some(true));
            assert_eq!(xor.next(), Some(true));
            assert_eq!(xor.next(), Some(true));
            assert_eq!(xor.next(), Some(true));
            assert_eq!(xor.next(), Some(false));
            assert_eq!(xor.next(), Some(false));
            assert_eq!(xor.next(), Some(false));
            assert_eq!(xor.next(), Some(true));
            assert_eq!(xor.next(), Some(true));
            assert_eq!(xor.next(), Some(false));
        }
    }

    #[test]
    fn count_ones() {
        assert_eq!(super::count_ones(0b1111_0000), 4);
        assert_eq!(super::count_ones(0b0001_0000), 1);
        assert_eq!(super::count_ones(0b0001_1111), 5);
        assert_eq!(super::count_ones(0b1010_1010), 4);

        assert_eq!(BoolVec::new().count_ones(), 0);
        assert_eq!(BoolVec::with_capacity(10).count_ones(), 0);
        assert_eq!(BoolVec::filled_with(100, false).count_ones(), 0);
        assert_eq!(BoolVec::filled_with(100, true).count_ones(), 100);

        let mut vec = BoolVec::new();
        vec.push(true);
        vec.push(true);
        vec.push(false);
        vec.push(true);
        vec.push(true);
        vec.push(false);
        vec.push(false);
        vec.push(true);
        vec.push(false);
        vec.push(false);
        vec.push(false);
        vec.push(true);
        vec.push(true);
        vec.push(true);
        vec.push(true);
        vec.push(false);

        assert_eq!(vec.count_ones(), 9);

        let vec = [true, true, false].iter().cloned().cycle().take(60).collect::<BoolVec>();
        assert_eq!(vec.count_ones(), 40);
    }

    #[test]
    fn from_iter() {
        let bits = [true, true, false].iter().cloned().cycle().take(100);

        let vec = bits.collect::<BoolVec>();

        assert_eq!(vec.count(), 100);

        for i in 0..100 {
            assert_eq!(vec.get(i).unwrap(), match i % 3 {
                0 => true,
                1 => true,
                2 => false,
                _ => unreachable!(),
            });
        }

        let bytes = std::iter::repeat(0b1010_1010).take(10);

        let vec = bytes.collect::<BoolVec>();

        for i in 0..80 {
            assert_eq!(vec.get(i).unwrap(), if i % 2 == 0 { true } else { false });
        }
    }
}

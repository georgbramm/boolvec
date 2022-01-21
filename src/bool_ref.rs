use std::fmt;
use std::ptr::NonNull;
use std::marker::PhantomData;

use std::cmp::{
    Ordering,
    Ord, PartialOrd,
};

use crate::mask::Mask;

/// An unsafe interface that holds a reference to a boolean that may be
/// in the middle of byte.
#[derive(Clone, Copy)]
pub(crate) struct UnsafeBoolRef {
    pub byte: NonNull<u8>,
    pub bit_mask: Mask,
}

impl fmt::Debug for UnsafeBoolRef {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        unsafe {
            fmt::Debug::fmt(&self.get(), f)
        }
    }
}

impl fmt::Display for UnsafeBoolRef {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        unsafe {
            fmt::Debug::fmt(&self.get(), f)
        }
    }
}

impl UnsafeBoolRef {
    /// Creates a new `MutBool`.
    #[inline]
    pub fn new(byte: NonNull<u8>, bit_mask: Mask) -> Self {
        Self {
            byte,
            bit_mask,
        }
    }

    /// Gets the value of the referenced boolean.
    ///
    /// # Safety
    /// The lifetime of the referenced byte must be valid.
    #[inline(always)]
    pub unsafe fn get(&self) -> bool {
        self.bit_mask.check(
            *self.byte.as_ref()
        )
    }

    /// Sets the value of the referenced boolean.
    ///
    /// # Safety
    /// The lifetime of the referenced byte must be valid.
    pub unsafe fn set(&mut self, value: bool) {
        self.bit_mask.set(self.byte.as_mut(), value);
    }

    /// Returns a reference that points to the next bit.
    /// 
    /// # Safety
    /// The next bit must be a valid value.
    pub unsafe fn next_bit(mut self) -> Self {
        self.bit_mask >>= 1;

        if self.bit_mask == Mask::VALUES[0] {
            self.byte = NonNull::new(self.byte.as_ptr().add(1)).unwrap();
        }

        self
    }

    /// Returns a reference that points to the next bit.
    /// 
    /// # Safety
    /// The previous bit must be a valid value.
    pub unsafe fn prev_bit(mut self) -> Self {
        self.bit_mask <<= 1;

        if self.bit_mask == Mask::VALUES[7] {
            self.byte = NonNull::new(self.byte.as_ptr().sub(1)).unwrap();
        }

        self
    }
}

impl PartialOrd for UnsafeBoolRef {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for UnsafeBoolRef {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.byte.cmp(&other.byte) {
            Ordering::Greater => Ordering::Greater,
            Ordering::Less => Ordering::Less,
            Ordering::Equal => self.bit_mask.cmp(&other.bit_mask),
        }
    }
}

impl PartialEq for UnsafeBoolRef {
    fn eq(&self, other: &Self) -> bool {
        unsafe { self.get() == other.get() }
    }
}

impl Eq for UnsafeBoolRef { }

/// A mutable reference to a `bool` value that may be in the middle of a byte.
#[derive(Clone, Copy, PartialOrd, Ord, PartialEq, Eq)]
pub struct RefBoolMut<'s> {
    inner: UnsafeBoolRef,
    _marker: PhantomData<&'s mut u8>,
}

impl<'s> fmt::Debug for RefBoolMut<'s> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&self.get(), f)
    }
}

impl<'s> fmt::Display for RefBoolMut<'s> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&self.get(), f)
    }
}

impl<'s> RefBoolMut<'s> {
    pub(crate) fn from_inner(inner: UnsafeBoolRef) -> Self {
        Self {
            inner,
            _marker: PhantomData,
        }
    }

    /// Creates a new `MutBool`.
    pub fn new(byte: &'s mut u8, bit_mask: Mask) -> Self {
        Self::from_inner(UnsafeBoolRef::new(NonNull::from(byte), bit_mask))
    }

    /// Gets the value of the referenced boolean.
    #[inline(always)]
    pub fn get(&self) -> bool {
        // Safety: The lifetime is checked by the compiler thanks to the
        // phantom data.
        unsafe { self.inner.get() }
    }

    /// Sets the value of the referenced boolean.
    #[inline(always)]
    pub fn set(&mut self, value: bool) {
        // Safety: The lifetime is checked by the compiler thanks to the
        // phantom data.
        unsafe { self.inner.set(value); }
    }

    /// Returns a reference that points to the next bit without being constrained
    /// by the referenced byte.
    ///
    /// # Safety
    /// The previous bit must be a valid value.
    #[inline]
    pub unsafe fn unconstrained_next_bit(mut self) -> Self {
        self.inner = self.inner.next_bit();
        self
    }

    /// Returns a reference that points to the previous bit without being constrained
    /// by the referenced byte.
    ///
    /// # Safety
    /// The previous bit must be a valid value.
    #[inline]
    pub unsafe fn unconstrained_prev_bit(mut self) -> Self {
        self.inner = self.inner.prev_bit();
        self
    }

    /// Returns a reference that points to the next bit within the referenced byte.
    ///
    /// # Panics
    /// This function panics if the previous bit is not part of the referenced byte.
    #[inline]
    pub fn next_bit(mut self) -> Self {
        if self.inner.bit_mask == Mask::VALUES[7] {
            panic!("The next bit was not part of the referenced byte.");
        }

        self.inner = unsafe { self.inner.next_bit() };
        self
    }

    /// Returns a reference that points to the previous bit within the referenced byte.
    /// 
    /// # Panics
    /// This function panics if the previous bit is not part of the referenced byte.
    #[inline]
    pub fn prev_bit(mut self) -> Self {
        if self.inner.bit_mask == Mask::VALUES[0] {
            panic!("The previous bit was not part of the referenced byte.");
        }

        self.inner = unsafe { self.inner.prev_bit() };
        self
    }
}

/// A reference to a `bool` value that may be in the middle of a byte.
#[derive(Clone, Copy, PartialOrd, Ord, PartialEq, Eq)]
pub struct RefBool<'s> {
    inner: UnsafeBoolRef,
    _marker: PhantomData<&'s u8>,
}

impl<'s> fmt::Debug for RefBool<'s> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&self.get(), f)
    }
}

impl<'s> fmt::Display for RefBool<'s> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&self.get(), f)
    }
}

impl<'s> RefBool<'s> {
    /// Creates a new `MutBool`.
    pub fn new(byte: &'s u8, bit_mask: Mask) -> Self {
        Self {
            inner: UnsafeBoolRef::new(NonNull::from(byte), bit_mask),
            _marker: PhantomData,
        }
    }

    /// Gets the value of the referenced boolean.
    pub fn get(&self) -> bool {
        // Safety: The lifetime is checked by the compiler thanks to the
        // phantom data.
        unsafe { self.inner.get() }
    }

    /// Returns a reference that points to the next bit without being constrained
    /// by the referenced byte.
    ///
    /// # Safety
    /// The previous bit must be a valid value.
    #[inline]
    pub unsafe fn unconstrained_next_bit(mut self) -> Self {
        self.inner = self.inner.next_bit();
        self
    }

    /// Returns a reference that points to the previous bit without being constrained
    /// by the referenced byte.
    ///
    /// # Safety
    /// The previous bit must be a valid value.
    #[inline]
    pub unsafe fn unconstrained_prev_bit(mut self) -> Self {
        self.inner = self.inner.prev_bit();
        self
    }

    /// Returns a reference that points to the next bit within the referenced byte.
    ///
    /// # Panics
    /// This function panics if the previous bit is not part of the referenced byte.
    #[inline]
    pub fn next_bit(mut self) -> Self {
        if self.inner.bit_mask == Mask::VALUES[7] {
            panic!("The next bit was not part of the referenced byte.");
        }

        self.inner = unsafe { self.inner.next_bit() };
        self
    }

    /// Returns a reference that points to the previous bit within the referenced byte.
    /// 
    /// # Panics
    /// This function panics if the previous bit is not part of the referenced byte.
    #[inline]
    pub fn prev_bit(mut self) -> Self {
        if self.inner.bit_mask == Mask::VALUES[0] {
            panic!("The previous bit was not part of the referenced byte.");
        }

        self.inner = unsafe { self.inner.prev_bit() };
        self
    }
}

#[cfg(test)]
mod ref_tests {
    use super::*;

    #[test]
    fn gets_sets() {
        let mut byte = 0b1100_1010;
        
        assert_eq!(RefBool::new(&byte, Mask::VALUES[0]).get(), true);
        assert_eq!(RefBool::new(&byte, Mask::VALUES[1]).get(), true);
        assert_eq!(RefBool::new(&byte, Mask::VALUES[2]).get(), false);
        assert_eq!(RefBool::new(&byte, Mask::VALUES[3]).get(), false);
        assert_eq!(RefBool::new(&byte, Mask::VALUES[4]).get(), true);
        assert_eq!(RefBool::new(&byte, Mask::VALUES[5]).get(), false);
        assert_eq!(RefBool::new(&byte, Mask::VALUES[6]).get(), true);
        assert_eq!(RefBool::new(&byte, Mask::VALUES[7]).get(), false);

        assert_eq!(RefBoolMut::new(&mut byte, Mask::VALUES[0]).get(), true);
        assert_eq!(RefBoolMut::new(&mut byte, Mask::VALUES[1]).get(), true);
        assert_eq!(RefBoolMut::new(&mut byte, Mask::VALUES[2]).get(), false);
        assert_eq!(RefBoolMut::new(&mut byte, Mask::VALUES[3]).get(), false);
        assert_eq!(RefBoolMut::new(&mut byte, Mask::VALUES[4]).get(), true);
        assert_eq!(RefBoolMut::new(&mut byte, Mask::VALUES[5]).get(), false);
        assert_eq!(RefBoolMut::new(&mut byte, Mask::VALUES[6]).get(), true);
        assert_eq!(RefBoolMut::new(&mut byte, Mask::VALUES[7]).get(), false);

        RefBoolMut::new(&mut byte, Mask::VALUES[0]).set(false);
        RefBoolMut::new(&mut byte, Mask::VALUES[1]).set(false);
        RefBoolMut::new(&mut byte, Mask::VALUES[2]).set(true);
        RefBoolMut::new(&mut byte, Mask::VALUES[3]).set(true);
        RefBoolMut::new(&mut byte, Mask::VALUES[4]).set(false);
        RefBoolMut::new(&mut byte, Mask::VALUES[5]).set(true);
        RefBoolMut::new(&mut byte, Mask::VALUES[6]).set(false);
        RefBoolMut::new(&mut byte, Mask::VALUES[7]).set(true);

        assert_eq!(RefBoolMut::new(&mut byte, Mask::VALUES[0]).get(), false);
        assert_eq!(RefBoolMut::new(&mut byte, Mask::VALUES[1]).get(), false);
        assert_eq!(RefBoolMut::new(&mut byte, Mask::VALUES[2]).get(), true);
        assert_eq!(RefBoolMut::new(&mut byte, Mask::VALUES[3]).get(), true);
        assert_eq!(RefBoolMut::new(&mut byte, Mask::VALUES[4]).get(), false);
        assert_eq!(RefBoolMut::new(&mut byte, Mask::VALUES[5]).get(), true);
        assert_eq!(RefBoolMut::new(&mut byte, Mask::VALUES[6]).get(), false);
        assert_eq!(RefBoolMut::new(&mut byte, Mask::VALUES[7]).get(), true);
    }

    #[test]
    fn offsets() {
        let slice = &mut [0b1100_0011, 0b1101_1010];
        let mut b = RefBoolMut::new(unsafe { &mut *slice.as_mut_ptr() }, Mask::VALUES[0]);

        unsafe {
            assert_eq!(b.get(), true);
            b = b.unconstrained_next_bit();
            assert_eq!(b.get(), true);
            b = b.unconstrained_next_bit();
            assert_eq!(b.get(), false);
            b = b.unconstrained_next_bit();
            assert_eq!(b.get(), false);
            b = b.unconstrained_next_bit();
            assert_eq!(b.get(), false);
            b = b.unconstrained_next_bit();
            assert_eq!(b.get(), false);
            b = b.unconstrained_next_bit();
            assert_eq!(b.get(), true);
            b = b.unconstrained_next_bit();
            assert_eq!(b.get(), true);
            b = b.unconstrained_next_bit();
            assert_eq!(b.get(), true);
            b = b.unconstrained_next_bit();
            assert_eq!(b.get(), true);
            b = b.unconstrained_next_bit();
            assert_eq!(b.get(), false);
            b = b.unconstrained_next_bit();
            assert_eq!(b.get(), true);
            b = b.unconstrained_next_bit();
            assert_eq!(b.get(), true);
            b = b.unconstrained_next_bit();
            assert_eq!(b.get(), false);
            b = b.unconstrained_next_bit();
            assert_eq!(b.get(), true);
            b = b.unconstrained_next_bit();
            assert_eq!(b.get(), false);

            b = b.unconstrained_prev_bit();
            assert_eq!(b.get(), true);
            b = b.unconstrained_prev_bit();
            assert_eq!(b.get(), false);
            b = b.unconstrained_prev_bit();
            assert_eq!(b.get(), true);
            b = b.unconstrained_prev_bit();
            assert_eq!(b.get(), true);
            b = b.unconstrained_prev_bit();
            assert_eq!(b.get(), false);
            b = b.unconstrained_prev_bit();
            assert_eq!(b.get(), true);
            b = b.unconstrained_prev_bit();
            assert_eq!(b.get(), true);
            b = b.unconstrained_prev_bit();
            assert_eq!(b.get(), true);
            b = b.unconstrained_prev_bit();
            assert_eq!(b.get(), true);
            b = b.unconstrained_prev_bit();
            assert_eq!(b.get(), false);
            b = b.unconstrained_prev_bit();
            assert_eq!(b.get(), false);
            b = b.unconstrained_prev_bit();
            assert_eq!(b.get(), false);
            b = b.unconstrained_prev_bit();
            assert_eq!(b.get(), false);
            b = b.unconstrained_prev_bit();
            assert_eq!(b.get(), true);
            b = b.unconstrained_prev_bit();
            assert_eq!(b.get(), true);
        }
    }
}

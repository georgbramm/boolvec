use std::fmt;
use std::ops::{
    Shl, ShlAssign,
    Shr, ShrAssign,
    Not,
    BitAnd, BitAndAssign,
    BitOr, BitOrAssign,
    BitXor, BitXorAssign,
};
use std::cmp::{
    PartialOrd,
    Ord,
    Ordering,
};

/// A bitmask.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct Mask {
    value: u8,
}

impl fmt::Display for Mask {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut value = self.value;

        let mut result = vec![0u8; 8];

        for i in 0..8 {
            result[7 - i] = '0' as u8 + (value & 1);
            value >>= 1;
        }

        f.pad(std::str::from_utf8(result.as_slice()).unwrap())
    }
}

impl fmt::Debug for Mask {
    #[inline(always)]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl Mask {
    /// The number of bits that can be stored in one single bitmask.
    pub const BITS: u32 = std::mem::size_of::<u8>() as u32 * 8;

    pub const VALUES: [Mask; 8] = unsafe { [
        Mask::new_unchecked(0b1000_0000),
        Mask::new_unchecked(0b0100_0000),
        Mask::new_unchecked(0b0010_0000),
        Mask::new_unchecked(0b0001_0000),
        Mask::new_unchecked(0b0000_1000),
        Mask::new_unchecked(0b0000_0100),
        Mask::new_unchecked(0b0000_0010),
        Mask::new_unchecked(0b0000_0001),
    ] };

    /// Creates a new `Mask`.
    pub fn new(value: u8) -> Mask {
        assert_eq!(
            crate::count_ones(value),
            1,
            "Bitmasks have to be a power of two.",
        );

        unsafe {
            Mask::new_unchecked(value)
        }
    }

    /// Creates a new `Mask`.
    /// 
    /// # Safety
    /// `value` have to be a power of two.
    #[inline(always)]
    pub const unsafe fn new_unchecked(value: u8) -> Mask {
        Mask {
            value,
        }
    }

    /// The offset the first bit of this mask, from right to left.
    #[inline]
    pub fn offset(&self) -> usize {
        match self.value {
            0b1000_0000 => 0,
            0b0100_0000 => 1,
            0b0010_0000 => 2,
            0b0001_0000 => 3,
            0b0000_1000 => 4,
            0b0000_0100 => 5,
            0b0000_0010 => 6,
            0b0000_0001 => 7,
            _ => unreachable!("Invalid bitmask."),
        }
    }

    /// Checks if the bit highlighted by this `Mask` is `1`.
    #[inline(always)]
    pub fn check(&self, byte: u8) -> bool {
        self.value & byte == self.value
    }

    /// Sets the highlighted bit to `value`.
    #[inline]
    pub fn set(&self, byte: &mut u8, value: bool) {
        *byte = if value {
            *byte | *self
        }
        else {
            *byte & !*self
        }
    }
}

impl Into<u8> for Mask {
    fn into(self) -> u8 {
        self.value
    }
}

impl From<u8> for Mask {
    fn from(value: u8) -> Mask {
        Self::new(value)
    }
}

impl Shr<u32> for Mask {
    type Output = Mask;

    fn shr(self, mut other: u32) -> Mask {
        other %= Mask::BITS;
        Mask {
            value: self.value.overflowing_shr(other).0 | self.value.overflowing_shl(Mask::BITS - other).0,
        }
    }
}

impl ShrAssign<u32> for Mask {
    #[inline(always)]
    fn shr_assign(&mut self, other: u32) {
        *self = *self >> other;
    }
}

impl Shl<u32> for Mask {
    type Output = Mask;

    fn shl(self, mut other: u32) -> Mask {
        other %= Mask::BITS;
        Mask {
            value: self.value.overflowing_shl(other).0 | self.value.overflowing_shr(Mask::BITS - other).0,
        }
    }
}

impl ShlAssign<u32> for Mask {
    #[inline(always)]
    fn shl_assign(&mut self, other: u32) {
        *self = *self << other;
    }
}

impl Not for Mask {
    type Output = Mask;

    #[inline(always)]
    fn not(self) -> Mask {
        Mask {
            value: !self.value
        }
    }
}

impl BitAnd<u8> for Mask {
    type Output = u8;

    #[inline(always)]
    fn bitand(self, other: u8) -> u8 {
        self.value & other
    }
}

impl BitOr<u8> for Mask {
    type Output = u8;

    #[inline(always)]
    fn bitor(self, other: u8) -> u8 {
        self.value | other
    }
}

impl BitXor<u8> for Mask {
    type Output = u8;

    #[inline(always)]
    fn bitxor(self, other: u8) -> u8 {
        self.value ^ other
    }
}


impl BitAnd<Mask> for u8 {
    type Output = u8;

    #[inline(always)]
    fn bitand(self, other: Mask) -> u8 {
        self & other.value
    }
}

impl BitOr<Mask> for u8 {
    type Output = u8;

    #[inline(always)]
    fn bitor(self, other: Mask) -> u8 {
        self | other.value
    }
}

impl BitXor<Mask> for u8 {
    type Output = u8;

    #[inline(always)]
    fn bitxor(self, other: Mask) -> u8 {
        self ^ other.value
    }
}

impl BitAndAssign<Mask> for u8 {
    #[inline(always)]
    fn bitand_assign(&mut self, other: Mask) {
        *self &= other.value;
    }
}

impl BitOrAssign<Mask> for u8 {
    #[inline(always)]
    fn bitor_assign(&mut self, other: Mask) {
        *self |= other.value;
    }
}

impl BitXorAssign<Mask> for u8 {
    #[inline(always)]
    fn bitxor_assign(&mut self, other: Mask) {
        *self ^= other.value;
    }
}

impl PartialOrd for Mask {
    #[inline(always)]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Mask {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        match self.value.cmp(&other.value) {
            Ordering::Greater => Ordering::Less,
            Ordering::Equal => Ordering::Equal,
            Ordering::Less => Ordering::Greater,
        }
    }
}


#[cfg(test)]
mod mask_tests {
    use super::*;

    #[test]
    fn offsets() {
        for i in 0..8 {
            assert_eq!(Mask::VALUES[i].offset(), i);
        }
    }

    #[test]
    fn checks() {
        let byte = 0b11001010;

        assert_eq!(Mask::VALUES[0].check(byte), true);
        assert_eq!(Mask::VALUES[1].check(byte), true);
        assert_eq!(Mask::VALUES[2].check(byte), false);
        assert_eq!(Mask::VALUES[3].check(byte), false);
        assert_eq!(Mask::VALUES[4].check(byte), true);
        assert_eq!(Mask::VALUES[5].check(byte), false);
        assert_eq!(Mask::VALUES[6].check(byte), true);
        assert_eq!(Mask::VALUES[7].check(byte), false);
    }

    #[test]
    fn shifts() {
        let mask = Mask::VALUES[0];

        for i in 0..32 {
            assert_eq!(mask >> i, Mask::VALUES[i as usize % 8], "i = {}", i);
        }

        for i in 0..32 {
            assert_eq!(mask << i, Mask::VALUES[Mask::BITS as usize - (i + 7) as usize % 8 - 1], "i = {}", i);
        }
    }
}

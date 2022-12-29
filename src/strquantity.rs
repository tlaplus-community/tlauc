use std::marker::Copy;
use std::ops::{Add, Neg, Range, RangeTo, Sub};

#[derive(Clone,Copy,Debug,PartialEq,PartialOrd)]
pub struct CharQuantity<T>(pub T) where T: Copy;

impl<T> CharQuantity<T> where T: Copy {
    pub fn value(self) -> T {
        self.0
    }
}

impl Add<CharQuantity<i8>> for CharQuantity<usize> {
    type Output = CharQuantity<usize>;

    fn add(self, other: CharQuantity<i8>) -> CharQuantity<usize> {
        CharQuantity((self.0 as i32 + other.0 as i32) as usize)
    }
}

impl Sub<CharQuantity<usize>> for CharQuantity<usize> {
    type Output = CharQuantity<usize>;

    fn sub(self, other: CharQuantity<usize>) -> CharQuantity<usize> {
        CharQuantity(self.0 - other.0)
    }
}

#[derive(Clone,Copy,Debug,PartialEq,PartialOrd)]
pub struct ByteQuantity<T>(pub T) where T: Copy;

impl<T> ByteQuantity<T> where T: Copy {
    pub fn as_range(range: &Range<ByteQuantity<T>>) -> Range<T> {
        range.start.0..range.end.0
    }
}

impl ByteQuantity<i8> {
    pub fn as_range_to(other: &ByteQuantity<i8>) -> RangeTo<usize> {
        ..other.0 as usize
    }
}

impl ByteQuantity<usize> {
    pub fn as_range_to(other: &ByteQuantity<usize>) -> RangeTo<usize> {
        ..other.0
    }
}

impl<T> From<CharQuantity<T>> for ByteQuantity<T>
    where T: Copy {
    fn from(other: CharQuantity<T>) -> ByteQuantity<T> {
        ByteQuantity(other.0)
    }
}

impl From<ByteQuantity<usize>> for ByteQuantity<i8> {
    fn from(other: ByteQuantity<usize>) -> ByteQuantity<i8> {
        ByteQuantity(other.0 as i8)
    }
}

impl Add<ByteQuantity<i8>> for ByteQuantity<usize> {
    type Output = ByteQuantity<usize>;

    fn add(self, other: ByteQuantity<i8>) -> ByteQuantity<usize> {
        ByteQuantity((self.0 as i32 + other.0 as i32) as usize)
    }
}

impl Sub<ByteQuantity<usize>> for ByteQuantity<usize> {
    type Output = ByteQuantity<usize>;

    fn sub(self, other: ByteQuantity<usize>) -> ByteQuantity<usize> {
        ByteQuantity(self.0 - other.0)
    }
}

impl Sub<ByteQuantity<i8>> for ByteQuantity<i8> {
    type Output = ByteQuantity<i8>;

    fn sub(self, other: ByteQuantity<i8>) -> ByteQuantity<i8> {
        ByteQuantity(self.0 - other.0)
    }
}

impl Neg for ByteQuantity<i8> {
    type Output = ByteQuantity<i8>;

    fn neg(self) -> ByteQuantity<i8> {
        ByteQuantity(-self.0)
    }
}

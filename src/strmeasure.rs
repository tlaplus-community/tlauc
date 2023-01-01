use std::ops::{Add, Neg, Range, RangeTo, Sub};

#[derive(Debug)]
pub struct StrElementQuantity {
    pub char: CharQuantity,
    pub byte: ByteQuantity,
}

impl StrElementQuantity {
    pub fn from_byte_index(byte_index: &ByteQuantity, text: &str) -> Self {
        StrElementQuantity {
            char: CharQuantity::from_byte_index(byte_index, text),
            byte: byte_index.clone(),
        }
    }
}

#[derive(Debug)]
pub struct StrElementDiff {
    pub char: CharDiff,
    pub byte: ByteDiff,
}

#[derive(Clone, Copy, Debug, PartialEq, PartialOrd)]
pub struct CharQuantity(pub usize);

#[derive(Clone, Copy, Debug, PartialEq, PartialOrd)]
pub struct ByteQuantity(pub usize);

#[derive(Clone, Copy, Debug, PartialEq, PartialOrd)]
pub struct CharDiff(pub i8);

#[derive(Clone, Copy, Debug, PartialEq, PartialOrd)]
pub struct ByteDiff(pub i8);

impl CharQuantity {
    pub fn from_byte_index(byte_index: &ByteQuantity, text: &str) -> Self {
        CharQuantity(text[byte_index.range_to()].chars().count())
    }

    pub fn repeat(&self, text: &str) -> String {
        text.repeat(self.0)
    }
}

impl ByteQuantity {
    pub fn from_char_index(char_index: &CharQuantity, text: &str) -> Self {
        match text.char_indices().nth(char_index.0) {
            Some((byte_index, _)) => ByteQuantity(byte_index),
            None => panic!("Cannot get character {} in string {}", char_index.0, text)
        }
    }

    pub fn as_range(range: &Range<ByteQuantity>) -> Range<usize> {
        range.start.range(&range.end)
    }

    pub fn range_to(&self) -> RangeTo<usize> {
        ..self.0
    }

    fn range(&self, other: &ByteQuantity) -> Range<usize> {
        self.0..other.0
    }
}

impl CharDiff {
    pub fn magnitude(&self) -> CharQuantity {
        CharQuantity(i8::abs(self.0) as usize)
    }
}

impl ByteDiff {
    pub fn magnitude(&self) -> ByteQuantity {
        ByteQuantity(i8::abs(self.0) as usize)
    }
}

impl Add<CharDiff> for CharQuantity {
    type Output = Self;

    fn add(self, offset: CharDiff) -> Self::Output {
        let result = self.0 as i32 + offset.0 as i32;
        assert!(result >= 0, "Adding char offset to char index results in negative value: {} {}", self.0, offset.0);
        CharQuantity(result as usize)
    }
}

impl Add<ByteDiff> for ByteQuantity {
    type Output = Self;

    fn add(self, offset: ByteDiff) -> Self::Output {
        let result = self.0 as i32 + offset.0 as i32;
        assert!(result >= 0, "Adding byte offset to byte index results in negative value: {} {}", self.0, offset.0);
        ByteQuantity(result as usize)
    }
}

impl Sub<CharQuantity> for CharQuantity {
    type Output = CharDiff;

    fn sub(self, other: CharQuantity) -> Self::Output {
        CharDiff((self.0 as i32 - other.0 as i32) as i8)
    }
}

impl Sub<ByteQuantity> for ByteQuantity {
    type Output = ByteDiff;

    fn sub(self, other: ByteQuantity) -> Self::Output {
        ByteDiff((self.0 as i32 - other.0 as i32) as i8)
    }
}

impl Neg for ByteDiff {
    type Output = Self;

    fn neg(self) -> Self::Output {
        ByteDiff(-self.0)
    }
}


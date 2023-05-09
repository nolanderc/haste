use crate::Storage;

#[haste::intern(Text)]
#[derive(PartialEq, Eq, Hash)]
pub struct TextData {
    text: InlineString,
}

impl Text {
    pub fn new(db: &dyn crate::Db, text: &str) -> Self {
        Self::insert(
            db,
            TextData {
                text: InlineString::new(text),
            },
        )
    }

    pub fn get(self, db: &dyn crate::Db) -> &str {
        haste::DatabaseExt::lookup(db, self).text.as_str()
    }
}

impl std::fmt::Debug for TextData {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.text.as_str().fmt(f)
    }
}

impl std::fmt::Display for TextData {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.text.as_str().fmt(f)
    }
}

impl haste::DisplayWith<dyn crate::Db + '_> for Text {
    fn fmt(&self, db: &dyn crate::Db, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.get(db), f)
    }
}

const INLINE_LEN: usize = 22;

enum InlineString {
    Inline { len: u8, bytes: [u8; INLINE_LEN] },
    Heap(Box<str>),
}

impl InlineString {
    fn new(text: &str) -> Self {
        if text.len() <= INLINE_LEN {
            let mut bytes = [0u8; INLINE_LEN];
            bytes[..text.len()].copy_from_slice(text.as_bytes());
            Self::Inline {
                len: text.len() as u8,
                bytes,
            }
        } else {
            Self::Heap(text.into())
        }
    }

    fn as_str(&self) -> &str {
        match self {
            InlineString::Inline { len, bytes } => unsafe {
                std::str::from_utf8_unchecked(&bytes[..*len as usize])
            },
            InlineString::Heap(heap) => heap,
        }
    }
}

impl PartialEq for InlineString {
    fn eq(&self, other: &Self) -> bool {
        self.as_str() == other.as_str()
    }
}

impl Eq for InlineString {}

impl std::hash::Hash for InlineString {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.as_str().hash(state)
    }
}

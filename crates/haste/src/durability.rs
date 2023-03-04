#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Durability(u8);

impl Durability {
    /// A query which often changes
    pub const LOW: Self = Durability(0);

    /// A query which occasionally changes
    pub const MEDIUM: Self = Durability(1);

    /// A query which rarely changes
    pub const HIGH: Self = Durability(2);

    /// A query which will never change.
    pub const CONSTANT: Self = Durability(3);

    /// The highest durability which is not `CONSTANT`
    pub const HIGHEST: Self = Self::HIGH;

    /// Total number of durability levels.
    pub(crate) const LEVELS: usize = Self::CONSTANT.0 as usize;

    pub(crate) fn index(&self) -> usize {
        usize::from(self.0)
    }
}

impl std::fmt::Debug for Durability {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let name = match *self {
            Self::LOW => "LOW",
            Self::MEDIUM => "MEDIUM",
            Self::HIGH => "HIGH",
            Self::CONSTANT => "CONSTANT",
            _ => return write!(f, "Durability({})", self.0),
        };
        f.write_str(name)
    }
}

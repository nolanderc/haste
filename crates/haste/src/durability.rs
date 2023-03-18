/// Durability is an approximate measure of how often an input's value changes.
///
/// This is only used as an optimization and does not affect correctness.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Durability(u8);

impl Durability {
    /// A query which often changes (eg. files in the working directory).
    pub const LOW: Self = Durability(0);

    /// A query which occasionally changes (eg. a list of dependencies)
    pub const MEDIUM: Self = Durability(1);

    /// A query which rarely changes (eg. code from the standard library or other third-parties)
    pub const HIGH: Self = Durability(2);

    /// A query which should never change (eg. a user's `$HOME` directory). Note that even inputs
    /// with `CONSTANT` durability *can* change.
    pub const CONSTANT: Self = Durability(3);

    /// The highest durability which is not `CONSTANT`
    pub const HIGHEST: Self = Self::HIGH;

    /// The default durability of inputs.
    pub const DEFAULT: Self = Self::MEDIUM;

    /// Total number of durability levels.
    pub(crate) const LEVELS: usize = 1 + Self::CONSTANT.index();

    pub(crate) const fn index(&self) -> usize {
        self.0 as usize
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

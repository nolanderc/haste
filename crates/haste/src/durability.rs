#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u8)]
pub enum Durability {
    Low = 0,
    Medium = 1,
    High = 2,
    Constant = 3,
}

impl Durability {
    pub const DEFAULT: Self = Self::Medium;
    pub const LOWEST: Self = Self::Low;
    pub const HIGHEST: Self = Self::High;
}

use std::num::NonZeroU32;

use crate::{revision::Revision, Durability};

pub struct History {
    current: Revision,
    last_change: [Option<Revision>; Durability::LEVELS],
}

impl History {
    pub fn new() -> Self {
        Self {
            current: Revision::new(NonZeroU32::new(1).unwrap()).unwrap(),
            last_change: [None; Durability::LEVELS],
        }
    }

    pub fn current(&self) -> Revision {
        self.current
    }

    pub fn update(&mut self, durability: Durability) {
        self.current = Revision::new(self.current.index().checked_add(1).unwrap())
            .expect("exhausted revision IDs");

        for change in &mut self.last_change[..=durability as usize] {
            *change = Some(self.current);
        }
    }

    pub fn maybe_changed_since(&self, revision: Revision, durability: Durability) -> bool {
        Some(revision) < self.last_change[durability as usize]
    }
}

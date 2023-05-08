use dashmap::DashMap;

use crate::ElementPath;

use super::{ActiveStack, StackId};

#[derive(Default)]
pub(super) struct CycleGraph {
    // For each stack, the stack it is blocked on.
    blocks: DashMap<StackId, Block>,
}

pub(super) struct Block {
    pub blocked_on: StackId,
    pub stack: ActiveStack,
}

impl CycleGraph {
    pub fn insert(&self, block: Block) -> Option<Cycle> {
        let source = block.stack.id;
        let blocked_on = block.blocked_on;

        self.blocks.insert(source, block);

        let start = self.detect_cycle(blocked_on)?;

        let mut participants = Vec::new();
        let mut curr = self.blocks.get(&start)?;

        let first = curr.stack.id;

        loop {
            let next = self.blocks.get(&curr.stack.id)?;

            let first_query = curr.stack.dependencies.last().unwrap().query();
            let position = next
                .stack
                .queries
                .iter()
                .rposition(|query| query.path == first_query)?;

            participants.extend(
                next.stack.queries[position..]
                    .iter()
                    .map(|query| query.path),
            );

            curr = next;

            if curr.stack.id == first {
                break;
            }
        }

        Some(Cycle { participants })
    }

    pub fn remove(&self, source: StackId) -> Option<ActiveStack> {
        let (_, block) = self.blocks.remove(&source)?;
        Some(block.stack)
    }

    fn detect_cycle(&self, start: StackId) -> Option<StackId> {
        let mut tortoise = start;
        let mut hare = self.blocks.get(&start)?.blocked_on;

        let mut len = 1;
        let mut power = 1;
        while tortoise != hare {
            if len == power {
                tortoise = hare;
                power *= 2;
                len = 0;
            }
            hare = self.blocks.get(&hare)?.blocked_on;
            len += 1;
        }

        Some(hare)
    }
}

pub struct Cycle {
    participants: Vec<ElementPath>,
}

impl std::fmt::Debug for Cycle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.participants.fmt(f)
    }
}

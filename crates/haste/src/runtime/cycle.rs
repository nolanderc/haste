use std::{cell::Cell, sync::Arc, task::Waker};

use ahash::HashMap;
use smallvec::SmallVec;

use crate::{ContainerPath, Database, IngredientPath};

#[derive(Default)]
pub struct CycleGraph {
    /// For each currently blocked query: the query they are blocked on
    vertices: HashMap<IngredientPath, Vertex>,

    /// For each query: its cycle recovery strategy
    recover_strategies: HashMap<ContainerPath, CycleStrategy>,
}

struct Vertex {
    /// The query this is blocked on
    blocked_on: IngredientPath,
    /// Points to a query which is known to be further down the dependency chain. This pointer
    /// is only valid for as long as the corresponding query is a valid `Vertex`. This is used
    /// as an optimization to reduce the number nodes that need to be visited when detecting
    /// cycles, similar to path shortening found in
    /// [Disjoint-Sets](https://en.wikipedia.org/wiki/Disjoint-set_data_structure).
    shortcut: Cell<IngredientPath>,

    waker: Waker,
}

impl CycleGraph {
    pub fn insert(
        &mut self,
        source: IngredientPath,
        target: IngredientPath,
        waker: &Waker,
        db: &dyn Database,
    ) {
        let vertex = Vertex {
            blocked_on: target,
            shortcut: Cell::new(target),
            waker: waker.clone(),
        };

        if let Some(previous) = self.vertices.insert(source, vertex) {
            panic!(
                concat!(
                    "the query `{:?}` is blocked on two queries at once ({:?} and {:?})",
                    "\nhelp: use `spawn` or `prefetch` to evaluate queries concurrently"
                ),
                source, previous.blocked_on, target
            );
        }

        self.detect_cycle(source, db);
    }

    pub fn remove(&mut self, source: IngredientPath) {
        if self.vertices.remove(&source).is_none() {
            panic!("called `remove` on an edge that does not exist")
        }
    }

    fn detect_cycle(&mut self, source: IngredientPath, db: &dyn Database) {
        if !self.is_cyclic(source) {
            return;
        }

        // list of all queries that are a part of the cycle
        let mut participants = SmallVec::<[IngredientPath; 8]>::new();
        // cycle participants who have cycle recovery set
        let mut recovered = SmallVec::<[usize; 8]>::new();

        let mut curr = source;

        // enumerate all cycle participants
        for i in 0.. {
            participants.push(curr);

            let strategy = self.lookup_strategy(curr.container, db);
            if strategy == CycleStrategy::Recover {
                recovered.push(i);
            }

            curr = self.vertices[&curr].blocked_on;
            if curr == source {
                break;
            }
        }

        let participants = Arc::<[_]>::from(participants.as_slice());

        let make_cycle = |index: usize| {
            let path = participants[index];
            let cycle = Cycle {
                start: index,
                participants: participants.clone(),
            };
            db.set_cycle(path, cycle);
            self.vertices[&path].waker.wake_by_ref();
        };

        if recovered.is_empty() {
            // distribute the cycle to all participants
            (0..participants.len()).for_each(make_cycle);
        } else {
            recovered.iter().copied().for_each(make_cycle);
        }
    }

    fn is_cyclic(&self, start: IngredientPath) -> bool {
        let mut prev: Option<&Vertex> = None;
        let mut curr = start;

        while let Some(vertex) = self.vertices.get(&curr) {
            let shortcut = vertex.shortcut.get();
            curr = if shortcut == vertex.blocked_on {
                vertex.blocked_on
            } else if self.vertices.contains_key(&shortcut) {
                // the cached query is still valid, so continue from there
                shortcut
            } else {
                vertex.blocked_on
            };

            if let Some(prev) = prev.replace(vertex) {
                // path shortening inspired by disjoint-set datastructure
                prev.shortcut.set(curr);
            }

            if curr == start {
                return true;
            }
        }

        false
    }

    fn lookup_strategy(&mut self, container: ContainerPath, db: &dyn Database) -> CycleStrategy {
        *self
            .recover_strategies
            .entry(container)
            .or_insert_with(|| db.cycle_strategy(container))
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum CycleStrategy {
    Panic,
    Recover,
}

#[derive(Clone)]
pub struct Cycle {
    start: usize,
    participants: Arc<[IngredientPath]>,
}

impl std::fmt::Debug for Cycle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl Cycle {
    pub fn iter(&self) -> impl Iterator<Item = IngredientPath> + '_ {
        let (before, after) = self.participants.split_at(self.start);
        after.iter().chain(before.iter()).copied()
    }

    pub fn fmt<'a>(&'a self, db: &'a dyn Database) -> impl std::fmt::Display + 'a {
        crate::util::fmt::from_fn(|f| {
            let alternate = f.alternate();
            let mut list = f.debug_list();
            for path in self.iter() {
                if alternate {
                    list.entry(&crate::util::fmt::query(db, path));
                } else {
                    list.entry(&path);
                }
            }
            list.finish()
        })
    }
}

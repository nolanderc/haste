use std::{collections::hash_map, sync::Arc, task::Waker};

use ahash::HashMap;
use smallvec::SmallVec;

use crate::{ContainerPath, Database, IngredientPath};

#[derive(Default)]
pub struct CycleGraph {
    /// For each currently blocked query: the query they are blocked on
    vertices: HashMap<IngredientPath, Vertex>,

    /// For each query: its cycle recovery strategy
    recovery: HashMap<ContainerPath, CycleStrategy>,
}

struct Vertex {
    /// The query this is blocked on
    blocked_on: IngredientPath,
    /// Points to the last known query in the dependency chain.
    /// This pointer is only valid for as long as the corresponding query is a valid `Vertex`.
    /// This is used as an optimization to reduce the number nodes that need to be visited when
    /// detecting cycles.
    last_in_chain: IngredientPath,

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
        match self.vertices.entry(source) {
            hash_map::Entry::Occupied(entry) => {
                let previous = entry.get();

                panic!(
                    concat!(
                        "the query `{:?}` is blocked on two queries at once ({:?} and {:?})",
                        "\nhelp: use `spawn` or `prefetch` to execute queries concurrently"
                    ),
                    source, previous.blocked_on, target
                );
            }
            hash_map::Entry::Vacant(entry) => {
                entry.insert(Vertex {
                    blocked_on: target,
                    last_in_chain: target,
                    waker: waker.clone(),
                });
                self.detect_cycle(source, db);
            }
        }
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

        for i in 0.. {
            participants.push(curr);

            let strategy = self.recovery(curr.container, db);
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
            let cycle = Cycle {
                start: index,
                participants: participants.clone(),
            };
            let path = participants[index];
            let container = db.dyn_container_path(path.container).unwrap();
            let cache = container.as_query_cache().unwrap();
            if let Err(cycle) = cache.set_cycle(path.resource, cycle) {
                panic!(
                    "found dependency cycle while recovering from another cycle: {:#}",
                    cycle.fmt(db)
                );
            }
            self.vertices[&path].waker.wake_by_ref();
        };

        if recovered.is_empty() {
            // distribute the cycle to all participants
            (0..participants.len()).for_each(make_cycle);
        } else {
            recovered.iter().copied().for_each(make_cycle);
        }
    }

    fn recovery(&mut self, container: ContainerPath, db: &dyn Database) -> CycleStrategy {
        *self.recovery.entry(container).or_insert_with(|| {
            db.dyn_container_path(container)
                .and_then(|c| c.as_query_cache())
                .map(|cache| cache.cycle_strategy())
                .unwrap_or(CycleStrategy::Panic)
        })
    }

    fn is_cyclic(&mut self, start: IngredientPath) -> bool {
        let mut participants = SmallVec::<[IngredientPath; 8]>::new();
        let mut curr = start;

        while let Some(vertex) = self.vertices.get(&curr) {
            participants.push(curr);

            curr = if vertex.last_in_chain == vertex.blocked_on {
                vertex.blocked_on
            } else if self.vertices.contains_key(&vertex.last_in_chain) {
                // the cached query is still valid, so continue from there
                vertex.last_in_chain
            } else {
                vertex.blocked_on
            };

            if curr == start {
                return true;
            }
        }

        // not a cycle, but all visited queries are blocked on the same query, so add new
        // shortcuts to the last node
        for path in participants {
            self.vertices.get_mut(&path).unwrap().last_in_chain = curr;
        }

        false
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

    pub(crate) fn fmt<'a>(&'a self, db: &'a dyn Database) -> impl std::fmt::Display + 'a {
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

use std::{
    sync::{atomic::Ordering::Relaxed, Arc, Mutex, RwLock},
    task::Waker,
};

use ahash::HashMap;
use dashmap::DashMap;
use smallvec::SmallVec;

use crate::{util::arc::AtomicWeak, ContainerPath, Database, IngredientPath};

#[derive(Default)]
pub struct CycleGraph {
    /// For each currently blocked query: the query they are blocked on
    vertices: DashMap<IngredientPath, Arc<Vertex>>,

    /// For each kind of query: its cycle recovery strategy
    recover_strategies: RwLock<HashMap<ContainerPath, CycleStrategy>>,
}

struct Vertex {
    this: IngredientPath,

    /// The query this is blocked on
    blocked_on: IngredientPath,

    /// Points to a query which is known to be further down the dependency chain. This is used as
    /// an optimization to reduce the number nodes that need to be visited when detecting cycles,
    /// similar to path shortening found in
    /// [Disjoint-Sets](https://en.wikipedia.org/wiki/Disjoint-set_data_structure).
    shortcut: AtomicWeak<Vertex>,

    waker: Mutex<Option<Waker>>,
}

impl CycleGraph {
    pub fn insert(
        &self,
        source: IngredientPath,
        target: IngredientPath,
        waker: &Waker,
        db: &dyn Database,
    ) {
        let vertex = Arc::new(Vertex {
            this: source,
            blocked_on: target,
            shortcut: AtomicWeak::new(None),
            waker: Mutex::new(Some(waker.clone())),
        });

        if let Some(previous) = self.vertices.insert(source, vertex) {
            panic!(
                concat!(
                    "the query `{:?}` is blocked on two queries at once (`{:?}` and `{:?}`)",
                    "\nhelp: use `spawn` or `prefetch` to evaluate queries concurrently"
                ),
                crate::util::fmt::ingredient(db, source),
                crate::util::fmt::ingredient(db, previous.blocked_on),
                crate::util::fmt::ingredient(db, target),
            );
        }

        self.resolve_cycle(source, db);
    }

    pub fn remove(&self, source: IngredientPath) {
        if self.vertices.remove(&source).is_none() {
            panic!("called `remove` on an edge that does not exist")
        }
    }

    fn resolve_cycle(&self, source: IngredientPath, db: &dyn Database) {
        let Some((start, min_length)) = self.find_cycle(source) else { return };

        // list of all queries that are a part of the cycle
        let mut participants = SmallVec::<[IngredientPath; 8]>::with_capacity(min_length);
        // cycle participants who have cycle recovery set
        let mut recovered = SmallVec::<[usize; 8]>::with_capacity(min_length);

        // Holds read-guards to the vertices reperesenting the participants.
        // This ensures that the cycle is not modified while enumerating it.
        let mut vertices = SmallVec::<[_; 8]>::with_capacity(min_length);

        let mut curr = start;

        // enumerate all cycle participants
        for i in 0.. {
            participants.push(curr);

            let strategy = self.lookup_strategy(curr.container, db);
            if strategy == CycleStrategy::Recover {
                recovered.push(i);
            }

            let Some(vertex) = self.vertices.get(&curr) else { return };
            let next = vertex.blocked_on;
            vertices.push(vertex);

            if next == start {
                break;
            }

            curr = next;
        }

        // attempt to take ownership of all the wakers: this ensures that the same cycle is not
        // reported twice
        let mut wakers = SmallVec::<[_; 8]>::with_capacity(vertices.len());
        for (vertex, participant) in vertices.iter().zip(&participants) {
            // tie-break: the cycle started at the query with the highest index wins
            let waker = if participant.ordered() < start.ordered() {
                vertex.waker.lock().unwrap()
            } else {
                match vertex.waker.try_lock() {
                    // we lost the tie-break
                    Err(std::sync::TryLockError::WouldBlock) => return,
                    result => result.unwrap(),
                }
            };

            if waker.is_none() {
                // the cycle has already been reported
                return;
            }

            wakers.push(waker);
        }

        // create the list of participants
        let participants = Arc::<[_]>::from(participants.as_slice());

        let wake_cycle = |index: usize| {
            let path = participants[index];
            let cycle = Cycle {
                start: index,
                participants: participants.clone(),
            };
            db.set_cycle(path, cycle);
            wakers[index].take().unwrap().wake();
        };

        tracing::info!(
            cycle = %Cycle {
                start: 0,
                participants: participants.clone()
            }.fmt(db),
            "found dependency cycle"
        );

        if recovered.is_empty() {
            // distribute the cycle to all participants
            (0..participants.len()).for_each(wake_cycle);
        } else {
            recovered.iter().copied().for_each(wake_cycle);
        }
    }

    /// If a cycle can be reached from `start`, returns a query in the cycle and a lower bound on
    /// the length of the cycle.
    fn find_cycle(&self, start: IngredientPath) -> Option<(IngredientPath, usize)> {
        let mut prev = None;
        let mut next = |curr: Arc<Vertex>| {
            // use the shortcut if it is still valid
            let next = match curr.shortcut.upgrade(Relaxed, Relaxed) {
                Some(shortcut) => shortcut,
                None => self.vertices.get(&curr.blocked_on)?.clone(),
            };

            if let Some(previous) = prev.replace(curr) {
                let shortcut = Arc::downgrade(&next);
                previous.shortcut.swap(Some(shortcut), Relaxed);
            }

            Some(next)
        };

        // Algorithm Source: https://en.wikipedia.org/wiki/Cycle_detection#Brent's_algorithm

        let start_vertex = self.vertices.get(&start)?.clone();

        // lower bound on the length of the cycle
        let mut length = 1;
        let mut power = 1;

        let mut tortoise = start;
        let mut hare = next(start_vertex)?;

        while tortoise != hare.this {
            if length == power {
                // continue with next power of two
                tortoise = hare.this;
                power *= 2;
                length = 0;
            }
            hare = next(hare)?;
            length += 1;
        }

        Some((hare.this, length))
    }

    fn lookup_strategy(&self, container: ContainerPath, db: &dyn Database) -> CycleStrategy {
        if let Some(strategy) = self.recover_strategies.read().unwrap().get(&container) {
            return *strategy;
        }

        let strategy = db.cycle_strategy(container);
        self.recover_strategies
            .write()
            .unwrap()
            .insert(container, strategy);
        strategy
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
        crate::fmt::Adapter::new(
            db,
            crate::util::fmt::from_fn(|f| {
                let mut list = f.debug_list();
                for path in self.iter() {
                    list.entry(&crate::util::fmt::ingredient(db, path));
                }
                list.finish()
            }),
        )
    }
}

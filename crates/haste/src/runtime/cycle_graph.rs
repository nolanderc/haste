use std::{collections::hash_map, sync::Arc};

use ahash::HashMap;
use smallvec::SmallVec;

use crate::{Database, IngredientPath};

/// A graph containing of queries and the 
#[derive(Default)]
pub struct CycleGraph {
    vertices: HashMap<IngredientPath, Vertex>,
}

struct Vertex {
    /// The query this is blocked on
    blocked_on: IngredientPath,
    /// Points to the last known query in the dependency chain.
    /// This pointer is only valid for as long as the corresponding query is a valid `Vertex`.
    /// This is used as an optimization to reduce the number nodes that need to be visited when
    /// detecting cycles.
    last_in_chain: IngredientPath,
    /// If we have found a cycle for this query previously it is stored here.
    cycle: Option<Cycle>,
}

impl CycleGraph {
    pub fn insert(&mut self, source: IngredientPath, target: IngredientPath) -> Option<Cycle> {
        match self.vertices.entry(source) {
            hash_map::Entry::Occupied(entry) => {
                let previous = entry.get();

                if let Some(cycle) = &previous.cycle {
                    return Some(cycle.clone());
                }

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
                    cycle: None,
                });
                self.find_cycle(source)
            }
        }
    }

    pub fn remove(&mut self, source: IngredientPath, target: IngredientPath) {
        self.vertices
            .remove(&source)
            .filter(|vertex| vertex.blocked_on == target)
            .expect("called `remove` on an edge that does not exist");
    }

    fn find_cycle(&mut self, source: IngredientPath) -> Option<Cycle> {
        debug_assert!(self.vertices[&source].cycle.is_none());

        let mut paths = SmallVec::<[IngredientPath; 8]>::new();
        let mut curr = source;

        while let Some(vertex) = self.vertices.get(&curr) {
            paths.push(curr);

            if vertex.cycle.is_some() {
                // there is a cycle ahead, but this query is not directly a part of it
                return None;
            }

            curr = if self.vertices.contains_key(&vertex.last_in_chain) {
                // jump ahead to the last known query in the chain
                vertex.last_in_chain
            } else {
                // otherwise just advance one step
                vertex.blocked_on
            };

            if curr == source {
                break;
            }
        }

        if source != curr {
            // not a cycle, but all visited queries are blocked on the same query, so add new
            // shortcuts to the last node
            for path in paths {
                self.vertices.get_mut(&path).unwrap().last_in_chain = curr;
            }
            return None;
        }

        // at this point we have found a cycle starting at `curr == source`

        // collect *all* the queries that are a part of the cycle
        paths.clear();
        loop {
            paths.push(curr);
            curr = self.vertices[&curr].blocked_on;
            if curr == source {
                break;
            }
        }
        let paths = Arc::<[_]>::from(paths.as_slice());

        // distribute the cycle to all participants
        for i in 0..paths.len() {
            self.vertices.get_mut(&curr).unwrap().cycle = Some(Cycle {
                start: i,
                paths: paths.clone(),
            });
        }

        Some(Cycle { start: 0, paths })
    }
}

#[derive(Clone)]
pub struct Cycle {
    start: usize,
    paths: Arc<[IngredientPath]>,
}

impl std::fmt::Debug for Cycle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl Cycle {
    pub fn iter(&self) -> impl Iterator<Item = IngredientPath> + '_ {
        let (before, after) = self.paths.split_at(self.start);
        after.iter().chain(before.iter()).copied()
    }

    pub fn fmt<'a>(&'a self, db: &'a dyn Database) -> impl std::fmt::Display + 'a {
        crate::util::fmt::from_fn(|f| {
            let alternate = f.alternate();
            let mut list = f.debug_list();
            for path in self.iter() {
                if alternate {
                    unsafe { list.entry(&crate::util::fmt::query(db, path)) };
                } else {
                    list.entry(&path);
                }
            }
            list.finish()
        })
    }
}

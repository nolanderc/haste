use futures_lite::FutureExt;

use crate::{revision::Revision, Dependency};

use super::*;

pub type VerifyFuture<'a, Q: Query> = impl Future<Output = VerifyResult<'a, Q>> + 'a;

pub type VerifyResult<'a, Q> = Result<&'a OutputSlot<Q>, VerifyData<'a, Q>>;

pub struct VerifyData<'a, Q: Query> {
    pub db: &'a DatabaseFor<Q>,
    pub slot: ClaimedSlot<'a, Q>,
    pub storage: &'a QueryStorage<Q>,
}

pub fn verify_shallow<Q: Query>(data: VerifyData<Q>) -> Result<VerifyResult<Q>, VerifyFuture<Q>> {
    let mut data = data;
    let Some(last_verified) = data.slot.last_verified() else {
        return Ok(Err(data))
    };
    let Some(previous) = data.slot.get_output() else {
        return Ok(Err(data))
    };

    if previous.dependencies.is_empty() {
        // the query does not depend on any side-effects, so is trivially verified.
        return Ok(Ok(data.slot.backdate()));
    }

    let runtime = data.db.runtime();

    let inputs = previous.transitive.inputs;
    let durability = previous.transitive.durability();
    if inputs_unchanged(runtime, last_verified, inputs, durability) {
        return Ok(Ok(data.slot.backdate()));
    }

    let dependencies = unsafe { data.storage.dependencies(previous.dependencies) };

    Err(verify_deep(data, last_verified, dependencies))
}

fn inputs_unchanged(
    runtime: &Runtime,
    last_verified: Revision,
    inputs: Option<InputRange>,
    durability: Durability,
) -> bool {
    match inputs {
        // there are no input dependencies, so the value is constant
        None => true,
        Some(range) => !runtime.any_changed_since(range, last_verified, durability),
    }
}

fn verify_deep<'a, Q: Query>(
    mut data: VerifyData<'a, Q>,
    last_verified: Revision,
    dependencies: &'a [Dependency],
) -> VerifyFuture<'a, Q> {
    crate::util::future::map(
        CheckDeepFuture::new(data.db.as_dyn(), last_verified, dependencies),
        move |unchanged| match unchanged {
            None => Err(data),
            Some(new_transitive) => {
                let previous = data.slot.get_output().unwrap();
                previous.transitive.update_inputs(new_transitive);
                return Ok(data.slot.backdate());
            }
        },
    )
}

struct CheckDeepFuture<'a> {
    db: &'a dyn Database,
    last_verified: Revision,
    dependencies: std::slice::Iter<'a, Dependency>,

    transitive: TransitiveDependencies,

    pending: Option<(Dependency, ChangeFuture<'a>)>,
}

impl<'a> CheckDeepFuture<'a> {
    fn new(db: &'a dyn Database, last_verified: Revision, dependencies: &'a [Dependency]) -> Self {
        Self {
            db,
            last_verified,
            dependencies: dependencies.iter(),
            transitive: TransitiveDependencies::CONSTANT,
            pending: None,
        }
    }
}

impl Future for CheckDeepFuture<'_> {
    type Output = Option<TransitiveDependencies>;

    fn poll(mut self: Pin<&mut Self>, cx: &mut std::task::Context<'_>) -> Poll<Self::Output> {
        let db = self.db;

        loop {
            let change;

            if let Some((_dep, ref mut future)) = self.pending {
                change = std::task::ready!(future.poll(cx));
                self.pending = None;
            } else if let Some(&dependency) = self.dependencies.next() {
                match db.last_change(dependency) {
                    LastChangeFuture::Ready(ready) => change = ready,
                    LastChangeFuture::Pending(pending) => {
                        self.pending = Some((dependency, pending));
                        continue;
                    }
                }
            } else {
                return Poll::Ready(Some(self.transitive));
            };

            if Some(self.last_verified) < change.changed_at {
                return Poll::Ready(None);
            }

            self.transitive.extend(change.transitive);
        }
    }
}

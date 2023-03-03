use crate::{Dependency, Revision};

use super::*;

pub type VerifyFuture<'a, Q: Query> =
    impl Future<Output = Result<&'a OutputSlot<Q>, ClaimedSlot<'a, Q>>> + 'a;

/// Verify that the query slot is up-to-date with respect to its dependencies.
/// If this returns `None`, the query needs to be re-executed, otherwise it returns the verified
/// output.
pub fn verify<'a, Q: Query>(
    db: &'a dyn Database,
    storage: &'a QueryStorage<Q>,
    slot: ClaimedSlot<'a, Q>,
) -> VerifyFuture<'a, Q> {
    async move {
        let Some(last_verified) = slot.last_verified() else { return Err(slot) };
        let Some(previous) = slot.get_output() else { return Err(slot) };

        let runtime = db.runtime();

        let maybe_changed =
            inputs_maybe_changed(runtime, last_verified, previous.latest_dependency) && {
                let dependencies = unsafe { storage.dependencies(previous.dependencies.clone()) };
                dependencies_maybe_changed(db, last_verified, dependencies).await
            };

        if maybe_changed {
            // the query might be out-of-date, so we need to re-execute it
            Err(slot)
        } else {
            // all dependencies were up-to-date
            Ok(slot.backdate())
        }
    }
}

fn inputs_maybe_changed(
    runtime: &Runtime,
    last_verified: Revision,
    latest_dependency: Option<Revision>,
) -> bool {
    match latest_dependency {
        // there are no dependencies, so the value is constant
        None => false,

        // This query only depends on inputs in the revisions `..=latest_dependency`.
        // If the only changes made to dependencies are in the range `latest_dependency+1..`
        // the output of this query cannot have changed.
        Some(latest_dependency) => {
            let earliest_change = runtime.earliest_change_since(last_verified);
            latest_dependency >= earliest_change
        }
    }
}

async fn dependencies_maybe_changed(
    db: &dyn Database,
    last_verified: Revision,
    dependencies: &[Dependency],
) -> bool {
    for &dependency in dependencies {
        if Some(last_verified) < db.last_changed(dependency).await {
            return true;
        }
    }
    false
}

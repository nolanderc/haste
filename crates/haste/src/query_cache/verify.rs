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
    mut slot: ClaimedSlot<'a, Q>,
) -> VerifyFuture<'a, Q> {
    async move {
        let Some(last_verified) = slot.last_verified() else { return Err(slot) };
        let Some(previous) = slot.get_output() else { return Err(slot) };

        let runtime = db.runtime();

        let latest_input = previous.transitive.latest_input;
        let durability = previous.transitive.durability;

        if inputs_unchanged(runtime, last_verified, latest_input, durability) {
            tracing::debug!(reason = "inputs unchanged", "backdating");
            return Ok(slot.backdate());
        }

        let dependencies = unsafe { storage.dependencies(previous.dependencies) };
        if let Some(transitive) = dependencies_unchanged(db, last_verified, dependencies).await {
            tracing::debug!(reason = "dependencies unchanged", "backdating");
            previous.transitive.extend(transitive);
            return Ok(slot.backdate());
        }

        Err(slot)
    }
}

fn inputs_unchanged(
    runtime: &Runtime,
    last_verified: Revision,
    latest_dependency: Option<Revision>,
    durability: Durability,
) -> bool {
    match latest_dependency {
        // there are no dependencies, so the value is constant
        None => true,

        // This query only depends on inputs in the revisions `..=latest_dependency`.
        // If the only changes made to dependencies are in the range `latest_dependency+1..`
        // the output of this query cannot have changed.
        Some(latest_dependency) => {
            let earliest_change = runtime.earliest_change_since(last_verified, durability);
            latest_dependency < earliest_change
        }
    }
}

async fn dependencies_unchanged(
    db: &dyn Database,
    last_verified: Revision,
    dependencies: &[Dependency],
) -> Option<TransitiveDependencies> {
    let mut transitive = TransitiveDependencies::CONSTANT;

    for &dependency in dependencies {
        let change = db.last_change(dependency).await;

        if Some(last_verified) < change.changed_at {
            tracing::debug!(
                dependency = %crate::util::fmt::ingredient(db, dependency.ingredient()),
                "change detected"
            );
            return None;
        }

        transitive.extend(change.transitive);
    }

    Some(transitive)
}

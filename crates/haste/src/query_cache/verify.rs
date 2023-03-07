use crate::{revision::Revision, Dependency};

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

        if previous.dependencies.is_empty() {
            // the query does not depend on any side-effects, so is trivially verified.
            tracing::debug!(reason = "no dependencies", "backdating");
            return Ok(slot.backdate());
        }

        let runtime = db.runtime();

        let inputs = previous.transitive.inputs;
        let durability = previous.transitive.durability;

        if inputs_unchanged(runtime, last_verified, inputs, durability) {
            tracing::debug!(reason = "inputs unchanged", "backdating");
            return Ok(slot.backdate());
        }

        let dependencies = unsafe { storage.dependencies(previous.dependencies) };
        if let Some(transitive) = dependencies_unchanged(db, last_verified, dependencies).await {
            tracing::debug!(reason = "dependencies unchanged", "backdating");
            previous.transitive = transitive;
            return Ok(slot.backdate());
        }

        Err(slot)
    }
}

fn inputs_unchanged(
    runtime: &Runtime,
    last_verified: Revision,
    inputs: Option<RevisionRange>,
    durability: Durability,
) -> bool {
    match inputs {
        // there are no input dependencies, so the value is constant
        None => true,
        Some(range) => !runtime.any_changed_since(range, last_verified, durability),
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

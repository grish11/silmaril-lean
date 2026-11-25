# Finite environment projection and run readback

The finite presentation uses Mathlib's `AList`, whose entries have unique
keys. Its view is the existing operational `Environment Key Value`. A row
occurs exactly when the view returns its value, and the row keys support
the view. Different row orders have equal views exactly when the rows are
permutations. Insertion and erasure commute with the functional operations
on environments. A supplied list of keys reconstructs a given environment
if it covers every present binding. That list may repeat keys and may
include absent keys.
[Mathlib association lists at the pinned revision](https://github.com/leanprover/downstream-lean4/blob/569134c2fc750d92baa85d50cd925a7e20a93dd2/mathlib4/Mathlib/Data/List/AList.lean)
· [Finite environments](../../Silmaril/Semantics/Operational/Environment/Finite/Thms.lean)

`Projection` compares a pair of CSLib transition systems with maps on
states and action labels. The soundness direction preserves each transition.
Readback starts with a particular finite source and a semantic step from
its view. It must produce an actual finite step from that source, a label
projecting to the semantic action, and a successor projecting to the
semantic target. Keep any additional layout invariant in the finite
state type so that a returned witness can serve as the next source.
[One-step criterion](../../Silmaril/Semantics/Operational/Projection/Defs.lean)

`execution_readback` uses the chosen finite successor at each step and
returns the full finite execution. Mapping its two lists recovers every
semantic label and intermediate state in order. The examples exercise
an executable write, read, erase and absent read against independent
functional transitions. A second example projects two distinct middle
states to one point. The individually projected labelled edges then form
a path with no finite execution through the chosen middle witness.
[Run theorems](../../Silmaril/Semantics/Operational/Projection/Thms.lean)
· [Examples](../../Silmaril/Semantics/Operational/Environment/Finite/Examples.lean)

## Runtime adapter

For a runtime with finite cells or local slots, use its own state as the
semantic state and fix the view of the chosen finite presentation. Prove
the view agrees with lookup and each exposed update. The `AList` operation
laws can discharge those pointwise obligations, and `encode` can produce
an initial witness when the runtime supplies a finite support. Prove a
separate relation between addresses, allocation metadata and control state
where they participate in a transition. If an allocation label reveals its
address, readback requires the presented allocator to realize that address.
A single deterministic allocator cannot in general reflect every possible
fresh-address choice with the address observed literally.

For indexed slots, `List.finRange slots` covers every key. A symbolic codec
can serialize the finite entries and prove that successful decoding
recovers its named layout. Equality of views alone leaves the order of
those entries unspecified.

For each symbolic or executable step, prove the two fields of `Projection`
over the actual step relations. Use `step_iff` to expose the projected action
and successor, then call `execution_readback` with the concrete initial
witness once these obligations are discharged. Its existential label may
choose any representative with the specified projection. An incoming
response that must retain its exact finite payload needs a separate
readback constraint. Initialization, terminal observations, blocking and
infinite executions also need their own correspondence proofs.

```sh
make check CHECK_TARGETS=+Silmaril.Semantics.Operational.Environment.Finite.Examples
```

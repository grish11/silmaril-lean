# Guarded e-graph snapshots and rebuild

`Silmaril.Formats.PER.EGraph.Thms` has two structural inputs: an ordered term
DAG and a partition snapshot. The DAG checker requires every child to refer
to a strictly earlier term; the child relation is well founded. Class IDs
are separately bounded by the partition's class count. The snapshot models
only the current term-to-class lookup, not a union-find parent forest. The
term DAG remains acyclic even when sound merges make the e-class graph cyclic.

Each term witnesses an e-node: a label and an **ordered** list of current
child class IDs. `Rebuilt` is the hashcons coherence obligation: equal
signatures must have the same owner class. It is equivalent to congruence
of the partition PER on the witnessed applications. This says nothing about
missing applications, the lookup's implementation, or any concrete hash.
An abstract name-to-term binding relation can be projected onto classes;
out-of-range term IDs contribute no binding.

`merge?` checks one proposed partition replacement. A seed must be explicitly
asserted. A rebuild merge requires equal current signatures and distinct
owners, so it can use child equalities only from the **old** partition. The
checker verifies that the new partition joins exactly the two specified old
classes, without dropping old equalities or adding unrelated ones. Reflexivity
on valid IDs, symmetry, transitivity, seed assertions and guarded congruence
justify the equality in every model; the checked step preserves soundness
starting from any sound snapshot, including a discrete one.

`exact_of_rebuilt` identifies the raw-ID partition PER with the generated
guarded PER only when the snapshot is sound, contains the seeds, and is rebuilt.
Syntax checks alone do not prove any of these semantic claims. This slice has
no saturation driver, complexity claim, hash table, union-find, serialization
or external name-to-DASL certificate format.

Build with `lake build --wfail +Silmaril.Formats.PER.EGraph.Thms` and run
`lake env lean -DwarningAsError=true --run tests/formats/GuardedEGraph.lean`.

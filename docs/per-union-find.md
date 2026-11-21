# Finite disjoint sets over PER fibers

`PER.fibers` interprets a lookup `α → Option β` as a partial partition. A key
is supported exactly when the lookup succeeds. A supported key's class is the
fiber of its returned label; unsupported keys are not an extra `none` class.
For a finite `OrderedMap α α`, its keys are exactly the domain: label values
may occur nowhere among the keys, and are not interpreted as parent pointers.
Injective relabeling preserves the PER and therefore the extensional family of
nonempty classes. Equality of those families is equivalent to equality of the
PERs.

`PER.UnionFind` is a separate finite rooted implementation. It checks that
every label names a known self-root. If viewed as a forest it is already
flat: a non-root has one edge to a root, and `find_twice` proves a second
lookup cannot go further. Empty, singleton, and insertion are executable;
inserting an existing key is a no-op and a new key starts alone. `sameClass`
returns `none` for an unknown key, not `some false`.

`union` returns `none` when either key is unknown. Otherwise it redirects
the right root to the left root on all entries in a relabeling pass. The
domain is unchanged; the only new related pairs are across the two selected
old classes. Reversing union gives the same partition, not necessarily the
same map. This reference implementation uses list lookup and whole-map
relabeling, not path compression, union by rank, or an amortized bound.

Fixed points give an existing `PER.Canonical` transversal. This requires no
congruence with any operation on keys and does not specify a canonical root
across different states.

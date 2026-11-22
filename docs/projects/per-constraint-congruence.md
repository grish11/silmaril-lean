# Constructor-congruent constraint models

`Silmaril.Calculi.PERConstraints.Congruence.Thms` restricts the
[CNF constraint institution](per-constraints.md) to models satisfying the
existing `PER.Constructors.Closed` rule. A signature pairs a syntax carrier
with guarded constructors. A translation maps terms and shapes, sends target
child positions to source positions, commutes with constructor application,
and sends enabled tuples to enabled tuples. It need not be injective, reflect
guards, or have a bijection on child positions.

The reduct is exactly inverse image on the underlying PER. The two enabled
premises of the constructor rule transport, and the target child premises are
read at the mapped positions. The resulting model is closed, so the original
CNF satisfaction condition holds on the restricted models, with the same
identity and composition laws. `forgetModels` is an institution morphism
whose maps forget the closedness witness and leave sentences unchanged.

The DASL adapter uses `Tree.map`, the public shape map, and unchanged child
positions. Its proof works under an explicit forward guard implication. A
kernel-checked example enables only reference leaves and collapses two reference
names: their images are valid by the target rule, so the two source leaves are
related in the reduct. This does not impose name equivalences on an arbitrary
source model.

This layer neither generates a closure nor assumes that all PERs are congruent.
It keeps model categories discrete and does not claim that unrestricted
satisfiability implies satisfiability with closed models.

```sh
make check CHECK_TARGETS='Silmaril.Calculi.PERConstraints.Congruence.Dasl.Thms'
```

# Choosing a cut inside the GCM corridor

Click's PLDI ’95 §§2.3–2.4 describe walking upward from the latest block
to the earliest block. The chooser prefers the shallowest loop nest and
then the deepest dominator position. This slice applies those block
constraints to one pure total floating node with supplied definition
and use sites in a typed CFG. [Proceedings][paper] · [Archived PDF][pdf] ·
[Schedule Early][early] · [Schedule Late][late]

The archived PDF has SHA-256
`9b2fae161f346d545a85af481ce7f8b1e5921e77a4fa17ee373780249206aa23`.
`chooseSynthesized?` obtains the existing certified complete dominator
tree and uses the existing loop-forest admission and depth computation.
For a nonempty use list, the early and late bounds determine a walk
through prefixes of the late address, ending at the early address.
The chooser keeps the represented blocks on that path, in the original
inventory order, and enumerates cuts only in those blocks.
[Definitions][defs] · [Tree synthesis][synthesis] · [Loop forest][forest]

The existing checker still resolves each Φ argument by its incoming
source and successor slot. It checks definition availability and local
binding order at each surviving cut. `acceptedCorridorCuts_eq` proves
that filtering blocks first gives exactly the original list of accepted
cuts, including its order. The proof uses the early/late corridor
equivalence to show that every accepted cut's block is visited by the
address walk. [Theorem header][theorems]

Both entry points use the same ranking. At equal loop depth they
prefer longer dominator addresses, which implements Click's block
tie-break. The repository additionally keeps the first accepted cut
in enumeration order at equal scores. Within one block that is the
first legal local cut. The address walk prunes the search while the
accepted list preserves that order.

`choosePlacement_eq` proves exact agreement with the existing chooser
under complete tree evidence. This includes forest refusal, a failing
bound, inverted bounds, and a block corridor with incompatible local
cuts. Empty use lists follow the existing chooser. The proof derives
successor closure from forest admission, and `chooseSynthesized?_eq`
also covers synthesis refusal. [Theorem header][theorems]

The typed regression has nested natural loops and two parallel inner
latch slots that carry distinct Φ operands. It observes depths zero,
one and two, and compares both executable choosers on the same cuts.
It checks the shallowest block, the deepest equal-depth block, the
first legal local cut, both kinds of empty corridor, and refusal
of a malformed use or incomplete inventory. [Regression][regression]

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.GCM.Corridor.Thms +Silmaril.Proofs.SSA.SeaOfNodes.GCM.Corridor.Regression'
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.GCM.Corridor.Correctness
lake env leanchecker Silmaril.SSA.SeaOfNodes.GCM.Corridor.Thms
```

[paper]: https://doi.org/10.1145/207110.207154
[pdf]: https://web.archive.org/web/20140908214434id_/https://courses.cs.washington.edu/courses/cse501/06wi/reading/click-pldi95.pdf
[early]: sea-of-nodes-gcm-early-placement.md
[late]: sea-of-nodes-gcm-late-placement.md
[synthesis]: ../../sea-of-nodes-gcm-synthesized-dominator-tree.md
[forest]: ../../sea-of-nodes-gcm-loop-forest.md
[defs]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/Corridor/Defs.lean
[theorems]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/Corridor/Thms.lean
[regression]: ../../../../Silmaril/Proofs/SSA/SeaOfNodes/GCM/Corridor/Regression.lean

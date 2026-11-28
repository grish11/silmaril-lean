# The Schedule Early bound on a typed CFG

In PLDI ’95 §2.2, Click schedules inputs first and places a floating
instruction in the block of its deepest dominator-tree input. An input
definition must dominate the placement. The paper handles pinned nodes
and explicit control dependencies as part of its traversal. This slice
takes the already resolved definition and use cuts of one pure total
floating node. [Proceedings][paper] · [Archived PDF][pdf] · [Coverage matrix][coverage]

The archived PDF has SHA-256
`9b2fae161f346d545a85af481ce7f8b1e5921e77a4fa17ee373780249206aa23`.
`earlyBound?` chooses a deepest definition block by its synthesized tree
address length, validates every supplied definition cut, and checks
that every definition block is its ancestor. Definitions in incomparable
blocks have no common reachable dominated block. An empty definition
list gives the anonymous entry as the bound. [Definitions][defs] ·
[Tree synthesis][synthesis]

`earlyBound?_spec` identifies dominance by the early bound with dominance
by all definition blocks for every reachable candidate. The theorem
`earlyBound?_isSome_iff` relates success to valid definitions and the
existence of a reachable block dominated by all of them. Both use complete
tree evidence. [Theorem header][theorems]

With a successor-closed inventory and both bounds, `legal_iff_bounds`
characterizes the existing legal corridor. A valid candidate block is
dominated by the early bound and dominates the late bound. At the cut,
same-block operand definitions must precede the insertion, and same-block
reads must follow it. The read conditions still use the exact resolved
occurrence, including each Φ source, slot, and argument index.
`early_dominates_late_of_legal` is a necessary condition for a legal cut.
Even equal bounds can leave incompatible local cut orders.
[Placement legality][legality] · [Late bound][late] · [Theorem header][theorems]

## Example

The public example reuses the late-bound diamond and its synthesized
tree. Definitions are supplied at entry, the fork, and after the binding
in `left`. The two parallel Φ slots read at the left terminator and give
the same `left` block bound as the deepest definition. The block number
is 2. The first two Boolean observations say whether the existing
checker admits cuts zero and one in `left`. The last says whether
discovery finds a cut after adding the right incoming use.
[Example][example] · [Regression][regression]

```lean
import Silmaril.SSA.SeaOfNodes.GCM.EarlyPlacement.Example.Defs

open Silmaril.SSA.SeaOfNodes.GCM.EarlyPlacement.Example

#eval observe
-- some (2, 2, false, true, false)
```

The regressions also cover incomparable definitions, invalid definition
cuts, an empty definition list, and an ordinary read before the local
definition when both block bounds are `left`. [Regression][regression]

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.GCM.EarlyPlacement.Thms +Silmaril.Proofs.SSA.SeaOfNodes.GCM.EarlyPlacement.Regression'
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.GCM.EarlyPlacement.Correctness
lake env leanchecker Silmaril.SSA.SeaOfNodes.GCM.EarlyPlacement.Thms
```

[paper]: https://doi.org/10.1145/207110.207154
[pdf]: https://web.archive.org/web/20140908214434id_/https://courses.cs.washington.edu/courses/cse501/06wi/reading/click-pldi95.pdf
[coverage]: ../coverage.md#global-code-motionglobal-value-numbering
[legality]: sea-of-nodes-gcm-legality.md
[late]: sea-of-nodes-gcm-late-placement.md
[synthesis]: ../../sea-of-nodes-gcm-synthesized-dominator-tree.md
[defs]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/EarlyPlacement/Defs.lean
[theorems]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/EarlyPlacement/Thms.lean
[example]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/EarlyPlacement/Example/Defs.lean
[regression]: ../../../../Silmaril/Proofs/SSA/SeaOfNodes/GCM/EarlyPlacement/Regression.lean

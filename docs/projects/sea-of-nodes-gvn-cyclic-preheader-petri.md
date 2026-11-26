# Coloured Petri completion after native cyclic GVN

Use the original `g.lowerTheta` and the fully normalized `Theta.emit g`
as inputs to the existing `NestedTheta.Petri` backend. Its `initial`,
`Step`, and `result` are indexed by the actual numbered graph. Each graph
therefore supplies its own places, pending marking, child activations and
return colours. The same original typed input tuple supplies the root
argument colours in both cases. The numbered emission's `emit_entry` law
preserves the preheader labels and full ordered Φ and capture wiring.
[Numbered emission](sea-of-nodes-gvn-cyclic-preheader-theta.md) ·
[Coloured firing definitions](../../Silmaril/SSA/RVSDG/NestedTheta/Petri/Defs.lean)

`emit_petri_finishes_iff` pairs the finite result packets of the two
coloured systems. The proof uses `NestedTheta.Petri.finishes_iff` on each
graph separately and the existing numbered return equivalence between
them. A witness consists of a completed marking, a finite chain of legal
firings from the initial marking, and the exact result tuple. Each graph
has its own trace and marking. `emit_petri_no_completion_iff` quantifies
over every result tuple, and `petri_no_completion_iff_observe_none`
relates that absence to the existing partial observation.
[GVN completion theorems](../../Silmaril/SSA/SeaOfNodes/GVN/Cyclic/Iteration/Preheader/Theta/Petri/Thms.lean) ·
[Coloured adequacy](../../Silmaril/SSA/RVSDG/NestedTheta/Petri/Thms.lean)

```lean
module
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader.Theta.Petri.Thms

open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.RVSDG (Tuple)
open Silmaril.SSA.RVSDG.NestedTheta.Petri (Finishes)
open Diamond (Ty Val ValueSort)
open GVN.Cyclic.Activation (Inputs)
open GVN.Cyclic.Builder.Preheader (Native)
open GVN.Cyclic.Iteration.Preheader.Theta
open Pure.SubZero (model)

example {args carried : List (ValueSort Unit)} {entry header : List (List (Ty Unit))}
    {out : ValueSort Unit} (g : Native args carried entry header out)
    (input : Inputs model args) (packet : Tuple (Val model.value) [.value out])
    (original : Finishes (Loop.thetaRuntime model) g.lowerTheta input packet) :
    Finishes (Loop.thetaRuntime model) (emit g) input packet :=
  (emit_petri_finishes_iff g input packet).mpr original
```

The fixture's native header shrinks from five producers to four and then
three. The numbered body sizes are six, five and four including the
routing node. With `(true, false, 3, 4)`, both actual θ entries receive
the original captures followed by the Φ tuple `(true, 7, 7, 7)`.
The check reads the actual numbered preheader operands, interprets its
three Petri primitives, and uses the backend's coloured read and
activation at the fourth root node. Separate numbered runs at bounds 2
and 3 give separate finite completion witnesses for word `99` via
coloured adequacy. With `(true, true, 3, 4)` the guard remains true, and
neither graph has a finite completed trace from its initial marking.
[Regressions](../../Silmaril/Proofs/SSA/SeaOfNodes/GVN/Cyclic/Iteration/Preheader/Regression.lean)

```sh
topic=SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader
make check CHECK_TARGETS="+Silmaril.$topic.Theta.Petri.Thms +Silmaril.Proofs.$topic.Regression"
lake env leanchecker "Silmaril.$topic.Theta.Petri.Thms"
lake env leanchecker "Silmaril.Proofs.$topic.Regression"
```

Click PLDI ’95 §3.1 step 3 motivates the elimination performed by the
native optimizer before lowering. The coloured semantics uses the
numbered θ interface based on Reissmann et al. §§4.1–4.3.
The comparison is existential finite completion from each initial
marking. Firing order, fairness, deadlock, and infinite traces lie
outside that observation.
[Pinned Click PDF](sea-of-nodes-gvn-cyclic-pass.md#sources) ·
[Versioned RVSDG source and coloured model](rvsdg/semantics/rvsdg-nested-petri.md)

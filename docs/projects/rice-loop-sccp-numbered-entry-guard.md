# Emit a numbered RVSDG entry guard for the two-route quad loop

`EntryGuard.compile p facts` runs the existing FIFO singleton admission
and emits one numbered RVSDG graph. Its selector runs on the original
entry bank, before either loop fragment's preheader. A predicate constant
is checked with the existing route operation. A word constant is checked
by two existing unsigned comparisons. Overdefined slots impose no test
and a bottom slot rejects. Each constant check uses γ to continue only
on success. The selector produces control index 1 for coverage and 0
otherwise.
[Emitter](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/SCCP/Dispatch/DeleteRoute/Bypass/Numbered/EntryGuard/Defs.lean)

The final γ consumes that index and the complete original bank in slot
order. Its children are the existing original and specialized numbered
graphs, with their own producer tables and θ bodies. `selector_run`
identifies the selector's actual result with the certified `TupleCovers`
decision. `attach_run` identifies execution with a run of the selected
child alone on exactly the same input and θ bound.
[Selection and observation laws](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/SCCP/Dispatch/DeleteRoute/Bypass/Numbered/EntryGuard/Thms.lean)

Neither the selector nor γ itself consumes a θ activation. For θ bound
`n`, `compile_run` compares the result with the original source at
`3*n+2` block visits. `compile_returns_iff` allows independent finite
witnesses, and `compile_noReturn_iff` compares exhaustion at every θ bound
with absence of a finite source return. These laws apply after singleton
admission for the fixed pure two-route quad profile. Analysis with both
or neither route marked gets the existing refusal. The graph handles
mismatched concrete inputs after successful admission.

## Run both paths of the same numbered graph

```lean
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered.EntryGuard.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered.EntryGuard
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example (program entry facts)
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (model)

abbrev runtime := Silmaril.SSA.SeaOfNodes.Quads.Join.model model

#eval
  let assumptions := facts (.constant ⟨true⟩)
  match compile program assumptions with
  | .error _ => none
  | .ok target =>
    let run (side : Bool) : Nat × Option Nat :=
      let input := entry true side
      let tag := ((selector assumptions).2.toGraph.run runtime input).get .head
      let result := match target.2.run runtime 1 input with
        | none => none
        | some (.cons value .nil) => some value.toNat
      (tag.down.val, result)
    some (run true, run false)
-- some ((1, some 99), 0, some 7)
```

The diagnostic runs the same emitted selector used by the final γ.
The compiled graph performs that selection itself. The regressions
also inspect the final γ in the numbered table, check a mismatched word,
exercise the existing admission refusals and run the original child on
an input for which the other child would keep looping.
[Checked regressions](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/SCCP/Dispatch/DeleteRoute/Bypass/Numbered/EntryGuard/Regression.lean) ·
[Typed CF entry guard](rice-loop-sccp-emitted-entry-guard.md) ·
[Rice and Wegman–Zadeck correspondence](rice-loop-sccp-two-route-worklist.md#source-correspondence)

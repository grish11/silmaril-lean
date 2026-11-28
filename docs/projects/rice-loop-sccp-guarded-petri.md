# Observe coloured Petri completion of the guarded quad loop

Pass the graph returned by numbered `EntryGuard.compile` directly to
`NestedTheta.Petri.initial`, `Step`, `result` or `Finishes`. Its numbered
producer and child tables determine the places and typed colours. The
root supplies the concrete entry bank in its original slot order.
At the final γ, the selected tag creates one live child marking with that
same bank. The child executes its existing numbered fragment and commits the exact
returned packet back to γ.
[Guarded numbered emitter](rice-loop-sccp-numbered-entry-guard.md) ·
[Nested firing semantics](rvsdg/semantics/rvsdg-nested-petri.md)

`finishes_iff_numbered` relates each exact root packet to a finite
numbered run, with independent witnesses for the firing trace and the θ
bound. `completed_packet_eq` identifies the packet of every completed
trace with the packet of any successful numbered run for the same input.
`attach_finishes_iff` gives the same completion criterion for the actual
selected child. On successful compilation, `compile_finishes_iff` connects
the singleton packet to the original source word, and
`compile_no_completion_iff` relates absence of finite completion to
absence of finite source return. These laws quantify over reachable finite
completions from the initial marking of the fixed pure two-route profile.
[Public completion laws](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/SCCP/Dispatch/DeleteRoute/Bypass/Numbered/EntryGuard/Petri/Thms.lean)

## Check both root packets on one net

Paste this into a Lean file and run
`lake env lean -DautoImplicit=false -DwarningAsError=true` on it.

```lean
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered.EntryGuard.Petri.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered.EntryGuard (Target compile)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered.EntryGuard.Petri
  (compile_finishes_iff)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example
  (program entry facts regs width)
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (model)
open Silmaril.SSA.SeaOfNodes.MLIR (Word)
open Silmaril.SSA.RVSDG.NestedTheta.Petri (Finishes)

abbrev runtime := Silmaril.SSA.SeaOfNodes.Quads.Join.model model

def assumptions := facts (.constant ⟨true⟩)
def target : Target regs width := (compile program assumptions).toOption.get (by rfl)

theorem compiled : compile program assumptions = .ok target := rfl

example : Finishes runtime target.2 (entry true true) (.cons (99 : Word width) .nil) :=
  (compile_finishes_iff compiled _ _).mpr ⟨5, rfl⟩

example : Finishes runtime target.2 (entry true false) (.cons (7 : Word width) .nil) :=
  (compile_finishes_iff compiled _ _).mpr ⟨5, rfl⟩
```

The regression executes legal firing traces on this same graph. The
tested schedule completes with `[99]` after 20 firings on the covered input
and `[7]` after 16 on the uncovered input. It also checks that a guarded
graph completes with `[7]` on an input for which its unselected
specialization has no finite completion.
[Checked firing traces](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/SCCP/Dispatch/DeleteRoute/Bypass/Numbered/EntryGuard/Petri/Regression.lean)

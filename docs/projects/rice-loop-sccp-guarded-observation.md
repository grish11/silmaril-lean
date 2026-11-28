# Compare the guarded quad artifacts at one typed entry

`admit source facts` runs the existing FIFO checker once and keeps its
singleton admission evidence. `Admitted.emit` uses that evidence for the
guarded CF and numbered emitters. Coloured Petri uses the same numbered
graph and its initial marking. `Admitted.emitted` identifies both
artifacts with the existing compiler results. Concrete inputs enter the
actual guard, so callers can use covered and uncovered banks with the
same artifact pair.
[Admission and observers](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/SCCP/Dispatch/DeleteRoute/Bypass/Backends/Guarded/Institution/Defs.lean) ·
[Guarded CF](rice-loop-sccp-emitted-entry-guard.md) ·
[Guarded numbered RVSDG](rice-loop-sccp-numbered-entry-guard.md) ·
[Coloured completion](rice-loop-sccp-guarded-petri.md)

`Backend.returns_iff_source` preserves and reflects each exact returned
word. CF has its own block bound, numbered RVSDG has its own θ bound, and
Petri has a finite firing trace to the exact root packet.
`Backend.observe_eq_source` gives all three observers the same canonical
`Part Word`, including undefinedness. CF and numbered observations use
the existing partial evaluators and project their typed return packets.
Petri definedness means that some finite trace reaches a completed
marking from the initial one.

`Sentence.equation` compares the two partial words, so two undefined
observations satisfy an equation. `Sentence.terminates` requires a finite
return at the given valuation. The common `comparison` corridor maps
sentences using `Admitted.emit` and uses the identity on the discrete
category of typed entry banks. `oneSignatureComparison` applies the
repository's one-signature construction to that corridor. The source
sentences range over successfully admitted programs at fixed register
and result widths. A cross-signature comparison would need transport of
the quad programs, typed entry facts, singleton admission evidence and
emitted guards, coherent with reduction of the entry valuation.
[Public comparison laws](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/SCCP/Dispatch/DeleteRoute/Bypass/Backends/Guarded/Institution/Thms.lean)

## Run the same emitted pair at both entries

```lean
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example
  (entry facts program regs width)
open CategoryTheory (Discrete)
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (model evalOp)
open Silmaril.SSA.SeaOfNodes.MLIR (Word)
open Silmaril.SSA.SeaOfNodes.MLIR.Lowering (encodeValues)

def guarded : Admitted regs width :=
  (admit program (facts (.constant ⟨true⟩))).toOption.get (by rfl)

abbrev runtime := Silmaril.SSA.SeaOfNodes.Quads.Join.model model

#eval
  let artifacts := guarded.emit
  let run (side : Bool) (cfFuel : Nat) : Option Nat × Option Nat :=
    let input := entry true side
    let cf := match artifacts.cf.run evalOp cfFuel (encodeValues input) with
      | some (.cons value .nil) => some value.toNat
      | none => none
    let numbered := match artifacts.numbered.2.run runtime 1 input with
      | some (.cons value .nil) => some (value : Word width).toNat
      | none => none
    (cf, numbered)
  (run true 6, run false 7)
-- ((some 99, some 99), some 7, some 7)

example : Backend.petri.Returns guarded.emit (entry true false) (7 : Word width) :=
  (Backend.petri.returns_iff_source guarded _ _).mpr ⟨5, rfl⟩
example (backend : Backend) :
    (targetRoom regs width backend).Sat (Discrete.mk (entry true false))
      ((comparison backend).sen (.terminates guarded)) :=
  ((comparison backend).sat _ _).mpr (Part.dom_iff_mem.mpr
    ⟨(7 : Word width), (guarded.mem_observe_iff _ _).mpr ⟨5, rfl⟩⟩)

```

The two output pairs are ordered CF then numbered. In the regression,
the returning loop and an admitted nonreturning loop both exhaust at CF
bound 1 and θ bound 0. The translated equation between them fails at
the same typed entry in all three rooms, and the nonreturning loop's
termination sentence also fails.
[Checked regressions](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/SCCP/Dispatch/DeleteRoute/Bypass/Backends/Guarded/Institution/Regression.lean)

# Reorder the typed entry of a guarded SCCP loop

A `TwoBackedges.Reindex.Registers old new` is a sort-preserving permutation.
`program` renames every operand and destination in the preheader, header and
both feedback routes, including the header test, selector and return register.
Feedback occurrence IDs and instruction order are preserved. `push` puts
entry facts in the new order, and `pull` reduces a concrete valuation back to
the original order. `covers_iff` and `source_run` prove that coverage and
native execution commute with that reduction, with the same native block
budget in the latter.
[Source API](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/Reindex/Thms.lean)

`solve_assignment` identifies the entire simultaneous least solution in
the new order. It uses the existing abstract producer evaluator and the
least-upper-bound characterization of each Φ over its marked occurrences.
The existing FIFO checker is exact on those marks, so `Guarded.admit_reindex`
proves that admission on the renamed program and facts succeeds with
the same retained feedback occurrence. Clients with an existing `Admitted`
can use `Guarded.reindex` to reuse that evidence without rerunning the solver.
[Admission](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/Reindex/Guarded/Defs.lean)

The existing emitters generate a new typed CF graph and a new numbered
γ/θ graph from the renamed quads and facts. `cf_guard` and `numbered_guard`
compare their emitted entry tests. `backend_returns` and `backend_observe`
compare exact returned words and undefinedness at corresponding entries
for CF, numbered RVSDG and the linked coloured Petri observer. Both
artifacts in a comparison have their own finite witnesses. Petri observes
existence of a finite completed trace. `sourceCorridor` translates partial
equations and termination sentences forward and reduces valuations backward.
`backend_satisfaction` gives the analogous square for generated artifacts
using the existing comparison. The square is scoped to artifacts with an
admitted source and fixed opcode interpretation. Admission transport uses
the final FIFO occurrence marks.
[Guard and observation laws](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/Reindex/Guarded/Thms.lean) ·
[Fixed-entry comparison](rice-loop-sccp-guarded-observation.md)

## Run one emitted artifact pair at two entries

The original bank is `[again, select, byte]`. Move `select` past the byte
to obtain `[again, byte, select]`. The guard accepts exactly the entries
with selector true and byte 7. The same re-emitted artifact pair returns 99
on the accepted entry and 7 by fallback on the rejected entry.

```lean
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Guarded.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example
  (entry facts regs word width)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex (Permutation)
open Silmaril.SSA.SeaOfNodes.Diamond (Val ValueSort dataPorts)
open Silmaril.SSA.SeaOfNodes.Loop.SCCP (BankDecidableEq)
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (model evalOp)
open Silmaril.SSA.SeaOfNodes.MLIR (Word)
open Silmaril.SSA.SeaOfNodes.MLIR.Lowering (encodeValues)
open Silmaril.MLIR.Arith (Width)

abbrev reordered : List (ValueSort Width) := [.predicate, word, .predicate]
abbrev ports := dataPorts reordered

local instance : BankDecidableEq Word ports where
  atPort i := Fin.cases (motive := fun j => DecidableEq (Val Word ports[j]))
    (inferInstance : DecidableEq (ULift Bool))
    (fun j => Fin.cases (motive := fun k => DecidableEq (Val Word ports[k.succ]))
      (inferInstance : DecidableEq (Word width))
      (fun k => Fin.cases (motive := fun l => DecidableEq (Val Word ports[l.succ.succ]))
        (inferInstance : DecidableEq (ULift Bool)) (fun l => l.elim0) k) j) i

def order : Registers regs reordered :=
  Permutation.cons (Permutation.swap (T := Silmaril.SSA.SeaOfNodes.Diamond.Ty Width)
    (.value .predicate) (.value word) []) (.value .predicate)

def original : Admitted regs width :=
  (admit
    Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example.program
    (facts (.constant ⟨true⟩))).toOption.get (by rfl)

def moved : Admitted reordered width := Guarded.reindex order original

def run (side : Bool) (cfFuel : Nat) : Option Nat × Option Nat :=
  let bank := push order (entry true side)
  let artifacts := moved.emit
  ((artifacts.cf.run evalOp cfFuel (encodeValues bank)).map (fun env => (env.get .here).toNat),
   (artifacts.numbered.2.run (Silmaril.SSA.SeaOfNodes.Quads.Join.model model) 1 bank).map
      (fun packet => (packet.get .head : Word width).toNat))

#eval (run true 6, run false 7)
-- ((some 99, some 99), some 7, some 7)

example : admit (program order original.source) (push order original.facts) = .ok moved :=
  Guarded.admit_reindex order original

example : Backend.petri.Returns moved.emit (push order (entry true false)) (7 : Word width) :=
  (Guarded.backend_returns order .petri original _ _).mpr
    ((Backend.petri.returns_iff_source original _ _).mpr ⟨5, rfl⟩)
```

The two values in each pair are CF and numbered RVSDG. The regression
also runs the renamed FIFO checker, checks that the guarded selector moves
to the last slot and exercises equation and termination transport.
[Checked regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/Reindex/Guarded/Regression.lean)

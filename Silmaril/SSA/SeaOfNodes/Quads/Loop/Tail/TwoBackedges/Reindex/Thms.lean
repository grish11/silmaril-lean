module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Thms
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Analysis

/-! Entry coverage, source execution and the least SCCP solution commute with register renaming. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex

open SeaOfNodes.Diamond (Model Val ValueSort dataPorts)
open SeaOfNodes.Diamond.SCCP (Fact TupleCovers)
open SeaOfNodes.Loop.SCCP (BankDecidableEq)
open Tail.Diamond.MLIR.CF.Pruned.Reindex (pull)
open RVSDG (Port Tuple)
open Blocks (Bank)

universe u v w

/-- A slot determines the sort and typed port in a fixed bank. -/
theorem slot_eq {T : Type u} {ports : List T} {s t : T} (p : Port ports s) (q : Port ports t)
    (same : slot p = slot q) : (⟨s, p⟩ : Sigma (Port ports)) = ⟨t, q⟩ :=
  Proofs.slot_eq p q same

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {old new : List (ValueSort Data)} {out : ValueSort Data}
variable (order : Registers old new)

/-- Keep each constant, overdefined or unseen fact at its corresponding typed position. -/
theorem covers_iff {value : Data → Type w} (facts : Tuple (Fact value) (dataPorts old))
    (input : Tuple (Val value) (dataPorts new)) :
    TupleCovers (push order facts) input ↔ TupleCovers facts (pull order input) :=
  Proofs.covers_iff order facts input

theorem pull_push {F : SeaOfNodes.Diamond.Ty Data → Type w} (input : Tuple F (dataPorts old)) :
    pull order (push order input) = input :=
  Proofs.pull_push order input

/-- All native block budgets agree, including exhaustion. -/
theorem source_run (m : Model.{u, v, w} Op) (p : Program Op old out)
    (fuel : Nat) (input : Bank (regs := new) m) :
    (program order p).source.runFrom m fuel 0 input = p.source.runFrom m fuel 0 (pull order input) :=
  Proofs.source_run order m p fuel input

variable (m : Model.{u, v, w} Op) (p : Program Op old out)
variable [BankDecidableEq m.value (dataPorts old)] [BankDecidableEq m.value (dataPorts new)]
variable (facts : Tuple (Fact m.value) (dataPorts old))

/-- The same ordered abstract producer equations commute before solving. -/
theorem transfer_assignment (state : SCCP.State m.value old out) :
    SCCP.transfer m (program order p) (push order facts) (assignment order state) =
      assignment order (SCCP.transfer m p facts state) :=
  Proofs.transfer_assignment order m p facts state

/-- Leastness identifies the entire renamed solution, including both feedback
occurrence marks. This argument is independent of the solver's schedule. -/
theorem solve_assignment :
    SCCP.solve m (program order p) (push order facts) = assignment order (SCCP.solve m p facts) :=
  Proofs.solve_assignment order m p facts

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex

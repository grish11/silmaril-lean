module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Weakening.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Weakening.Analysis

/-! Projection laws for every old slot, native run and abstract equation. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Weakening

open SeaOfNodes.Diamond (Model Val ValueSort dataPorts sortValue)
open SeaOfNodes.Diamond.SCCP (Fact TupleCovers)
open SeaOfNodes.Loop.SCCP (BankDecidableEq)
open RVSDG (Tuple)
open Blocks (Bank)
open Join (Block)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {fresh out : ValueSort Data}

theorem covers_iff {value : Data → Type w} (inputFacts : Tuple (Fact value) (dataPorts regs))
    (input : Tuple (Val value) (dataPorts (fresh :: regs))) :
    TupleCovers (facts fresh inputFacts) input ↔ TupleCovers inputFacts (project input) :=
  Proofs.covers_iff inputFacts input

variable (m : Model.{u, v, w} Op)

/-- No source quad reads or overwrites the new slot. -/
theorem block_eval (block : Block Op regs) (value : sortValue m.value fresh)
    (bank : Bank (regs := regs) m) :
    Block.eval (block.map (quad fresh)) m (.cons value bank) = .cons value (block.eval m bank) :=
  Proofs.block_eval m block value bank

/-- Projection preserves the native word or exhaustion at every block budget. -/
theorem source_run (p : Program Op regs out) (fuel : Nat) (input : Bank (regs := fresh :: regs) m) :
    (program fresh p).source.runFrom m fuel 0 input = p.source.runFrom m fuel 0 (project input) :=
  Proofs.source_run m p fuel input

variable (p : Program Op regs out)
variable [oldEq : BankDecidableEq m.value (dataPorts regs)]
variable (freshEq : DecidableEq (sortValue m.value fresh))
variable (input : Tuple (Fact m.value) (dataPorts regs))

theorem transfer_project (state : SCCP.State m.value (fresh :: regs) out) :
    projectState (@SCCP.transfer _ _ _ _ m (program fresh p) (extendEq freshEq oldEq) (facts fresh input) state) =
      SCCP.transfer m p input (projectState state) :=
  Proofs.transfer_project m p freshEq input state

/-- The least solution projects to all original facts and occurrence marks. -/
theorem solve_project :
    projectState (@SCCP.solve _ _ _ _ m (program fresh p) (extendEq freshEq oldEq) (facts fresh input)) =
      SCCP.solve m p input :=
  Proofs.solve_project m p freshEq input

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Weakening

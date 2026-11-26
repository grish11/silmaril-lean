module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Boundaries.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Thms
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.MLIR.CF.InnerPhi.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Boundaries.Waiting
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Cut.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Phi.Readback.Thms

/-! Complete typed packets on the actual emitted join places. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open Silmaril.MLIR.Arith (Width)
open Blocks (Bank)
open RVSDG.NestedTheta.Petri (finishes_iff pending)
open Shared.MLIR.CF.InnerPhi (gamma_run headerBank side occurrence)
open MLIR.CF.Phi (pack arrivalSide arrivalEnv)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} (p : Program src entry)
variable (input old : Bank (regs := regs) model)

theorem outer_reaches :
    OuterReads p old (p.outerBank model old (p.toControl.selected model old)) :=
  (outerCut p).2.2.reads_of_finishes semantics old _
    ((finishes_iff semantics (outerRegion p).toGraph old _).mpr ⟨0, outer_run p model 0 old⟩)

theorem inner_reaches :
    InnerReads p old (p.toRoutes.prefixBank model old (occurrence (side p.toRoutes old))) :=
  (innerCut p).2.2.reads_of_finishes semantics _ _
    ((finishes_iff semantics (innerPrefix p).toGraph _ _).mpr ⟨0, gamma_run p.toRoutes old 0⟩)

/-- The published outer bank has exactly the complete CF operands in
their destination order, including the explicit Φ payload. -/
theorem outer_packet (rows : MLIR.CF.Phi.Rows p) :
    ∃ bank, OuterReads p old bank ∧
      encodeValues bank = MLIR.CF.Phi.Readback.readBank rows (arrivalSide (p := p) old) (arrivalEnv input old) ∧
      pack (encodeValues bank) = rows.latch input old := by
  refine ⟨_, outer_reaches p old, ?_, ?_⟩
  · rw [MLIR.CF.Phi.Readback.readBank_eq]
    exact (rows.selected_bank input old).symm
  · rw [rows.latch_eq, rows.selected_bank]

/-- The inner child publishes the complete reconstructed inner-tail packet. -/
theorem inner_packet (rows : Shared.MLIR.CF.InnerPhi.Rows p.toRoutes) :
    ∃ bank, InnerReads p old bank ∧ encodeValues bank = rows.bank (side p.toRoutes old) input old :=
  ⟨_, inner_reaches p old, (rows.bank_eq (side p.toRoutes old) input old).symm⟩

/-- Within the actual θ body, the outer γ can still be waiting on its
true child when the inner γ has marked all of the CF/Φ arguments. -/
theorem inner_waiting_packet (rows : Shared.MLIR.CF.InnerPhi.Rows p.toRoutes)
    (entered : ((headerBank p.toRoutes old).get p.outerTest).down = true) :
    ∃ mark bank, Waiting p old 0 mark ∧ readInner p old 0 mark = some bank ∧
      encodeValues bank = rows.bank (side p.toRoutes old) input old := by
  have choice : (Prefix.outerChoice p.toRoutes).eval (headerBank p.toRoutes old) = 0 := by
    simp [Prefix.outerChoice, Join.Choice.eval, entered]
  obtain ⟨bank, ⟨mark, steps, colours⟩, packet⟩ := inner_packet p input old rows
  exact ⟨mark, bank, Proofs.waiting_reaches p old 0 choice mark steps, colours, packet⟩

/-- The actual outer-false child has a legal waiting marking and bypasses
the inner boundary. Its outer result is still covered by outer_packet. -/
theorem bypass (taken : ((headerBank p.toRoutes old).get p.outerTest).down = false) :
    ∃ mark, Waiting p old 1 mark ∧ readInner p old 1 mark = none := by
  have choice : (Prefix.outerChoice p.toRoutes).eval (headerBank p.toRoutes old) = 1 := by
    simp [Prefix.outerChoice, Join.Choice.eval, taken]
  exact ⟨pending semantics _, Proofs.waiting_reaches p old 1 choice _ .refl, rfl⟩

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri

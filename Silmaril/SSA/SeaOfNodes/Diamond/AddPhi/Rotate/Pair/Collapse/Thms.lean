module

public import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Collapse.Defs
import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Collapse.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Collapse

open Pure.SubZero (model)
open RVSDG (Tuple)

variable {inputs : List (ValueSort Unit)} {sigs : List (List (Ty Unit))}
variable {g : AddPhi.Pair.Source inputs sigs} {x : InputWord inputs}
variable {target : Program inputs sigs []}

/-- Exact admission and emitted shape for the constant-result branch. -/
theorem rewrite_eq_ok_iff :
    rewrite g x = .ok target ↔
      ∃ first second, AddPhi.Pair.literalRows? g = some (first, second) ∧
        AddPhi.Pair.nonconstantColumns first second = true ∧
        AddPhi.Pair.add first = AddPhi.Pair.add second ∧
        target = emit g x (AddPhi.Pair.add first) :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Collapse.rewrite_eq_ok_iff

/-- Return the old capture with no residual binding when the common sum is zero. -/
theorem suffix_zero : suffix 0 = returnCapture := rfl

/-- A nonzero common sum produces one literal and one add in the suffix. -/
theorem suffix_nonzero {value : BitVec 64} (nonzero : value ≠ 0) :
    suffix value = addConstant value := ite_eq_right nonzero

/-- Each original Region occurrence has the same wrapping return value. -/
theorem rewrite_slot_eval_eq (accepted : rewrite g x = .ok target)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (slot : Slot) :
    target.atSlot entry slot = (original g x).atSlot entry slot :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Collapse.slot_eval_eq accepted entry slot

/-- The emitted program preserves the return at every typed entry. -/
theorem rewrite_denote_eq (accepted : rewrite g x = .ok target)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    target.denote entry = (original g x).denote entry :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Collapse.denote_eq accepted entry

/-- Both native programs have exactly the same finite return observations. -/
theorem rewrite_returns_iff (accepted : rewrite g x = .ok target)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (value : BitVec 64) :
    target.Returns entry value ↔ (original g x).Returns entry value := by
  rw [Program.returns_iff_denote, Program.returns_iff_denote, rewrite_denote_eq accepted]

end Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Collapse

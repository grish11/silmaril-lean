module

public import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate

open Pure.SubZero (model word)
open RVSDG (Tuple)

variable {inputs joined : List (ValueSort Unit)} {sigs : List (List (Ty Unit))}

/-- Native finite return is the selected arm followed by the stored pure suffix. -/
theorem Program.returns_iff_denote (p : Program inputs sigs joined)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (value : BitVec 64) :
    p.Returns entry value ↔ p.denote entry = value :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.returns_iff_denote p entry value

variable {g : WordGraph inputs sigs} {x : InputWord inputs} {k : WordWire inputs sigs}
variable {target : Program inputs sigs [word]}

/-- The emitted suffix uses the original residual argument. The original
shared table, guard and ordered Region are retained. -/
theorem rewrite?_emitted_shape (accepted : rewrite? g x k = some target) :
    target.residual = x ∧ target.suffix = residualAdd ∧
      target.diamond.shared = g.dataflow ∧ target.diamond.predicate = g.predicate ∧
      target.diamond.merge = g.phi.merge :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.emitted_shape accepted

/-- The new suffix returns the same word at each original predecessor occurrence. -/
theorem rewrite?_slot_eval_eq (accepted : rewrite? g x k = some target)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (slot : Slot) :
    target.atSlot entry slot = (original g x k).atSlot entry slot :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.slot_eval_eq accepted entry slot

/-- The actual emitted program has the same result for every typed input. -/
theorem rewrite?_denote_eq (accepted : rewrite? g x k = some target)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    target.denote entry = (original g x k).denote entry :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.denote_eq accepted entry

/-- The rewrite preserves and reflects finite returns, including the residual add. -/
theorem rewrite?_returns_iff (accepted : rewrite? g x k = some target)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (value : BitVec 64) :
    target.Returns entry value ↔ (original g x k).Returns entry value := by
  rw [Program.returns_iff_denote, Program.returns_iff_denote, rewrite?_denote_eq accepted]

end Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate

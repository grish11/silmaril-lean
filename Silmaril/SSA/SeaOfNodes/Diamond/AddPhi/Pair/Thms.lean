module

public import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Pair.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Pair.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Pair

open Pure.ConstantFold (Literals)
open Pure.SubZero (model)
open RVSDG (Tuple extend)

variable {inputs : List (ValueSort Unit)} {sigs : List (List (Ty Unit))}
variable {g : Source inputs sigs} {target : Result inputs sigs}

/-- Each checked row is the interpreted join tuple at its own predecessor. -/
theorem literalRows?_slot_eval_eq {first second : Operands}
    (found : literalRows? g = some (first, second))
    (entry : Tuple (Val model.value) (dataPorts inputs)) (slot : Slot) :
    (g.arms slot).eval model entry (g.shared.eval model entry PUnit.unit) =
      match slot with
      | .first => first
      | .second => second :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Pair.literalRows_slot_eval_eq found entry slot

/-- The guarded literal fold checks both ordered rows at their original occurrences. -/
theorem rewriteWith?_admission {admit : Operands → Operands → Bool}
    (accepted : rewriteWith? admit g = some target) :
    let known : Literals (dataPorts inputs) (extend [] sigs) := scanLiterals (fun _ => none) g.shared
    ∃ first second, armLiterals? known (g.arms .first) = some first ∧
      armLiterals? known (g.arms .second) = some second ∧
      admit first second = true ∧ target = emit g first second :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Pair.accepted_eq accepted

/-- A caller's guard affects admission. Every emitted row still has the original pair sum. -/
theorem rewriteWith?_slot_eval_eq {admit : Operands → Operands → Bool}
    (accepted : rewriteWith? admit g = some target)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (slot : Slot) :
    (target.arms slot).eval model entry (target.shared.eval model entry PUnit.unit) =
      .cons (sourceAt g entry slot) .nil :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Pair.slot_eval_eq accepted entry slot

/-- Both original rows were checked in their own typed scopes, in Region order. -/
theorem rewrite?_admission (accepted : rewrite? g = some target) :
    let known : Literals (dataPorts inputs) (extend [] sigs) := scanLiterals (fun _ => none) g.shared
    ∃ first second, armLiterals? known (g.arms .first) = some first ∧
      armLiterals? known (g.arms .second) = some second ∧
      eligible first second = true ∧ target = emit g first second :=
  rewriteWith?_admission (admit := eligible) accepted

/-- The shared prefix, predicate and exact Region order are retained. -/
theorem rewrite?_keeps_control (accepted : rewrite? g = some target) :
    target.shared = g.shared ∧ target.predicate = g.predicate ∧ target.merge = g.merge :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Pair.keeps_control (admit := eligible) accepted

/-- Each rewritten operand is the original add of that occurrence's two values. -/
theorem rewrite?_slot_eval_eq (accepted : rewrite? g = some target)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (slot : Slot) :
    (target.arms slot).eval model entry (target.shared.eval model entry PUnit.unit) =
      .cons (sourceAt g entry slot) .nil :=
  rewriteWith?_slot_eval_eq (admit := eligible) accepted entry slot

/-- The selected native arm returns the original modular sum for each typed entry. -/
theorem rewrite?_denote_eq (accepted : rewrite? g = some target)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    target.denote model entry = .cons (sourceDenote g entry) .nil :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Pair.denote_eq accepted entry

/-- Finite return observations of the nominated add and emitted Φ coincide. -/
theorem rewrite?_returns_iff (accepted : rewrite? g = some target)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (result : BitVec 64) :
    target.Returns model entry (.cons result .nil) ↔ SourceReturns g entry result :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Pair.returns_iff accepted entry result

end Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Pair

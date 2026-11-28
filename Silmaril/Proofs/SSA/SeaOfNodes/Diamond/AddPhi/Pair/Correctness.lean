module

public import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Pair.Defs
import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Thms
import Silmaril.SSA.SeaOfNodes.Diamond.Arms.Thms
import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Pair

open Silmaril.SSA
open SeaOfNodes.Diamond
open SeaOfNodes.Diamond.AddPhi (Result scanLiterals scanLiterals_agrees literalArm_eval)
open SeaOfNodes.Diamond.AddPhi.Pair
open SeaOfNodes.Pure.ConstantFold
open SeaOfNodes.Pure.SubZero (model word wordPort)
open RVSDG (Locals Tuple extend)

variable {inputs : List (ValueSort Unit)} {sigs : List (List (Ty Unit))}
variable {g : Source inputs sigs} {target : Result inputs sigs} {admit : Operands → Operands → Bool}

private theorem literalRows_found {first second : Operands} (found : literalRows? g = some (first, second)) :
    let known : Literals (dataPorts inputs) (extend [] sigs) := scanLiterals (fun _ => none) g.shared
    armLiterals? known (g.arms .first) = some first ∧ armLiterals? known (g.arms .second) = some second := by
  unfold literalRows? at found
  obtain ⟨left, leftEq, found⟩ := Option.bind_eq_some_iff.mp found
  obtain ⟨right, rightEq, found⟩ := Option.bind_eq_some_iff.mp found
  cases Option.some.inj found
  exact ⟨leftEq, rightEq⟩

private theorem accepted_rows (accepted : rewriteWith? admit g = some target) :
    ∃ first second, literalRows? g = some (first, second) ∧
      admit first second = true ∧ target = emit g first second := by
  unfold rewriteWith? at accepted
  obtain ⟨⟨first, second⟩, found, accepted⟩ := Option.bind_eq_some_iff.mp accepted
  dsimp only at accepted
  split at accepted
  · rename_i admitted
    exact ⟨first, second, found, admitted, (Option.some.inj accepted).symm⟩
  · contradiction

theorem accepted_eq (accepted : rewriteWith? admit g = some target) :
    let known : Literals (dataPorts inputs) (extend [] sigs) := scanLiterals (fun _ => none) g.shared
    ∃ first second, armLiterals? known (g.arms .first) = some first ∧
      armLiterals? known (g.arms .second) = some second ∧
      admit first second = true ∧ target = emit g first second := by
  obtain ⟨first, second, found, admitted, emitted⟩ := accepted_rows accepted
  obtain ⟨firstEq, secondEq⟩ := literalRows_found found
  exact ⟨first, second, firstEq, secondEq, admitted, emitted⟩

private theorem armLiterals_eval {args : List (Ty Unit)} {past : List (List (Ty Unit))}
    {known : Literals args past} {arm : Arms.Arm SeaOfNodes.Pure.SubZero.Opcode args past [word, word]}
    {entry : Tuple (Val model.value) args} {locals : Locals (Val model.value) past}
    (agree : Scan.Literals.Agrees known entry locals) {operands : Operands}
    (found : armLiterals? known arm = some operands) : arm.eval model entry locals = operands :=
  Scan.literalInputs_sound (scanLiterals_agrees arm.dataflow known entry locals agree) arm.outputs found

theorem literalRows_slot_eval_eq {first second : Operands} (found : literalRows? g = some (first, second))
    (entry : Tuple (Val model.value) (dataPorts inputs)) (slot : Slot) :
    (g.arms slot).eval model entry (g.shared.eval model entry PUnit.unit) =
      match slot with
      | .first => first
      | .second => second := by
  have facts : Scan.Literals.Agrees (scanLiterals (fun _ => none) g.shared) entry
      (g.shared.eval model entry PUnit.unit) :=
    scanLiterals_agrees g.shared (fun _ => none) entry PUnit.unit (by intro _ _ _ h; contradiction)
  obtain ⟨firstEq, secondEq⟩ := literalRows_found found
  cases slot
  · exact armLiterals_eval facts firstEq
  · exact armLiterals_eval facts secondEq

theorem keeps_control (accepted : rewriteWith? admit g = some target) :
    target.shared = g.shared ∧ target.predicate = g.predicate ∧ target.merge = g.merge := by
  obtain ⟨first, second, _, _, _, rfl⟩ := accepted_eq accepted
  exact ⟨rfl, rfl, rfl⟩

theorem slot_eval_eq (accepted : rewriteWith? admit g = some target)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (slot : Slot) :
    (target.arms slot).eval model entry (target.shared.eval model entry PUnit.unit) =
      .cons (sourceAt g entry slot) .nil := by
  obtain ⟨first, second, found, _, rfl⟩ := accepted_rows accepted
  have readRow := literalRows_slot_eval_eq found entry slot
  cases slot <;> simp only [emit, sourceAt, readRow, literalArm_eval]

theorem denote_eq (accepted : rewrite? g = some target)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    target.denote model entry = .cons (sourceDenote g entry) .nil := by
  obtain ⟨sharedEq, predicateEq, mergeEq⟩ := keeps_control (admit := eligible) accepted
  unfold Arms.Graph.denote sourceDenote
  rw [slot_eval_eq (admit := eligible) accepted, sharedEq, predicateEq, mergeEq]
  rfl

theorem returns_iff (accepted : rewrite? g = some target)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (result : BitVec 64) :
    target.Returns model entry (.cons result .nil) ↔ SourceReturns g entry result := by
  rw [Arms.Graph.returns_iff_denote, denote_eq accepted]
  simp only [SourceReturns, Arms.Graph.returns_iff_denote]
  constructor
  · intro equal
    exact ⟨g.denote model entry, rfl, congrArg (fun row => row.get .head) equal⟩
  · rintro ⟨_, rfl, equal⟩
    exact congrArg (fun v : BitVec 64 => Tuple.cons (F := Val model.value) (t := wordPort) v .nil) equal

end Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Pair

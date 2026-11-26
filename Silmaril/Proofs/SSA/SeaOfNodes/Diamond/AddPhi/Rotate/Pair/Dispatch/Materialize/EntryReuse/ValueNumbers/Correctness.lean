module

public import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.ValueNumbers.Defs
import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Thms
import Silmaril.SSA.SeaOfNodes.GVN.Thms
import Silmaril.SSA.SeaOfNodes.GVN.WordNumber.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.ValueNumbers

open Silmaril.SSA.SeaOfNodes.Diamond
open AddPhi.Rotate (Program)
open AddPhi.Rotate.Pair.Dispatch.Materialize (suffix)
open AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse
open AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.ValueNumbers
open Silmaril.SSA.SeaOfNodes.GVN.WordNumber (Key entry_read_agrees eval_agrees)
open Silmaril.SSA.SeaOfNodes.Pure.SubZero (model word)
open Silmaril.SSA.RVSDG (Tuple)

variable {inputs : List (ValueSort Unit)} {sigs : List (List (Ty Unit))}
variable {p : Program inputs sigs [word]} {rep : EntryAdd p} {target : Program inputs sigs [word, word]}

theorem check_pairing (checked : ValueNumbers.check p rep = true) (slot : Slot) :
    ∃ lhs rhs, rep.key = addKey lhs rhs ∧
      operandKey (sharedKeys p) lhs = .argument p.residual ∧
      operandKey (sharedKeys p) rhs = phiKey p (sharedKeys p) slot := by
  cases found : addOperands? rep.key with
  | none => simp [ValueNumbers.check, found] at checked
  | some key =>
    obtain ⟨⟨lhs, rhs⟩, keyEq⟩ := key
    simp only [ValueNumbers.check, found, Bool.and_eq_true] at checked
    refine ⟨lhs, rhs, keyEq, Key.eq_of_matches checked.1.1, ?_⟩
    cases slot
    · exact Key.eq_of_matches checked.1.2
    · exact Key.eq_of_matches checked.2

private theorem operandKey_eval (p : Program inputs sigs [word])
    (entry : Tuple (Val model.value) (dataPorts inputs)) (wire : SharedWord inputs sigs) :
    (operandKey (sharedKeys p) wire).eval entry =
      read model wire entry (p.diamond.shared.eval model entry PUnit.unit) :=
  eval_agrees p.diamond.shared (entry_read_agrees entry) wire

theorem phiKey_eval (p : Program inputs sigs [word])
    (entry : Tuple (Val model.value) (dataPorts inputs)) (slot : Slot) :
    (phiKey p (sharedKeys p) slot).eval entry =
      ((p.diamond.arms slot).eval model entry (p.diamond.shared.eval model entry PUnit.unit)).get .head := by
  let arm := p.diamond.arms slot
  have agree := eval_agrees arm.dataflow (operandKey_eval p entry) (arm.outputs.get .head)
  refine agree.trans ?_
  change read model (arm.outputs.get .head) entry _ = (arm.eval model entry _).get .head
  dsimp only [Arms.Arm.eval]
  generalize arm.outputs = wires
  cases wires with
  | cons wire tail => cases tail; rfl

theorem check_agrees (checked : ValueNumbers.check p rep = true) : RepresentativeAgrees p rep := by
  intro entry slot
  obtain ⟨lhs, rhs, key, capture, phi⟩ := check_pairing checked slot
  have leftEq := congrArg (Key.eval entry) capture
  have rightEq := congrArg (Key.eval entry) phi
  rw [operandKey_eval] at leftEq
  rw [operandKey_eval, phiKey_eval] at rightEq
  have same := rep.read_key model entry PUnit.unit
  rw [key] at same
  let locals := p.diamond.shared.eval model entry PUnit.unit
  change read model rep.origin entry locals =
    BitVec.add (read model lhs entry locals) (read model rhs entry locals) at same
  rw [leftEq, rightEq] at same
  exact same

theorem discover_eq_some_iff :
    discoverAndRewrite? p = some target ↔
      ∃ value rep, p.suffix = suffix .right value ∧
        findRepresentative? p = some rep ∧ target = emit p rep value := by
  constructor
  · intro accepted
    obtain ⟨matched, _, next⟩ := Option.bind_eq_some_iff.mp accepted
    obtain ⟨rep, found, output⟩ := Option.bind_eq_some_iff.mp next
    exact ⟨matched.val, rep, matched.property, found, (Option.some.inj output).symm⟩
  · rintro ⟨value, rep, shape, found, rfl⟩
    have hit : rightValue? (suffix .right value) = some ⟨value, rfl⟩ := rfl
    simp only [discoverAndRewrite?]
    generalize h : p.suffix = old
    rw [h] at shape
    subst old
    simp [hit, found]

end Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.ValueNumbers

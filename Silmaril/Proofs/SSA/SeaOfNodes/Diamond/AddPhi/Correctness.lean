module

public import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Defs
import Silmaril.SSA.SeaOfNodes.Diamond.Arms.Thms
import Silmaril.SSA.SeaOfNodes.Diamond.Thms
import Silmaril.SSA.SeaOfNodes.GVN.Thms
import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi

open Silmaril.SSA
open SeaOfNodes.Diamond SeaOfNodes.Diamond.AddPhi
open SeaOfNodes.Pure.ConstantFold
open SeaOfNodes.Pure.SubZero (Opcode model word wordPort)
open RVSDG (Locals Tuple extend)

theorem scan_agrees {args : List (Ty Unit)} {past sigs : List (List (Ty Unit))}
    (flow : Dataflow Opcode args past sigs) (known : Literals args past)
    (entry : Tuple (Val model.value) args) (locals : Locals (Val model.value) past)
    (agree : Scan.Literals.Agrees known entry locals) :
    Scan.Literals.Agrees (scanLiterals known flow) entry (flow.eval model entry locals) := by
  induction flow with
  | nil => exact agree
  | cons op operands rest ih =>
    apply ih
    apply Scan.Literals.push_agrees agree
    intro value found
    cases op <;> cases found
    cases operands
    rfl

theorem literalArm_eval {args : List (Ty Unit)} {past : List (List (Ty Unit))}
    (entry : Tuple (Val model.value) args) (locals : Locals (Val model.value) past) (value : BitVec 64) :
    (literalArm value).eval model entry locals = .cons value .nil := by
  exact congrArg (fun v : BitVec 64 => Tuple.cons (F := Val model.value) (t := wordPort) v .nil)
    (SeaOfNodes.GVN.read_newest (head := [wordPort]) .head model entry locals (.cons value .nil))

variable {inputs : List (ValueSort Unit)} {sigs : List (List (Ty Unit))}
variable {g : WordGraph inputs sigs} {rhs : WordWire inputs sigs} {target : Result inputs sigs}

private theorem accepted_eq (accepted : rewrite? g rhs = some target) :
    let known := scanLiterals (fun _ => none) g.dataflow
    ∃ first second right : BitVec 64,
      known (g.phi.operand .first) = some first ∧ known (g.phi.operand .second) = some second ∧
      known rhs = some right ∧ target = emit g first second right := by
  unfold rewrite? at accepted
  obtain ⟨first, firstEq, accepted⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨second, secondEq, accepted⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨right, rightEq, accepted⟩ := Option.bind_eq_some_iff.mp accepted
  split at accepted
  · contradiction
  · exact ⟨first, second, right, firstEq, secondEq, rightEq, (Option.some.inj accepted).symm⟩

theorem keeps_control (accepted : rewrite? g rhs = some target) :
    target.shared = g.dataflow ∧ target.predicate = g.predicate ∧ target.merge = g.phi.merge := by
  obtain ⟨first, second, right, _, _, _, rfl⟩ := accepted_eq accepted
  exact ⟨rfl, rfl, rfl⟩

theorem slot_eval_eq (accepted : rewrite? g rhs = some target)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (slot : Slot) :
    (target.arms slot).eval model entry (target.shared.eval model entry PUnit.unit) =
      .cons (sourceAt g rhs entry slot) .nil := by
  obtain ⟨first, second, right, hf, hs, hr, rfl⟩ := accepted_eq accepted
  have facts : Scan.Literals.Agrees (scanLiterals (fun _ => none) g.dataflow) entry
      (g.dataflow.eval model entry PUnit.unit) :=
    scan_agrees g.dataflow (fun _ => none) entry PUnit.unit (by intro _ _ _ h; contradiction)
  have readFirst := facts (g.phi.operand .first) hf
  have readSecond := facts (g.phi.operand .second) hs
  have readRight := facts rhs hr
  cases slot
  · simpa only [emit, sourceAt, readFirst, readRight] using
      literalArm_eval entry (g.dataflow.eval model entry PUnit.unit) (addWords first right)
  · simpa only [emit, sourceAt, readSecond, readRight] using
      literalArm_eval entry (g.dataflow.eval model entry PUnit.unit) (addWords second right)

theorem denote_eq (accepted : rewrite? g rhs = some target)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    target.denote model entry = .cons (sourceDenote g rhs entry) .nil := by
  obtain ⟨sharedEq, predicateEq, mergeEq⟩ := keeps_control accepted
  unfold Arms.Graph.denote sourceDenote Graph.denote
  rw [slot_eval_eq accepted, sharedEq, predicateEq, mergeEq]
  rfl

theorem returns_iff (accepted : rewrite? g rhs = some target)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (result : BitVec 64) :
    target.Returns model entry (.cons result .nil) ↔ SourceReturns g rhs entry result := by
  rw [Arms.Graph.returns_iff_denote, denote_eq accepted]
  change (Tuple.cons (F := Val model.value) (t := wordPort) (sourceDenote g rhs entry) .nil =
    .cons result .nil) ↔ _
  simp only [SourceReturns, Graph.returns_iff_denote]
  constructor
  · intro equal
    exact ⟨g.denote model entry, rfl, congrArg (fun row => row.get .head) equal⟩
  · rintro ⟨_, rfl, equal⟩
    exact congrArg (fun v : BitVec 64 => Tuple.cons (F := Val model.value) (t := wordPort) v .nil) equal

end Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi

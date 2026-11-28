module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Institution.Defs
public import Silmaril.Logic.Institution.Observational.Sentence
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Institution.Satisfaction

import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Thms

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Institution.Proofs

open CategoryTheory (Discrete)
open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy model word)
open Silmaril.SSA.SeaOfNodes
open Diamond.LambdaSSA (Atom inputEnv instruction instruction_deterministic)
open Diamond.LambdaSSA.Institution.Fiber (fiberRoom inputModel)
open Loop.LambdaSSA
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA.Semantics
open Silmaril.Isotope.Institution.Observational
  (Observation ssaBeh ret_mem_ssaBeh fault_mem_ssaBeh diverge_mem_ssaBeh scoped_eval_congr
    scoped_diverges_congr)
open Silmaril.Isotope.Morphism.SSAIter (envOfBound_agrees)
open Silmaril.Logic.Institution.Observational (Sentence)

variable {arity : Nat} {entrySigs sigs rightEntry rightSigs : List (List PortTy)}
variable {left : SourceWithEntry arity entrySigs sigs} {right : SourceWithEntry arity rightEntry rightSigs}
variable {leftTargets rightTargets : Checked.Phi.Targets}

theorem room_ret_iff (accepted : lowerChecked left = some leftTargets)
    (input : WordTuple arity) (initial final : Memory) (label : Nat) (payload : Value (Atom model)) :
    Observation.ret initial (label, payload) final ∈
      ssaBeh 1 (inputModel (P := Rows.wordSignature) model Memory input) (scope accepted) ↔
    ∃ value : Word, value ∈ left.denote model input ∧ label = 0 ∧
      payload = Generic.packResult model (out := word) value ∧ final = initial := by
  let M := inputModel (P := Rows.wordSignature) model Memory input
  refine ret_mem_ssaBeh.trans ((scoped_eval_congr (scope accepted).property
    (envOfBound_agrees M.bound) (fun _ => rfl)).trans ?_)
  exact (lambda_return_iff accepted input initial final label payload).trans
    (exists_congr fun value => and_congr (left.returns_iff_mem_denote model input value) Iff.rfl)

theorem room_fault_absent (accepted : lowerChecked left = some leftTargets)
    (input : WordTuple arity) (initial final : Memory) :
    Observation.fault initial final ∉
      ssaBeh 1 (inputModel (P := Rows.wordSignature) model Memory input) (scope accepted) :=
  fun member => (fault_mem_ssaBeh.mp member).false

theorem room_diverges_iff (accepted : lowerChecked left = some leftTargets)
    (input : WordTuple arity) (initial : Memory) :
    Observation.diverge initial ∈
      ssaBeh 1 (inputModel (P := Rows.wordSignature) model Memory input) (scope accepted) ↔
    left.denote model input = Part.none := by
  constructor
  · intro diverged
    apply Part.eq_none_iff'.mpr
    intro defined
    obtain ⟨value, present⟩ := Part.dom_iff_mem.mp defined
    have returned := (room_ret_iff accepted input initial initial 0
      (Generic.packResult model (out := word) value)).mpr ⟨value, present, rfl, rfl, rfl⟩
    exact (ret_mem_ssaBeh.mp returned).not_diverges (instruction_deterministic model)
      (External.Diverges.false_iff.mp (diverge_mem_ssaBeh.mp diverged))
  · intro absent
    obtain ⟨_, _, _, same⟩ := lowerChecked_sound accepted
    let M := inputModel (P := Rows.wordSignature) model Memory input
    apply diverge_mem_ssaBeh.mpr
    apply (scoped_diverges_congr (scope accepted).property
      (envOfBound_agrees M.bound) (fun _ => rfl)).mpr
    change External.Diverges (instruction model) (fun _ _ _ => False)
      (.region (inputEnv model input) leftTargets.2 initial)
    rw [same]
    exact External.Diverges.of_internal (Width.lower_diverges_of_absent left input initial absent)

theorem room_equation_at_iff (leftChecked : lowerChecked left = some leftTargets)
    (rightChecked : lowerChecked right = some rightTargets) (input : WordTuple arity) (initial : Memory) :
    (fiberRoom Rows.wordSignature (wordSorts arity).length).Sat
      (Discrete.mk (inputModel (P := Rows.wordSignature) model Memory input))
      (Sentence.eq (scope leftChecked) (scope rightChecked)) ↔ left.denote model input = right.denote model input := by
  let M := inputModel (P := Rows.wordSignature) model Memory input
  change ssaBeh 1 M (scope leftChecked) = ssaBeh 1 M (scope rightChecked) ↔ _
  constructor
  · intro agree
    have project : lambdaReturns input initial (scope leftChecked) = lambdaReturns input initial (scope rightChecked) := by
      ext ⟨value, final⟩
      exact Set.ext_iff.mp agree
        (Observation.ret initial (0, Generic.packResult model (out := word) value) final)
    exact (equation_at_iff leftChecked rightChecked input initial).2.1.mp project
  · intro agree
    apply Observation.set_eq_iff.mpr
    refine ⟨?_, fun start finish => iff_of_false (room_fault_absent leftChecked input start finish)
      (room_fault_absent rightChecked input start finish), fun start => ?_⟩
    · rintro start ⟨label, payload⟩ finish
      refine (room_ret_iff leftChecked input start finish label payload).trans
        (Iff.trans ?_ (room_ret_iff rightChecked input start finish label payload).symm)
      rw [agree]
    · refine (room_diverges_iff leftChecked input start).trans
        (Iff.trans ?_ (room_diverges_iff rightChecked input start).symm)
      rw [agree]

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Institution.Proofs

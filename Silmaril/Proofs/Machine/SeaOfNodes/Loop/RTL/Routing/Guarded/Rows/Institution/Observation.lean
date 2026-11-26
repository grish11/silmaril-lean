module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Institution.Defs
public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Fuel.Thms
public import Silmaril.SSA.SeaOfNodes.Loop.Institution.Thms

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Proofs.Institution

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (model word)
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA (Atom inputEnv instruction)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA.Semantics.Region (Eval)

variable {arity : Nat} {p : Plan arity} {spec : Spec} {targets : Checked.Phi.Targets}

private theorem checked_targets (plan : checkPlan arity spec = some p)
    (lowered : lowerChecked arity spec = some targets) :
    targets = (lowerBank p.graph, Generic.lower p.graph) := by
  obtain ⟨checked, same, _, emitted⟩ := (lowerChecked_eq_some_iff arity spec targets).mp lowered
  cases plan.symm.trans same
  exact emitted

theorem rtl_return_iff (plan : checkPlan arity spec = some p)
    (lowered : lowerChecked arity spec = some targets) (input : WordTuple arity)
    (initial final : Memory) (returned : List Word) :
    targets.1.oracle 0 (words input) initial returned final ↔
      ∃ value, value ∈ p.program.graph.denote model input ∧ returned = [value] ∧ final = initial := by
  rw [checked_targets plan lowered]
  exact (rtl_returns_iff p input initial final returned).trans
    (exists_congr fun value => and_congr (p.graph.returns_iff_mem_denote model input value) Iff.rfl)

theorem lambda_return_iff (plan : checkPlan arity spec = some p)
    (lowered : lowerChecked arity spec = some targets) (input : WordTuple arity)
    (initial final : Memory) (label : Nat) (payload : Value (Atom model)) :
    Eval (instruction model) (inputEnv model input) targets.2 initial label payload final ↔
      ∃ value, value ∈ p.program.graph.denote model input ∧ label = 0 ∧
        payload = Generic.packResult model (out := word) value ∧ final = initial := by
  rw [checked_targets plan lowered]
  simpa only [Plan.program, p.graph.returns_iff_mem_denote] using
    Generic.lower_eval_iff p.graph model input initial final label payload

theorem observations_eq (plan : checkPlan arity spec = some p)
    (lowered : lowerChecked arity spec = some targets) (input : WordTuple arity) (initial : Memory) :
    (rtlObservation targets.1 input initial =
      { result | result.1 ∈ p.program.graph.denote model input ∧ result.2 = initial }) ∧
    (lambdaObservation targets.2 input initial =
      { result | result.1 ∈ p.program.graph.denote model input ∧ result.2 = initial }) := by
  constructor
  · ext ⟨value, final⟩
    change targets.1.oracle 0 (words input) initial [value] final ↔
      value ∈ p.program.graph.denote model input ∧ final = initial
    rw [rtl_return_iff plan lowered]
    constructor
    · rintro ⟨out, returns, same, memory⟩
      obtain ⟨rfl, _⟩ := List.cons.inj same
      exact ⟨returns, memory⟩
    · rintro ⟨returns, memory⟩
      exact ⟨value, returns, rfl, memory⟩
  · rw [checked_targets plan lowered]
    ext ⟨value, final⟩
    change Eval (instruction model) (inputEnv model input) (Generic.lower p.graph)
        initial 0 (Generic.packResult model (out := word) value) final ↔
      value ∈ p.graph.denote model input ∧ final = initial
    constructor
    · intro eval
      obtain ⟨_, _, _, _, memory⟩ :=
        (Generic.lower_eval_iff p.graph model input _ _ _ _).mp eval
      subst final
      exact ⟨(Generic.mem_denote_iff p.graph model input initial value).mpr eval, rfl⟩
    · rintro ⟨returns, memory⟩
      subst final
      exact (Generic.mem_denote_iff p.graph model input initial value).mp returns

theorem no_finite_return_iff (plan : checkPlan arity spec = some p)
    (lowered : lowerChecked arity spec = some targets) (input : WordTuple arity) (initial : Memory) :
    ((∀ returned final, ¬ targets.1.oracle 0 (words input) initial returned final) ↔
        p.program.graph.denote model input = Part.none) ∧
    ((∀ label payload final, ¬ Eval (instruction model) (inputEnv model input)
        targets.2 initial label payload final) ↔ p.program.graph.denote model input = Part.none) := by
  simp only [Part.eq_none_iff', Part.dom_iff_mem]
  constructor
  · constructor
    · rintro absent ⟨value, present⟩
      exact absent [value] initial ((rtl_return_iff plan lowered input initial initial [value]).mpr
        ⟨value, present, rfl, rfl⟩)
    · intro absent returned final run
      obtain ⟨value, present, _, _⟩ := (rtl_return_iff plan lowered input initial final returned).mp run
      exact absent ⟨value, present⟩
  · constructor
    · rintro absent ⟨value, present⟩
      exact absent 0 _ initial ((lambda_return_iff plan lowered input initial initial 0 _).mpr
        ⟨value, present, rfl, rfl, rfl⟩)
    · intro absent label payload final eval
      obtain ⟨value, present, _, _, _⟩ :=
        (lambda_return_iff plan lowered input initial final label payload).mp eval
      exact absent ⟨value, present⟩

theorem equation_at_iff {left right : Plan arity} {leftSpec rightSpec : Spec}
    {leftTargets rightTargets : Checked.Phi.Targets}
    (leftPlan : checkPlan arity leftSpec = some left) (rightPlan : checkPlan arity rightSpec = some right)
    (leftLower : lowerChecked arity leftSpec = some leftTargets)
    (rightLower : lowerChecked arity rightSpec = some rightTargets)
    (input : WordTuple arity) (initial : Memory) :
    rtlObservation leftTargets.1 input initial = lambdaObservation rightTargets.2 input initial ↔
      left.program.graph.denote model input = right.program.graph.denote model input := by
  rw [(observations_eq leftPlan leftLower input initial).1,
    (observations_eq rightPlan rightLower input initial).2]
  constructor
  · intro same
    apply Part.ext
    intro value
    simpa only [Set.mem_ofPred_eq, and_true] using (Set.ext_iff.mp same) (value, initial)
  · intro same
    rw [same]

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Proofs.Institution

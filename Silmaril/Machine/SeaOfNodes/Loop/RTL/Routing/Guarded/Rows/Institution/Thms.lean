module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Institution.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.Institution.Thms
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Institution.Observation

/-! Pointwise preservation and reflection of native partial loop equations. -/

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (model word)
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA (Atom inputEnv instruction)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA.Semantics.Region (Eval)

variable {arity : Nat} {p : Plan arity} {spec : Spec} {targets : Checked.Phi.Targets}

/-- Every finite machine return has one word and preserves the whole memory. -/
theorem rtl_return_iff (plan : checkPlan arity spec = some p)
    (lowered : lowerChecked arity spec = some targets) (input : WordTuple arity)
    (initial final : Memory) (returned : List Word) :
    targets.1.oracle 0 (words input) initial returned final ↔
      ∃ value, value ∈ p.program.graph.denote model input ∧ returned = [value] ∧ final = initial :=
  Proofs.Institution.rtl_return_iff plan lowered input initial final returned

/-- Every finite CFG return has the packed source result at label zero and
preserves the whole memory. -/
theorem lambda_return_iff (plan : checkPlan arity spec = some p)
    (lowered : lowerChecked arity spec = some targets) (input : WordTuple arity)
    (initial final : Memory) (label : Nat) (payload : Value (Atom model)) :
    Eval (instruction model) (inputEnv model input) targets.2 initial label payload final ↔
      ∃ value, value ∈ p.program.graph.denote model input ∧ label = 0 ∧
        payload = Generic.packResult model (out := word) value ∧ final = initial :=
  Proofs.Institution.lambda_return_iff plan lowered input initial final label payload

/-- Both operational observations recover the native partial value with
the initial memory attached as the entire final memory. -/
theorem observations_eq (plan : checkPlan arity spec = some p)
    (lowered : lowerChecked arity spec = some targets) (input : WordTuple arity) (initial : Memory) :
    (rtlObservation targets.1 input initial =
      { result | result.1 ∈ p.program.graph.denote model input ∧ result.2 = initial }) ∧
    (lambdaObservation targets.2 input initial =
      { result | result.1 ∈ p.program.graph.denote model input ∧ result.2 = initial }) :=
  Proofs.Institution.observations_eq plan lowered input initial

/-- An undefined native observation excludes every finite return from
either target, with no fuel bound. -/
theorem no_finite_return_iff (plan : checkPlan arity spec = some p)
    (lowered : lowerChecked arity spec = some targets) (input : WordTuple arity) (initial : Memory) :
    ((∀ returned final, ¬ targets.1.oracle 0 (words input) initial returned final) ↔
        p.program.graph.denote model input = Part.none) ∧
    ((∀ label payload final, ¬ Eval (instruction model) (inputEnv model input)
        targets.2 initial label payload final) ↔ p.program.graph.denote model input = Part.none) :=
  Proofs.Institution.no_finite_return_iff plan lowered input initial

/-- Compare the left machine and right CFG at one native valuation and any
common initial memory. Their return sets agree exactly when the native
partial values agree. -/
theorem equation_at_iff {left right : Plan arity} {leftSpec rightSpec : Spec}
    {leftTargets rightTargets : Checked.Phi.Targets}
    (leftPlan : checkPlan arity leftSpec = some left) (rightPlan : checkPlan arity rightSpec = some right)
    (leftLower : lowerChecked arity leftSpec = some leftTargets)
    (rightLower : lowerChecked arity rightSpec = some rightTargets)
    (input : WordTuple arity) (initial : Memory) :
    rtlObservation leftTargets.1 input initial = lambdaObservation rightTargets.2 input initial ↔
      left.program.graph.denote model input = right.program.graph.denote model input :=
  Proofs.Institution.equation_at_iff leftPlan rightPlan leftLower rightLower input initial

/-- Satisfaction in the existing native loop model is equality of the
two operational observations at every native valuation. -/
theorem equation_holds_iff {left right : Plan arity} {leftSpec rightSpec : Spec}
    {leftTargets rightTargets : Checked.Phi.Targets}
    (leftPlan : checkPlan arity leftSpec = some left) (rightPlan : checkPlan arity rightSpec = some right)
    (leftLower : lowerChecked arity leftSpec = some leftTargets)
    (rightLower : lowerChecked arity rightSpec = some rightTargets) (initial : Memory) :
    (left.equation right).Holds model ↔
      ∀ input : WordTuple arity,
        rtlObservation leftTargets.1 input initial = lambdaObservation rightTargets.2 input initial :=
  forall_congr' fun input => (equation_at_iff leftPlan rightPlan leftLower rightLower input initial).symm

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows

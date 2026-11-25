module

public import Silmaril.Logic.Temporal.TLA.Kernel.Defs
import Silmaril.Proofs.Logic.Temporal.TLA.Kernel.Bounded

public section

namespace Silmaril.Logic.Temporal.TLA.Kernel

variable {Γ : Scope} {Input Node X : Type}

theorem Predicate.check_iff (p : Predicate Γ Input) (ρ : RigidEnv Γ) (input : Input) :
    p.check ρ input = true ↔ p.holds ρ input :=
  @decide_eq_true_iff _ (p.decision ρ input)

/-- A bounded step quantifier is a General TLA rigid existential with a
membership guard. -/
theorem Predicate.existsIn_toAction {a : Scalar} (domain : StepExpr Γ (List (Value a)))
    (body : StepPredicate (Γ.bindRigid a)) :
    (existsIn domain body).toAction =
      General.Action.existsRigid (fun ρ s t =>
        ρ.last ∈ domain ρ.drop (s, t) ∧ body.toAction ρ s t) :=
  rfl

theorem Predicate.bracket_toAction [DecidableEq X] (p : StepPredicate Γ)
    (observe : StateExpr Γ X) (ρ : RigidEnv Γ) :
    (p.bracket observe).toAction ρ = (p.toAction ρ).bracket (observe ρ) :=
  rfl

/-- An injective observation adds precisely whole-state stuttering. -/
theorem Predicate.bracket_full [DecidableEq X] (p : StepPredicate Γ)
    (observe : StateExpr Γ X) (ρ : RigidEnv Γ) (s t : State Γ)
    (injective : ∀ ⦃s t⦄, observe ρ s = observe ρ t → s = t) :
    (p.bracket observe).toAction ρ s t ↔ p.toAction ρ s t ∨ s = t := by
  change p.toAction ρ s t ∨ observe ρ t = observe ρ s ↔ p.toAction ρ s t ∨ s = t
  exact or_congr Iff.rfl ⟨fun h => injective h.symm, fun h => congrArg (observe ρ) h.symm⟩

/-- The bounded view includes exactly the listed states satisfying initialization. -/
theorem Bounded.mem_initials (domain : Bounded Γ Node) (ρ : RigidEnv Γ)
    (init : StatePredicate Γ) (node : Node) :
    node ∈ domain.initials ρ init ↔
      node ∈ domain.states ∧ init.toStatePred.eval ρ (domain.valuation node) := by
  rw [Bounded.initials, List.mem_filter]
  exact and_congr Iff.rfl (init.check_iff ρ _)

/-- The bounded view includes exactly the listed endpoint pairs satisfying the
supplied General TLA action. -/
theorem Bounded.mem_transitions (domain : Bounded Γ Node) (ρ : RigidEnv Γ)
    (step : StepPredicate Γ) (src dst : Node) :
    (src, dst) ∈ domain.transitions ρ step ↔
      src ∈ domain.states ∧ dst ∈ domain.states ∧
        step.toAction ρ (domain.valuation src) (domain.valuation dst) :=
  Proofs.Logic.Temporal.TLA.Kernel.mem_transitions domain ρ step src dst

end Silmaril.Logic.Temporal.TLA.Kernel

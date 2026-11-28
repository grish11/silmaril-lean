module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.Soundness
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Initial.Defs

/-! # Evaluation of constructor-sequenced returns -/

@[expose] public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.Observer

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.RetainedLet (returnOnce)
open Paper.UnaryReturn.Beta.Constructors
open Silmaril.Isotope.LambdaSSA.Semantics (extend)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Observer
  (UnitPayloadPolicy Env EnvTy Val ValTy Result)
open scoped Paper.BoundSimulation.Obstruction

universe u v

variable {α : Type u} {Φ : Type v} [HasTy Φ (Ty α)]

local notation "plain" => ({} : TermObservation (α := α) Φ)

theorem sequence_pair_of_guard {observation : TermObservation (α := α) Φ} (a b : Tm Φ)
    (unmarked : (observation.pairLet && selectsPair observation.pairLetCall a &&
      (startsLet a || startsLet b)) = false) (unmarkedLet : observation.boundUnaryLet = false) (env : Env) :
    evalRegionWith observation (returnOnce (.pair a b)) env =
      evalRegionWith observation (pairSequence a b) env := by
  simp only [returnOnce, pairSequence, evalRegionWith, evalTermWith,
    unmarked, unmarkedLet, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  cases evalTermWith observation a env with
  | none => rfl
  | some v =>
    simp only [evalTerm_rename b (observation := observation) (env := env)
      (env' := extend env v) (ρ := Nat.succ) (fun _ => rfl)]
    cases evalTermWith observation b env <;> simp [startsLet, extend]

theorem sequence_pair {observation : TermObservation (α := α) Φ} (unmarked : observation.pairLet = false)
    (unmarkedLet : observation.boundUnaryLet = false) (a b : Tm Φ) (env : Env) :
    evalRegionWith observation (returnOnce (.pair a b)) env =
      evalRegionWith observation (pairSequence a b) env :=
  sequence_pair_of_guard a b (by simp only [unmarked, Bool.false_and]) unmarkedLet env

private theorem sequence_inl (observation : TermObservation (α := α) Φ)
    (unmarkedLet : observation.boundUnaryLet = false) (a : Tm Φ) (env : Env) :
    evalRegionWith observation (returnOnce (.inl a)) env =
      evalRegionWith observation (inlSequence a) env := by
  simp only [returnOnce, inlSequence, evalRegionWith, evalTermWith, unmarkedLet, Bool.and_false, Bool.false_eq_true, ite_false]
  cases evalTermWith observation a env <;> rfl

private theorem sequence_inr (observation : TermObservation (α := α) Φ)
    (unmarkedLet : observation.boundUnaryLet = false) (a : Tm Φ) (env : Env) :
    evalRegionWith observation (returnOnce (.inr a)) env =
      evalRegionWith observation (inrSequence a) env := by
  simp only [returnOnce, inrSequence, evalRegionWith, evalTermWith, unmarkedLet, Bool.and_false, Bool.false_eq_true, ite_false]
  cases evalTermWith observation a env <;> rfl

section

set_option linter.concreteInstances false

variable [UnitPayloadPolicy]

/-- Pair observations may inspect computed operands if they leave every
pair with a constructor-normalizing left operand unmarked. -/
theorem constructorStep_same_of_guard {observation : TermObservation (α := α) Φ}
    (unmarked : ∀ {Γ : VCtx (Ty α)} {a v : Tm Φ} {A : Ty α}, Normalizes Γ a v A → ∀ (b : Tm Φ),
      (observation.pairLet && selectsPair observation.pairLetCall a &&
        (startsLet a || startsLet b)) = false)
    (unmarkedLet : observation.boundUnaryLet = false)
    {Γ L : List (Ty α)} {r s : Region Φ} (h : Paper.WithConstructorSequencing.Step Γ r s L) :
    SameWith observation Γ r s := by
  cases h with
  | pair ha hb => exact fun env _ => sequence_pair_of_guard _ _ (unmarked ha _) unmarkedLet env
  | inl ha => exact fun env _ => sequence_inl observation unmarkedLet _ env
  | inr ha => exact fun env _ => sequence_inr observation unmarkedLet _ env

/-- The sequencing generators preserve observations that leave pair assembly
unmarked. The common operand observations can still inspect calls. -/
theorem constructorStep_same {observation : TermObservation (α := α) Φ}
    (unmarked : observation.pairLet = false) (unmarkedLet : observation.boundUnaryLet = false)
    {Γ L : List (Ty α)} {r s : Region Φ} (h : Paper.WithConstructorSequencing.Step Γ r s L) :
    SameWith observation Γ r s :=
  constructorStep_same_of_guard (fun _ _ => by simp only [unmarked, Bool.false_and]) unmarkedLet h

/-- Opt-in constructor sequencing preserves the unmarked observation. -/
theorem sequencing_same {Γ L : List (Ty α)} {r s : Region Φ}
    (h : Paper.WithConstructorSequencing.Eqv Γ r s L) : SameWith {} Γ r s :=
  extension_same (observation := plain)
    (fun e => Or.elim e (unary_fusion_same rfl) (constructorStep_same rfl rfl)) h

end

open scoped Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Observer.AlternateUnit

private theorem value_or_empty (P : Ty α) : (∃ v, ValTy v P) ∨ Paper.StructurallyEmpty P := by
  induction P with
  | base a => exact .inl ⟨.unit, .base⟩
  | unit => exact .inl ⟨.unit, .unit⟩
  | empty => exact .inr .empty
  | product A B ihA ihB =>
    rcases ihA with ⟨a, ha⟩ | hA
    · rcases ihB with ⟨b, hb⟩ | hB
      · exact .inl ⟨.pair a b, .pair ha hb⟩
      · exact .inr (.right hB)
    · exact .inr (.left hA)
  | coprod A B ihA ihB =>
    rcases ihA with ⟨a, ha⟩ | hA
    · exact .inl ⟨.inl a, .inl ha⟩
    · rcases ihB with ⟨b, hb⟩ | hB
      · exact .inl ⟨.inr b, .inr hb⟩
      · exact .inr (.sum hA hB)

theorem structurallyEmpty_of_tagged_branches_eq (P : Ty α)
    (h : Paper.WithConstructorSequencing.Eqv [P] (.br 0 (.inl (.var 0)) : Region Φ)
      (.br 0 (.inr (.var 0))) [.coprod P P]) : Paper.StructurallyEmpty P := by
  rcases value_or_empty P with ⟨v, hv⟩ | hEmpty
  · have env : EnvTy [P] (fun _ => v) := by
      intro i A hi
      cases i with
      | zero => cases Option.some.inj hi; exact hv
      | succ i => cases i <;> contradiction
    have observed := sequencing_same h (fun _ => v) env
    change Result.jump 0 (.inl v) = Result.jump 0 (.inr v) at observed
    cases observed
  · exact hEmpty

omit [HasTy Φ (Ty α)] in
private theorem closed_has_distinct_values {Γ : VCtx (Ty α)} {w : Tm Φ} {P : Ty α}
    (hw : Tm.BranchValue Γ w P) (emptyCtx : Γ = []) :
    ∃ x y, ValTy x P ∧ ValTy y P ∧ x ≠ y := by
  induction hw with
  | var hi => subst Γ; cases hi
  | unit => exact ⟨.unit, .inl .unit, .unit, .alternateUnit rfl, by intro eq; cases eq⟩
  | pair _ _ ihL ihR =>
    obtain ⟨x, y, hx, hy, ne⟩ := ihL
    obtain ⟨z, _, hz, _, _⟩ := ihR
    exact ⟨.pair x z, .pair y z, .pair hx hz, .pair hy hz, fun eq => ne (Value.pair.inj eq).1⟩
  | inl _ ih =>
    obtain ⟨x, y, hx, hy, ne⟩ := ih
    exact ⟨.inl x, .inl y, .inl hx, .inl hy, fun eq => ne (Value.inl.inj eq)⟩
  | inr _ ih =>
    obtain ⟨x, y, hx, hy, ne⟩ := ih
    exact ⟨.inr x, .inr y, .inr hx, .inr hy, fun eq => ne (Value.inr.inj eq)⟩

private theorem eval_closed_independent {Γ : VCtx (Ty α)} {w : Tm Φ} {P : Ty α}
    (hw : Tm.BranchValue Γ w P) (emptyCtx : Γ = []) (env other : Env) :
    evalTermWith plain w env = evalTermWith plain w other := by
  induction hw with
  | var hi => subst Γ; cases hi
  | unit => rfl
  | pair _ _ ihL ihR => simp only [evalTermWith, ihL, ihR]
  | inl _ ih => simp only [evalTermWith, ih]
  | inr _ ih => simp only [evalTermWith, ih]

private theorem singleton_env {P : Ty α} {v : Val} (hv : ValTy v P) : EnvTy [P] (fun _ => v) := by
  intro i A hi
  cases i with
  | zero => cases Option.some.inj hi; exact hv
  | succ i => cases i <;> contradiction

theorem reset_ne_forward {P : Ty α} {w : Tm Φ} (hw : Tm.BranchValue [] w P) :
    ¬ Paper.WithConstructorSequencing.Eqv [P] (.br 0 w) (.br 0 (.var 0)) [P] := by
  intro h
  obtain ⟨x, y, hx, hy, ne⟩ := closed_has_distinct_values hw rfl
  have seen (v : Val) (hv : ValTy v P) : evalTermWith plain w (fun _ => v) = some v := by
    have e := sequencing_same h (fun _ => v) (singleton_env hv)
    cases run : evalTermWith plain w (fun _ => v) <;>
      simp_all only [evalRegionWith, evalTermWith, Result.jump.injEq, true_and]
    contradiction
  exact ne (Option.some.inj ((seen x hx).symm.trans ((eval_closed_independent hw rfl _ _).trans (seen y hy))))

theorem reset_left_ne_right {P : Ty α} {w : Tm Φ} (hw : Tm.BranchValue [] w P) :
    ¬ Paper.WithConstructorSequencing.Eqv [P] (.br 0 (.inl w)) (.br 0 (.inr w)) [.coprod P P] := by
  intro h
  obtain ⟨v, _, hv, _, _⟩ := closed_has_distinct_values hw rfl
  have e := sequencing_same h (fun _ => v) (singleton_env hv)
  have ctx : EnvTy ([] : VCtx (Ty α)) (fun _ => v) := fun _ _ hi => by cases hi
  obtain ⟨x, eval, _⟩ := evalValue (observation := plain) hw ctx
  simp only [evalRegionWith, evalTermWith, Bool.and_false, Bool.false_eq_true, ite_false,
    eval, Option.map_some, Result.jump.injEq, true_and] at e
  cases e

private def quote : Val → Tm Φ
  | .atom a => a.elim
  | .unit => .unit
  | .pair v w => .pair (quote v) (quote w)
  | .inl v => .inl (quote v)
  | .inr v => .inr (quote v)

private theorem eval_quote {Γ : VCtx (Ty α)} {t : Tm Φ} {A : Ty α}
    (ht : Tm.BranchValue Γ t A) (env : Env) :
    (evalTermWith plain t env).map quote = some (t.subst (quote ∘ env)) := by
  induction ht with
  | var _ => rfl
  | unit => rfl
  | pair _ _ ia ib =>
    obtain ⟨v, ev, hv⟩ := Option.map_eq_some_iff.mp ia
    obtain ⟨w, ew, hw⟩ := Option.map_eq_some_iff.mp ib
    simp [evalTermWith, ev, ew, quote, Tm.subst, hv, hw]
  | inl _ ih =>
    obtain ⟨v, ev, hv⟩ := Option.map_eq_some_iff.mp ih
    simp [evalTermWith, ev, quote, Tm.subst, hv]
  | inr _ ih =>
    obtain ⟨v, ev, hv⟩ := Option.map_eq_some_iff.mp ih
    simp [evalTermWith, ev, quote, Tm.subst, hv]

omit [HasTy Φ (Ty α)] in
private theorem closed_subst {Γ : VCtx (Ty α)} {t : Tm Φ} {A : Ty α}
    (ht : Tm.BranchValue Γ t A) (hΓ : Γ = []) (θ : Nat → Tm Φ) : t.subst θ = t := by
  induction ht with
  | var hi => subst Γ; cases hi
  | unit => rfl
  | pair _ _ ia ib => simp only [Tm.subst, ia, ib]
  | inl _ ih => simp only [Tm.subst, ih]
  | inr _ ih => simp only [Tm.subst, ih]

private theorem singleton_branch_observation {P : Ty α} {Γ Δ : VCtx (Ty α)} {t u : Tm Φ} {A : Ty α}
    (ht : Tm.BranchValue Γ t A) (hu : Tm.BranchValue Δ u A)
    (h : Paper.WithConstructorSequencing.Eqv [P] (.br 0 t) (.br 0 u) [A])
    (v : Val) (hv : ValTy v P) :
    t.subst (fun _ => quote v) = u.subst (fun _ => quote v) := by
  have observed := sequencing_same h (fun _ => v) (singleton_env hv)
  obtain ⟨x, ex, hx⟩ := Option.map_eq_some_iff.mp (eval_quote ht (fun _ => v))
  obtain ⟨y, ey, hy⟩ := Option.map_eq_some_iff.mp (eval_quote hu (fun _ => v))
  simp only [evalRegionWith, ex, ey, Result.jump.injEq, true_and] at observed
  exact hx.symm.trans (observed ▸ hy)


theorem closed_resets_injective {P : Ty α} {x y : Tm Φ}
    (hx : Tm.BranchValue [] x P) (hy : Tm.BranchValue [] y P)
    (h : Paper.WithConstructorSequencing.Eqv [P] (.br 0 x) (.br 0 y) [P]) : x = y := by
  have env : EnvTy ([] : VCtx (Ty α)) (fun _ => .unit) := fun _ _ hi => by cases hi
  obtain ⟨v, _, hv⟩ := evalValue (observation := plain) hx env
  simpa only [closed_subst hx rfl, closed_subst hy rfl] using singleton_branch_observation hx hy h v hv

theorem branch_observation_of_closed_input {t u w : Tm Empty} {A P : Ty Empty}
    (ht : Tm.BranchValue [P] t A) (hu : Tm.BranchValue [P] u A)
    (hw : Tm.BranchValue [] w P)
    (h : Paper.WithConstructorSequencing.Eqv [P] (.br 0 t) (.br 0 u) [A]) :
    t.subst (fun _ => w) = u.subst (fun _ => w) := by
  obtain ⟨v, he, hv⟩ := Option.map_eq_some_iff.mp (eval_quote hw (fun _ => .unit))
  have typed : ValTy v P := evalTerm_typed hw.hasType (fun _ _ hi => by cases hi) he
  rw [closed_subst hw rfl] at hv
  simpa only [hv] using singleton_branch_observation ht hu h v typed

theorem closed_branch_injective {t u : Tm Empty} {A : Ty Empty}
    (ht : Tm.BranchValue [] t A) (hu : Tm.BranchValue [] u A)
    (h : Paper.WithConstructorSequencing.Eqv [.unit] (.br 0 t) (.br 0 u) [A]) : t = u := by
  simpa only [closed_subst ht rfl, closed_subst hu rfl] using
    singleton_branch_observation ht hu h .unit .unit

theorem unit_branch_observations {t u : Tm Empty} {A : Ty Empty}
    (ht : Tm.BranchValue [.unit] t A) (hu : Tm.BranchValue [.unit] u A)
    (h : Paper.WithConstructorSequencing.Eqv [.unit] (.br 0 t) (.br 0 u) [A]) :
    t.subst (fun _ => .unit) = u.subst (fun _ => .unit) ∧
      t.subst (fun _ => .inl .unit) = u.subst (fun _ => .inl .unit) :=
  ⟨singleton_branch_observation ht hu h .unit .unit,
    singleton_branch_observation ht hu h (.inl .unit) (.alternateUnit rfl)⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.Observer

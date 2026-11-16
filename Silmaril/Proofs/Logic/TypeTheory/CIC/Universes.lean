module

public import Silmaril.Logic.TypeTheory.CIC.Universes.Defs
import Mathlib.Tactic

public section

namespace Silmaril.Proofs.Logic.TypeTheory.CIC

open Silmaril.Logic.TypeTheory.CIC

universe u v w

namespace UniverseExprLaws

@[simp] theorem subst_level {Level : Type u} (u : UniverseExpr Level) :
    u.subst .level = u := by
  induction u <;> simp_all [UniverseExpr.subst]

@[simp] theorem eval_subst {Level : Type u} {Level' : Type v}
    (σ : Level → UniverseExpr Level') (ρ : Level' → ℕ) (u : UniverseExpr Level) :
    (u.subst σ).eval ρ = u.eval (fun l => (σ l).eval ρ) := by
  induction u <;> simp_all [UniverseExpr.subst, UniverseExpr.eval]

theorem subst_comp {Level : Type u} {Level' : Type v} {Level'' : Type w}
    (σ : Level → UniverseExpr Level') (τ : Level' → UniverseExpr Level'')
    (u : UniverseExpr Level) :
    (u.subst σ).subst τ = u.subst (fun l => (σ l).subst τ) := by
  induction u <;> simp_all [UniverseExpr.subst]

@[simp] theorem rename_id {Level : Type u} (u : UniverseExpr Level) :
    u.rename id = u := by
  simpa only [UniverseExpr.rename, Function.comp_id] using subst_level u

theorem rename_comp {Level : Type u} {Level' : Type v} {Level'' : Type w}
    (f : Level → Level') (g : Level' → Level'') (u : UniverseExpr Level) :
    (u.rename f).rename g = u.rename (g ∘ f) := by
  simpa only [UniverseExpr.rename, Function.comp_def, UniverseExpr.subst]
    using subst_comp (.level ∘ f) (.level ∘ g) u

@[simp] theorem eval_rename {Level : Type u} {Level' : Type v}
    (f : Level → Level') (ρ : Level' → ℕ) (u : UniverseExpr Level) :
    (u.rename f).eval ρ = u.eval (ρ ∘ f) := by
  simpa only [UniverseExpr.rename, Function.comp_def, UniverseExpr.eval]
    using eval_subst (.level ∘ f) ρ u

theorem usesBelow_mono {Level : Type u} {ρ : Level → ℕ} {n m : ℕ}
    {u : UniverseExpr Level} (hu : u.UsesBelow ρ n) (hnm : n ≤ m) :
    u.UsesBelow ρ m := lt_of_lt_of_le hu hnm

theorem ground_bound_iff (u : UniverseExpr ℕ) (n : ℕ) :
    u.UsesBelow id n ↔ u.universeBound ≤ n := by
  simp only [UniverseExpr.UsesBelow, UniverseExpr.universeBound]
  omega

end UniverseExprLaws

namespace SortExprLaws

theorem cumul_refl {Level : Type u} (ρ : Level → ℕ) (s : SortExpr Level) :
    s.Cumul ρ s := by
  cases s <;> simp [SortExpr.Cumul]

theorem cumul_trans {Level : Type u} {ρ : Level → ℕ} {a b c : SortExpr Level}
    (hab : a.Cumul ρ b) (hbc : b.Cumul ρ c) : a.Cumul ρ c := by
  cases a <;> cases b <;> cases c <;> simp_all [SortExpr.Cumul]
  exact hab.trans hbc

theorem product_usesBelow {Level : Type u} {ρ : Level → ℕ} {n : ℕ}
    {a b : SortExpr Level} (ha : a.UsesBelow ρ n) (hb : b.UsesBelow ρ n) :
    (a.product b).UsesBelow ρ n := by
  cases a <;> cases b <;>
    simp_all [SortExpr.product, SortExpr.sup, SortExpr.UsesBelow,
      UniverseExpr.UsesBelow, UniverseExpr.eval]

theorem super_usesBelow {Level : Type u} {ρ : Level → ℕ} {n : ℕ}
    {s : SortExpr Level} (hn : 1 ≤ n) (hs : s.UsesBelow ρ n) :
    s.super.UsesBelow ρ (n + 1) := by
  cases s <;>
    simp_all only [SortExpr.super, SortExpr.UsesBelow,
      UniverseExpr.UsesBelow, UniverseExpr.eval]
  all_goals omega

theorem usesBelow_mono {Level : Type u} {ρ : Level → ℕ} {n m : ℕ}
    {s : SortExpr Level} (hs : s.UsesBelow ρ n) (hnm : n ≤ m) :
    s.UsesBelow ρ m := by
  cases s with
  | prop | sprop => trivial
  | type u => exact UniverseExprLaws.usesBelow_mono hs hnm

theorem ground_bound_iff (s : SortExpr ℕ) (n : ℕ) :
    s.UsesBelow id n ↔ s.universeBound ≤ n := by
  cases s with
  | prop | sprop => simp only [SortExpr.UsesBelow, SortExpr.universeBound, Nat.zero_le]
  | type u => exact UniverseExprLaws.ground_bound_iff u n

end SortExprLaws

end Silmaril.Proofs.Logic.TypeTheory.CIC

module

public import Silmaril.Logic.TypeTheory.CIC.Universes.Defs
public import Silmaril.Proofs.Logic.TypeTheory.CIC.Universes

@[expose] public section

/-! # Laws of the CIC universe and sort layer -/

namespace Silmaril.Logic.TypeTheory.CIC

universe u v w

namespace UniverseExpr

@[simp] theorem subst_level {Level : Type u} (a : UniverseExpr Level) :
    a.subst .level = a :=
  Silmaril.Proofs.Logic.TypeTheory.CIC.UniverseExprLaws.subst_level a

@[simp] theorem eval_subst {Level : Type u} {Level' : Type v}
    (σ : Level → UniverseExpr Level') (ρ : Level' → ℕ) (a : UniverseExpr Level) :
    (a.subst σ).eval ρ = a.eval (fun l => (σ l).eval ρ) :=
  Silmaril.Proofs.Logic.TypeTheory.CIC.UniverseExprLaws.eval_subst σ ρ a

theorem subst_comp {Level : Type u} {Level' : Type v} {Level'' : Type w}
    (σ : Level → UniverseExpr Level') (τ : Level' → UniverseExpr Level'')
    (a : UniverseExpr Level) :
    (a.subst σ).subst τ = a.subst (fun l => (σ l).subst τ) :=
  Silmaril.Proofs.Logic.TypeTheory.CIC.UniverseExprLaws.subst_comp σ τ a

@[simp] theorem rename_id {Level : Type u} (a : UniverseExpr Level) : a.rename id = a :=
  Silmaril.Proofs.Logic.TypeTheory.CIC.UniverseExprLaws.rename_id a

theorem rename_comp {Level : Type u} {Level' : Type v} {Level'' : Type w}
    (f : Level → Level') (g : Level' → Level'') (a : UniverseExpr Level) :
    (a.rename f).rename g = a.rename (g ∘ f) :=
  Silmaril.Proofs.Logic.TypeTheory.CIC.UniverseExprLaws.rename_comp f g a

@[simp] theorem eval_rename {Level : Type u} {Level' : Type v}
    (f : Level → Level') (ρ : Level' → ℕ) (a : UniverseExpr Level) :
    (a.rename f).eval ρ = a.eval (ρ ∘ f) :=
  Silmaril.Proofs.Logic.TypeTheory.CIC.UniverseExprLaws.eval_rename f ρ a

theorem usesBelow_mono {Level : Type u} {ρ : Level → ℕ} {n m : ℕ}
    {a : UniverseExpr Level} (ha : a.UsesBelow ρ n) (hnm : n ≤ m) : a.UsesBelow ρ m :=
  Silmaril.Proofs.Logic.TypeTheory.CIC.UniverseExprLaws.usesBelow_mono ha hnm

/-- A finite supply counts numeric levels, including the highest level used. -/
theorem ground_bound_iff (a : UniverseExpr ℕ) (n : ℕ) :
    a.UsesBelow id n ↔ a.universeBound ≤ n :=
  Silmaril.Proofs.Logic.TypeTheory.CIC.UniverseExprLaws.ground_bound_iff a n

end UniverseExpr

namespace SortExpr

theorem cumul_refl {Level : Type u} (ρ : Level → ℕ) (s : SortExpr Level) : s.Cumul ρ s :=
  Silmaril.Proofs.Logic.TypeTheory.CIC.SortExprLaws.cumul_refl ρ s

theorem cumul_trans {Level : Type u} {ρ : Level → ℕ} {a b c : SortExpr Level}
    (hab : a.Cumul ρ b) (hbc : b.Cumul ρ c) : a.Cumul ρ c :=
  Silmaril.Proofs.Logic.TypeTheory.CIC.SortExprLaws.cumul_trans hab hbc

/-- Product formation stays within a common finite universe supply. -/
theorem product_usesBelow {Level : Type u} {ρ : Level → ℕ} {n : ℕ}
    {a b : SortExpr Level} (ha : a.UsesBelow ρ n) (hb : b.UsesBelow ρ n) :
    (a.product b).UsesBelow ρ n :=
  Silmaril.Proofs.Logic.TypeTheory.CIC.SortExprLaws.product_usesBelow ha hb

/-- Typing a sort consumes one further level; Prop and SProp require Type 1. -/
theorem super_usesBelow {Level : Type u} {ρ : Level → ℕ} {n : ℕ}
    {s : SortExpr Level} (hn : 1 ≤ n) (hs : s.UsesBelow ρ n) :
    s.super.UsesBelow ρ (n + 1) :=
  Silmaril.Proofs.Logic.TypeTheory.CIC.SortExprLaws.super_usesBelow hn hs

theorem usesBelow_mono {Level : Type u} {ρ : Level → ℕ} {n m : ℕ}
    {s : SortExpr Level} (hs : s.UsesBelow ρ n) (hnm : n ≤ m) : s.UsesBelow ρ m :=
  Silmaril.Proofs.Logic.TypeTheory.CIC.SortExprLaws.usesBelow_mono hs hnm

theorem ground_bound_iff (s : SortExpr ℕ) (n : ℕ) :
    s.UsesBelow id n ↔ s.universeBound ≤ n :=
  Silmaril.Proofs.Logic.TypeTheory.CIC.SortExprLaws.ground_bound_iff s n

/-- Impredicativity does not impose a bound on the domain's Type level. -/
@[simp] theorem product_prop {Level : Type u} (a : SortExpr Level) :
    a.product .prop = .prop := rfl

@[simp] theorem product_sprop {Level : Type u} (a : SortExpr Level) :
    a.product .sprop = .sprop := rfl

@[simp] theorem super_prop {Level : Type u} :
    (SortExpr.prop : SortExpr Level).super = .type (.succ .zero) := rfl

@[simp] theorem super_sprop {Level : Type u} :
    (SortExpr.sprop : SortExpr Level).super = .type (.succ .zero) := rfl

/-- Ordinary Prop cumulatively embeds into Set in the selected Rocq profile. -/
theorem prop_cumul_set {Level : Type u} (ρ : Level → ℕ) :
    (SortExpr.prop : SortExpr Level).Cumul ρ (.type .zero) := trivial

/-- Strict propositions do not acquire ordinary Prop's cumulativity. -/
theorem sprop_not_cumul_prop {Level : Type u} (ρ : Level → ℕ) :
    ¬ (SortExpr.sprop : SortExpr Level).Cumul ρ .prop := id

theorem sprop_not_cumul_type {Level : Type u} (ρ : Level → ℕ) (a : UniverseExpr Level) :
    ¬ (SortExpr.sprop : SortExpr Level).Cumul ρ (.type a) := id

/-- A ground Type level is not available in a supply ending immediately below it. -/
theorem ground_type_not_usesBelow (k : ℕ) :
    ¬ (SortExpr.type (.level k)).UsesBelow id k := Nat.lt_irrefl k

/-- The super-sort of Prop needs two available numeric levels, not one. -/
theorem prop_super_not_usesBelow_one {Level : Type u} (ρ : Level → ℕ) :
    ¬ (SortExpr.prop : SortExpr Level).super.UsesBelow ρ 1 := Nat.lt_irrefl 1

end SortExpr

end Silmaril.Logic.TypeTheory.CIC

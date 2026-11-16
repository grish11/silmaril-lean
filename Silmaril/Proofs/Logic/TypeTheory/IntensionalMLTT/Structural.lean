module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.Syntax.Defs

public section

namespace Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT

open Silmaril.Logic.TypeTheory.IntensionalMLTT
open Term

@[simp] theorem upRen_id (n : ℕ) : upRen (_root_.id : Fin n → Fin n) = _root_.id := by
  funext i
  cases i using Fin.cases <;> rfl

@[simp] theorem upRen_comp {n m k : ℕ} (ρ : Fin n → Fin m) (τ : Fin m → Fin k) :
    upRen (τ ∘ ρ) = upRen τ ∘ upRen ρ := by
  funext i
  cases i using Fin.cases <;> rfl

@[simp] theorem rename_id {n : ℕ} (t : Term n) : t.rename _root_.id = t := by
  induction t <;> simp_all [Term.rename]

theorem rename_comp {n m k : ℕ} (t : Term n) (ρ : Fin n → Fin m) (τ : Fin m → Fin k) :
    (t.rename ρ).rename τ = t.rename (τ ∘ ρ) := by
  induction t generalizing m k <;> simp_all [Term.rename]

@[simp] theorem upSub_var (n : ℕ) : upSub (Term.var : Fin n → Term n) = Term.var := by
  funext i
  cases i using Fin.cases <;> rfl

@[simp] theorem subst_var {n : ℕ} (t : Term n) : t.subst Term.var = t := by
  induction t <;> simp_all [Term.subst]

theorem upSub_ren {n m k : ℕ} (ρ : Fin n → Fin m) (σ : Fin m → Term k) :
    upSub (σ ∘ ρ) = upSub σ ∘ upRen ρ := by
  funext i
  cases i using Fin.cases <;> rfl

/-- Substitute after renaming by composing their variable actions. -/
theorem subst_rename {n m k : ℕ} (t : Term n) (ρ : Fin n → Fin m) (σ : Fin m → Term k) :
    (t.rename ρ).subst σ = t.subst (σ ∘ ρ) := by
  induction t generalizing m k <;> simp_all [Term.rename, Term.subst, upSub_ren]

theorem rename_upSub {n m k : ℕ} (σ : Fin n → Term m) (ρ : Fin m → Fin k) :
    (fun i => (upSub σ i).rename (upRen ρ)) = upSub (fun i => (σ i).rename ρ) := by
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
    change ((σ i).rename Fin.succ).rename (upRen ρ) = ((σ i).rename ρ).rename Fin.succ
    rw [rename_comp, rename_comp]
    rfl

/-- Renaming commutes with substitution by acting on each substituted term. -/
theorem rename_subst {n m k : ℕ} (t : Term n) (σ : Fin n → Term m) (ρ : Fin m → Fin k) :
    (t.subst σ).rename ρ = t.subst (fun i => (σ i).rename ρ) := by
  induction t generalizing m k <;> simp_all [Term.rename, Term.subst, rename_upSub]

theorem subst_upSub {n m k : ℕ} (σ : Fin n → Term m) (τ : Fin m → Term k) :
    (fun i => (upSub σ i).subst (upSub τ)) = upSub (fun i => (σ i).subst τ) := by
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
    change ((σ i).rename Fin.succ).subst (upSub τ) = ((σ i).subst τ).rename Fin.succ
    rw [subst_rename, rename_subst]
    rfl

/-- Simultaneous substitutions compose capture-avoidably under every binder. -/
theorem subst_comp {n m k : ℕ} (t : Term n) (σ : Fin n → Term m) (τ : Fin m → Term k) :
    (t.subst σ).subst τ = t.subst (fun i => (σ i).subst τ) := by
  induction t generalizing m k <;> simp_all [Term.subst, subst_upSub]

/-- Substitution by renamed variables agrees with renaming. -/
theorem subst_renaming {n m : ℕ} (t : Term n) (ρ : Fin n → Fin m) :
    t.subst (fun i => Term.var (ρ i)) = t.rename ρ := by
  have h : t.subst (Term.var ∘ ρ) = (t.rename ρ).subst Term.var :=
    (subst_rename t ρ Term.var).symm
  simpa only [subst_var, Function.comp_def] using h

/-- Renaming does not create or remove universe occurrences. -/
theorem universeBound_rename {n m : ℕ} (t : Term n) (ρ : Fin n → Fin m) :
    (t.rename ρ).universeBound = t.universeBound := by
  induction t generalizing m <;> simp_all [Term.rename, Term.universeBound]

/-- A single instantiation cancels weakening of a term. -/
theorem instantiate_weaken {n : ℕ} (t a : Term n) : t.weaken.instantiate a = t := by
  change (t.rename Fin.succ).subst (Fin.cons a Term.var) = t
  rw [subst_rename]
  exact subst_var t

/-- Instantiating the newest variable returns exactly the supplied term. -/
theorem instantiate_var {n : ℕ} (a : Term n) : (Term.var 0).instantiate a = a := rfl

/-- A J motive can separately select its endpoint and its path. -/
theorem instantiate₂_endpoint {n : ℕ} (a p : Term n) :
    (Term.var (1 : Fin (n + 2))).instantiate₂ a p = a := rfl

theorem instantiate₂_path {n : ℕ} (a p : Term n) :
    (Term.var (0 : Fin (n + 2))).instantiate₂ a p = p := rfl

end Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT

module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.Syntax.Defs
import Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Structural

@[expose] public section

/-! Capture-avoiding renaming and substitution, including J's two-binder motive. -/

namespace Silmaril.Logic.TypeTheory.IntensionalMLTT.Term

@[simp] theorem upRen_id (n : ℕ) : upRen (_root_.id : Fin n → Fin n) = _root_.id :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.upRen_id n

@[simp] theorem upRen_comp {n m k : ℕ} (ρ : Fin n → Fin m) (τ : Fin m → Fin k) :
    upRen (τ ∘ ρ) = upRen τ ∘ upRen ρ :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.upRen_comp ρ τ

@[simp] theorem rename_id {n : ℕ} (t : Term n) : t.rename _root_.id = t :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.rename_id t

theorem rename_comp {n m k : ℕ} (t : Term n) (ρ : Fin n → Fin m) (τ : Fin m → Fin k) :
    (t.rename ρ).rename τ = t.rename (τ ∘ ρ) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.rename_comp t ρ τ

@[simp] theorem upSub_var (n : ℕ) : upSub (Term.var : Fin n → Term n) = Term.var :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.upSub_var n

@[simp] theorem subst_var {n : ℕ} (t : Term n) : t.subst Term.var = t :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.subst_var t

theorem upSub_ren {n m k : ℕ} (ρ : Fin n → Fin m) (σ : Fin m → Term k) :
    upSub (σ ∘ ρ) = upSub σ ∘ upRen ρ :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.upSub_ren ρ σ

theorem subst_rename {n m k : ℕ} (t : Term n) (ρ : Fin n → Fin m) (σ : Fin m → Term k) :
    (t.rename ρ).subst σ = t.subst (σ ∘ ρ) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.subst_rename t ρ σ

theorem rename_upSub {n m k : ℕ} (σ : Fin n → Term m) (ρ : Fin m → Fin k) :
    (fun i => (upSub σ i).rename (upRen ρ)) = upSub (fun i => (σ i).rename ρ) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.rename_upSub σ ρ

theorem rename_subst {n m k : ℕ} (t : Term n) (σ : Fin n → Term m) (ρ : Fin m → Fin k) :
    (t.subst σ).rename ρ = t.subst (fun i => (σ i).rename ρ) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.rename_subst t σ ρ

theorem subst_upSub {n m k : ℕ} (σ : Fin n → Term m) (τ : Fin m → Term k) :
    (fun i => (upSub σ i).subst (upSub τ)) = upSub (fun i => (σ i).subst τ) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.subst_upSub σ τ

theorem subst_comp {n m k : ℕ} (t : Term n) (σ : Fin n → Term m) (τ : Fin m → Term k) :
    (t.subst σ).subst τ = t.subst (fun i => (σ i).subst τ) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.subst_comp t σ τ

theorem subst_renaming {n m : ℕ} (t : Term n) (ρ : Fin n → Fin m) :
    t.subst (fun i => Term.var (ρ i)) = t.rename ρ :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.subst_renaming t ρ

theorem universeBound_rename {n m : ℕ} (t : Term n) (ρ : Fin n → Fin m) :
    (t.rename ρ).universeBound = t.universeBound :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.universeBound_rename t ρ

theorem instantiate_weaken {n : ℕ} (t a : Term n) : t.weaken.instantiate a = t :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.instantiate_weaken t a

end Silmaril.Logic.TypeTheory.IntensionalMLTT.Term

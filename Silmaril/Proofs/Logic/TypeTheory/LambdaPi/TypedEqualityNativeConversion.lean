module

public import Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.NativeConversion.Defs

public section

namespace Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityNativeConversion

open Silmaril.Logic.TypeTheory
open Silmaril.Logic.TypeTheory.LambdaPi
open Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality
open Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.NativeConversion

open Silmaril.Calculi.LambdaCube

/-- Renaming a source term composes its variable assignment. -/
theorem term_rename {n m : ℕ} (t : SourceTerm n) (r : Fin n → Fin m)
    (σ : Fin m → LambdaPi.Term) : term σ (t.rename r) = term (σ ∘ r) t := by
  induction t generalizing m with
  | var i => rfl
  | univ i => cases i with
    | zero => rfl
    | succ i => cases i <;> rfl
  | pi A B ihA ihB | lam A B ihA ihB =>
    simp only [IntensionalMLTT.Term.rename, term, ihA, ihB]
    congr 1
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  | app f a ihf iha => simp only [IntensionalMLTT.Term.rename, term, ihf, iha]
  | _ => rfl

/-- Native renaming acts on the explicit source-variable assignment. -/
theorem term_nativeRename {n : ℕ} (t : SourceTerm n) (σ : Fin n → LambdaPi.Term)
    (r : ℕ → ℕ) : (term σ t).rename r = term (fun i => (σ i).rename r) t := by
  induction t generalizing r with
  | var i => rfl
  | univ i => cases i with
    | zero => rfl
    | succ i => cases i <;> rfl
  | pi A B ihA ihB | lam A B ihA ihB =>
    simp only [term, Pseudo.rename, ihA, ihB]
    congr 1
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp only [lift, Fin.cons_succ, Pseudo.rename_rename]
      rfl
  | app f a ihf iha => simp only [term, Pseudo.rename, ihf, iha]
  | _ => rfl

/-- Native substitution acts on the explicit source-variable assignment. -/
theorem term_nativeSubst {n : ℕ} (t : SourceTerm n) (σ : Fin n → LambdaPi.Term)
    (τ : ℕ → LambdaPi.Term) : (term σ t).subst τ = term (fun i => (σ i).subst τ) t := by
  induction t generalizing τ with
  | var i => rfl
  | univ i => cases i with
    | zero => rfl
    | succ i => cases i <;> rfl
  | pi A B ihA ihB | lam A B ihA ihB =>
    simp only [term, Pseudo.subst, ihA, ihB]
    congr 1
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp only [lift, Fin.cons_succ, Pseudo.subst_rename, Pseudo.rename_subst]
      rfl
  | app f a ihf iha => simp only [term, Pseudo.subst, ihf, iha]
  | _ => rfl

/-- Source substitution composes compiled assignments. -/
theorem term_subst {n m : ℕ} (t : SourceTerm n) (τ : Fin n → SourceTerm m)
    (σ : Fin m → LambdaPi.Term) :
    term σ (t.subst τ) = term (fun i => term σ (τ i)) t := by
  induction t generalizing m with
  | var i => rfl
  | univ i => cases i with
    | zero => rfl
    | succ i => cases i <;> rfl
  | pi A B ihA ihB | lam A B ihA ihB =>
    simp only [IntensionalMLTT.Term.subst, term, ihA, ihB]
    congr 1
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp only [IntensionalMLTT.Term.upSub, Fin.cons_succ,
        IntensionalMLTT.Term.weaken, term_rename, lift, Fin.cons_succ]
      exact (term_nativeRename (τ j) σ Nat.succ).symm
  | app f a ihf iha => simp only [IntensionalMLTT.Term.subst, term, ihf, iha]
  | _ => rfl

/-- Source binder discharge is native capture-avoiding beta substitution. -/
theorem term_instantiate {n : ℕ} (b : SourceTerm (n + 1)) (a : SourceTerm n)
    (σ : Fin n → LambdaPi.Term) :
    term σ (b.instantiate a) = (term (lift σ) b).substOne (term σ a) := by
  rw [IntensionalMLTT.Term.instantiate, term_subst, Pseudo.substOne, term_nativeSubst]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp only [Fin.cons_succ, lift, term, Pseudo.subst_rename]
    exact (Pseudo.subst_var (σ j) _ (fun _ => rfl)).symm

/-- Every independently checked LF equality gives native raw beta-eta conversion.
The assignment may use named constants for globals and native variables for locals.
This theorem supplies conversion, not native endpoint typing or its converse. -/
theorem equality {k n : ℕ} {S : IntensionalMLTT.Context k}
    {Γ : IntensionalMLTT.Context n} {t u A : SourceTerm n}
    (h : Equality S Γ t u A) (σ : Fin n → LambdaPi.Term) :
    BetaEtaConversion (term σ t) (term σ u) := by
  induction h using Equality.rec (motive_1 := fun _ _ => True)
      (motive_2 := fun _ _ _ _ => True)
  case nil => trivial
  case snoc => trivial
  case signature => trivial
  case snoc => intros; trivial
  case type => exact .refl _
  case var => exact .refl _
  case pi hA hB ihA ihB => exact .pi (ihA σ) (ihB (lift σ))
  case lam hA hB hb ihA ihB ihb => exact .lam (.refl _) (ihb (lift σ))
  case app hA hB hf ha ihA ihB ihf iha => exact .app (ihf σ) (iha σ)
  case beta hA hB hb ha ihA ihB ihb iha =>
    simp only [term, term_instantiate]
    exact .beta _ _ _
  case eta k n S s Γ A f B hA hB hf ihA ihB ihf =>
    simp only [term, IntensionalMLTT.Term.weaken, term_rename]
    have he : term (lift σ ∘ Fin.succ) f = (term σ f).rename Nat.succ :=
      (term_nativeRename f σ Nat.succ).symm
    rw [he]
    exact .eta _ _
  case conv ht hAB iht ihAB => exact iht σ
  case symm h ih => exact .symm (ih σ)
  case trans h h' ih ih' => exact .trans (ih σ) (ih' σ)

/-- The same forward equality theorem in the existing named beta-eta calculus. -/
theorem equality_conversion {k n : ℕ} {S : IntensionalMLTT.Context k}
    {Γ : IntensionalMLTT.Context n} {t u A : SourceTerm n}
    (h : Equality S Γ t u A) (σ : Fin n → LambdaPi.Term)
    (declared : String → LambdaPi.Term → Prop) :
    (Calculus.lfBetaEta declared).Conversion (term σ t) (term σ u) :=
  (Calculus.lfBetaEta_conversion_iff declared _ _).mpr (equality h σ)

end Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityNativeConversion

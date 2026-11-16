module

public import Silmaril.Logic.TypeTheory.LambdaPi.ContextConversion.Defs

@[expose] public section

namespace Silmaril.Proofs.Logic.TypeTheory.LambdaPi

open Silmaril.Logic.TypeTheory.LambdaPi Silmaril.Calculi.LambdaCube

theorem conversion_rename {C : Calculus} {t u : Term} (h : C.Conversion t u) (ρ : ℕ → ℕ) :
    C.Conversion (t.rename ρ) (u.rename ρ) := by
  induction h generalizing ρ with
  | refl _ => exact .refl _
  | symm _ ih => exact .symm (ih ρ)
  | trans _ _ ih₁ ih₂ => exact .trans (ih₁ ρ) (ih₂ ρ)
  | beta A b a =>
    simpa only [Pseudo.rename, Pseudo.rename_substOne] using
      (Calculus.Conversion.beta (C := C) (A.rename ρ)
        (b.rename (Silmaril.DeBruijn.lift ρ)) (a.rename ρ))
  | rewrite r hr σ =>
    simp only [Pseudo.rename_subst]
    exact .rewrite r hr (Pseudo.rename ρ ∘ σ)
  | app _ _ ihf iha => exact .app (ihf ρ) (iha ρ)
  | lam _ _ ihA ihb => exact .lam (ihA ρ) (ihb _)
  | pi _ _ ihA ihB => exact .pi (ihA ρ) (ihB _)

theorem context_conversion_contexts {C : Calculus} {Γ Δ : List Term}
    (h : ContextConversion C Γ Δ) : ContextOK C Γ ∧ ContextOK C Δ := by
  induction h with
  | nil => exact ⟨.nil, .nil⟩
  | cons _ hA hB _ ih => exact ⟨.cons ih.1 hA, .cons ih.2 hB⟩

theorem context_conversion_id {C : Calculus} {Γ : List Term} (h : ContextOK C Γ) :
    ContextConversion C Γ Γ := by
  induction h with
  | nil => exact .nil
  | cons _ hA ih => exact .cons ih hA hA (.refl _)

theorem context_conversion_symm {C : Calculus} {Γ Δ : List Term}
    (h : ContextConversion C Γ Δ) : ContextConversion C Δ Γ := by
  induction h with
  | nil => exact .nil
  | cons _ hA hB he ih => exact .cons ih hB hA he.symm

theorem context_conversion_trans {C : Calculus} {Γ Δ Θ : List Term}
    (h : ContextConversion C Γ Δ) (h' : ContextConversion C Δ Θ) : ContextConversion C Γ Θ := by
  induction h generalizing Θ with
  | nil => cases h'; exact .nil
  | cons _ hA _ he ih =>
    cases h' with
    | cons h' _ hD he' => exact .cons (ih h') hA hD (he.trans he')

theorem context_conversion_typed {C : Calculus} {Γ Δ : List Term}
    (h : ContextConversion C Γ Δ) : TypedSubstitution C Γ Δ Pseudo.var := by
  induction h with
  | nil => exact ⟨.nil, fun hi => nomatch hi⟩
  | @cons Γ Δ A B h hA hB he ih =>
    have hA' : Derives C ∅ ⟨Δ, A, Term.univ .type⟩ := by
      simpa only [Pseudo.subst_var _ _ (fun _ => rfl), Pseudo.subst] using hA.subst ih
    refine ⟨.cons ih.target hB, ?_⟩
    intro i T hi
    cases hi with
    | zero =>
      have hv := Derives.conv (Derives.var hB) (conversion_rename he.symm Nat.succ) (Derives.weak hA' hB)
      simpa only [Pseudo.subst_var _ _ (fun _ => rfl)] using hv
    | succ D hi =>
      have hv := Derives.weak (ih.entries hi) hB
      simpa only [Pseudo.subst_var _ _ (fun _ => rfl), Pseudo.rename] using hv

end Silmaril.Proofs.Logic.TypeTheory.LambdaPi

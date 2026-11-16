module

public import Silmaril.Logic.TypeTheory.LambdaPi.Substitution.Defs

@[expose] public section

namespace Silmaril.Proofs.Logic.TypeTheory.LambdaPi

open Silmaril.Logic.TypeTheory.LambdaPi Silmaril.Calculi.LambdaCube

theorem scoped_rename (t : Term) : ∀ {n m} (ρ : ℕ → ℕ), t.Scoped n →
    (∀ i < n, ρ i < m) → Term.Scoped m (t.rename ρ) := by
  have hl : ∀ {n m} (ρ : ℕ → ℕ), (∀ i < n, ρ i < m) →
      ∀ i < n + 1, Silmaril.DeBruijn.lift ρ i < m + 1 := by
    intro n m ρ h i hi
    cases i with
    | zero => exact Nat.zero_lt_succ _
    | succ i => exact Nat.succ_lt_succ (h i (Nat.lt_of_succ_lt_succ hi))
  induction t with
  | sort _ => intros; trivial
  | var i => exact fun ρ ht hρ => hρ i ht
  | app _ _ ihf iha => exact fun ρ ht hρ => ⟨ihf ρ ht.1 hρ, iha ρ ht.2 hρ⟩
  | lam _ _ ihA ihb => exact fun ρ ht hρ => ⟨ihA ρ ht.1 hρ, ihb _ ht.2 (hl ρ hρ)⟩
  | pi _ _ ihA ihB => exact fun ρ ht hρ => ⟨ihA ρ ht.1 hρ, ihB _ ht.2 (hl ρ hρ)⟩

theorem scoped_subst (t : Term) : ∀ {n m} (σ : ℕ → Term), t.Scoped n →
    (∀ i < n, (σ i).Scoped m) → Term.Scoped m (t.subst σ) := by
  have hl : ∀ {n m} (σ : ℕ → Term), (∀ i < n, (σ i).Scoped m) →
      ∀ i < n + 1, Term.Scoped (m + 1) (Pseudo.liftSub σ i) := by
    intro n m σ h i hi
    cases i with
    | zero => exact Nat.zero_lt_succ _
    | succ i =>
      exact scoped_rename _ Nat.succ (h i (Nat.lt_of_succ_lt_succ hi))
        (fun j hj => Nat.succ_lt_succ hj)
  induction t with
  | sort _ => intros; trivial
  | var i => exact fun σ ht hσ => hσ i ht
  | app _ _ ihf iha => exact fun σ ht hσ => ⟨ihf σ ht.1 hσ, iha σ ht.2 hσ⟩
  | lam _ _ ihA ihb => exact fun σ ht hσ => ⟨ihA σ ht.1 hσ, ihb _ ht.2 (hl σ hσ)⟩
  | pi _ _ ihA ihB => exact fun σ ht hσ => ⟨ihA σ ht.1 hσ, ihB _ ht.2 (hl σ hσ)⟩

theorem scoped_substOne {n : ℕ} {b a : Term} (hb : b.Scoped (n + 1)) (ha : a.Scoped n) :
    Term.Scoped n (b.substOne a) := by
  apply scoped_subst b (fun | 0 => a | i + 1 => .var i) hb
  intro i hi
  cases i with
  | zero => exact ha
  | succ i => exact Nat.lt_of_succ_lt_succ hi

theorem derives_scoped {C : Calculus} {J : Judgment} (h : Derives C ∅ J) :
    J.term.Scoped J.context.length ∧ J.type.Scoped J.context.length := by
  induction h with
  | hyp h => exact False.elim h
  | type => exact ⟨True.intro, True.intro⟩
  | constant _ _ ih => exact ⟨True.intro, ih.1⟩
  | var hA ih => exact ⟨Nat.zero_lt_succ _,
      scoped_rename _ Nat.succ ih.1 (fun _ hi => Nat.succ_lt_succ hi)⟩
  | weak _ _ iht _ => exact ⟨
      scoped_rename _ Nat.succ iht.1 (fun _ hi => Nat.succ_lt_succ hi),
      scoped_rename _ Nat.succ iht.2 (fun _ hi => Nat.succ_lt_succ hi)⟩
  | pi _ _ ihA ihB => exact ⟨⟨ihA.1, ihB.1⟩, True.intro⟩
  | lam _ _ ihb ihpi => exact ⟨⟨ihpi.1.1, ihb.1⟩, ihpi.1⟩
  | app _ _ ihf iha => exact ⟨⟨ihf.1, iha.1⟩, scoped_substOne ihf.2.2 iha.1⟩
  | conv _ _ _ iht ihB => exact ⟨iht.1, ihB.1⟩

theorem derives_context {C : Calculus} {J : Judgment} (h : Derives C ∅ J) :
    ContextOK C J.context := by
  induction h with
  | hyp h => exact False.elim h
  | type => exact .nil
  | constant _ _ _ => exact .nil
  | var hA ih => exact .cons ih hA
  | weak _ hB iht _ => exact .cons iht hB
  | pi _ _ ihA _ => exact ihA
  | lam _ _ _ ihpi => exact ihpi
  | app _ _ ihf _ => exact ihf
  | conv _ _ _ iht _ => exact iht

theorem derives_closed_weaken {C : Calculus} {Δ : List Term} {t A : Term}
    (hΔ : ContextOK C Δ) (h : Derives C ∅ ⟨[], t, A⟩) : Derives C ∅ ⟨Δ, t, A⟩ := by
  have ht : t.Scoped 0 := (derives_scoped h).1
  have hA : A.Scoped 0 := (derives_scoped h).2
  induction hΔ with
  | nil => exact h
  | cons _ hB ih =>
    have hr := Derives.weak ih hB
    simpa only [rename_eq_scoped t Nat.succ ht (by omega),
      rename_eq_scoped A Nat.succ hA (by omega)] using hr

theorem lookup_derives {C : Calculus} {Γ : List Term} (hΓ : ContextOK C Γ)
    {i : ℕ} {A : Term} (hi : Lookup Γ i A) : Derives C ∅ ⟨Γ, .var i, A⟩ := by
  induction hi with
  | zero Γ A => cases hΓ with | cons _ hA => exact .var hA
  | succ B hi ih =>
    cases hΓ with
    | cons hΓ hB => exact .weak (ih hΓ) hB

theorem typed_substitution_tail {C : Calculus} {Γ Δ : List Term} {A : Term} {σ : ℕ → Term}
    (hσ : TypedSubstitution C (A :: Γ) Δ σ) :
    TypedSubstitution C Γ Δ (fun i => σ (i + 1)) where
  target := hσ.target
  entries hi := by
    have h := hσ.entries (Lookup.succ A hi)
    simpa only [Pseudo.subst_rename, Function.comp_def] using h

theorem typed_substitution_lift {C : Calculus} {Γ Δ : List Term} {A : Term} {σ : ℕ → Term}
    (hσ : TypedSubstitution C Γ Δ σ) (hA : Derives C ∅ ⟨Δ, A.subst σ, Term.univ .type⟩) :
    TypedSubstitution C (A :: Γ) (A.subst σ :: Δ) (Pseudo.liftSub σ) where
  target := .cons hσ.target hA
  entries := by
    intro i B hi
    cases hi with
    | zero =>
      have he : (A.rename Nat.succ).subst (Pseudo.liftSub σ) =
          (A.subst σ).rename Nat.succ := by
        rw [Pseudo.subst_rename, Pseudo.rename_subst]
        rfl
      simpa only [Pseudo.liftSub, he] using Derives.var hA
    | succ B hi =>
      have hj := Derives.weak (hσ.entries hi) hA
      simpa only [Pseudo.liftSub, Pseudo.subst_rename, Pseudo.rename_subst,
        Function.comp_def] using hj

theorem derives_pi_domain {C : Calculus} {J : Judgment} (h : Derives C ∅ J) :
    ∀ A B, J.term = .pi A B → Derives C ∅ ⟨J.context, A, Term.univ .type⟩ := by
  induction h with
  | hyp h => exact False.elim h
  | type => intro A B he; cases he
  | constant _ _ _ => intro A B he; cases he
  | var _ _ => intro A B he; cases he
  | @weak Γ t T D ht hD ih _ =>
    intro A B he
    cases t with
    | sort _ => cases he
    | var _ => cases he
    | app _ _ => cases he
    | lam _ _ => cases he
    | pi A₀ B₀ =>
      cases he
      exact .weak (ih A₀ B₀ rfl) hD
  | pi hA _ _ _ => intro A B he; cases he; exact hA
  | lam _ _ _ _ => intro A B he; cases he
  | app _ _ _ _ => intro A B he; cases he
  | conv _ _ _ ih _ => exact ih

theorem derives_substitution {C : Calculus} {J : Judgment} (h : Derives C ∅ J)
    {Δ : List Term} {σ : ℕ → Term} (hσ : TypedSubstitution C J.context Δ σ) :
    Derives C ∅ ⟨Δ, J.term.subst σ, J.type.subst σ⟩ := by
  induction h generalizing Δ σ with
  | hyp h => exact False.elim h
  | type => exact derives_closed_weaken hσ.target Derives.type
  | constant hd hA _ =>
    have ht := derives_closed_weaken hσ.target (Derives.constant hd hA)
    have hc : Term.Scoped 0 _ := (derives_scoped hA).1
    simpa only [Pseudo.subst, subst_eq_scoped _ σ hc (by omega)] using ht
  | var hA _ => exact hσ.entries (Lookup.zero _ _)
  | weak _ _ iht _ =>
    simpa only [Pseudo.subst_rename, Function.comp_def] using iht (typed_substitution_tail hσ)
  | pi _ _ ihA ihB =>
    exact .pi (ihA hσ) (ihB (typed_substitution_lift hσ (ihA hσ)))
  | lam _ _ ihb ihpi =>
    have hp := ihpi hσ
    have hdomain := derives_pi_domain hp _ _ rfl
    exact .lam (ihb (typed_substitution_lift hσ hdomain)) hp
  | app _ _ ihf iha =>
    simpa only [Pseudo.subst, Pseudo.subst_substOne] using Derives.app (ihf hσ) (iha hσ)
  | conv _ heq _ iht ihB => exact .conv (iht hσ) (heq.subst σ) (ihB hσ)

theorem typed_substitution_id {C : Calculus} {Γ : List Term} (hΓ : ContextOK C Γ) :
    TypedSubstitution C Γ Γ Pseudo.var where
  target := hΓ
  entries hi := by
    simpa only [Pseudo.subst_var _ _ (fun _ => rfl)] using lookup_derives hΓ hi

theorem typed_substitution_comp {C : Calculus} {Γ Δ Θ : List Term} {σ τ : ℕ → Term}
    (hσ : TypedSubstitution C Γ Δ σ) (hτ : TypedSubstitution C Δ Θ τ) :
    TypedSubstitution C Γ Θ (fun i => (σ i).subst τ) where
  target := hτ.target
  entries hi := by
    simpa only [Pseudo.subst_subst, Function.comp_def] using
      derives_substitution (hσ.entries hi) hτ

theorem typed_substitution_single {C : Calculus} {Γ : List Term} {A a : Term}
    (ha : Derives C ∅ ⟨Γ, a, A⟩) :
    TypedSubstitution C (A :: Γ) Γ (fun | 0 => a | i + 1 => .var i) where
  target := derives_context ha
  entries := by
    intro i B hi
    cases hi with
    | zero =>
      simpa only [Pseudo.subst_rename, Function.comp_def,
        Pseudo.subst_var _ _ (fun _ => rfl)] using ha
    | succ B hi =>
      simpa only [Pseudo.subst_rename, Function.comp_def,
        Pseudo.subst_var _ _ (fun _ => rfl)] using lookup_derives (derives_context ha) hi

end Silmaril.Proofs.Logic.TypeTheory.LambdaPi

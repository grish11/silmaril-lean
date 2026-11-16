module

public import Silmaril.Logic.TypeTheory.LambdaPi.Encoding.Defs

@[expose] public section

namespace Silmaril.Proofs.Logic.TypeTheory.LambdaPi

open Silmaril.Logic.TypeTheory.LambdaPi Silmaril.Calculi.LambdaCube

theorem scoped_mono (t : Term) : ∀ {n m}, n ≤ m → t.Scoped n → t.Scoped m := by
  induction t with
  | sort _ => intros; trivial
  | var _ => exact fun h hn => Nat.lt_of_lt_of_le hn h
  | app _ _ ihf iha => exact fun h ht => ⟨ihf h ht.1, iha h ht.2⟩
  | lam _ _ ihA ihb => exact fun h ht => ⟨ihA h ht.1, ihb (Nat.succ_le_succ h) ht.2⟩
  | pi _ _ ihA ihB => exact fun h ht => ⟨ihA h ht.1, ihB (Nat.succ_le_succ h) ht.2⟩

theorem rename_eq_scoped (t : Term) : ∀ {n} (ρ : ℕ → ℕ), t.Scoped n →
    (∀ i < n, ρ i = i) → t.rename ρ = t := by
  have hl : ∀ {n} (ρ : ℕ → ℕ), (∀ i < n, ρ i = i) →
      ∀ i < n + 1, Silmaril.DeBruijn.lift ρ i = i := by
    intro n ρ h i hi
    cases i with
    | zero => rfl
    | succ i => exact congrArg Nat.succ (h i (Nat.lt_of_succ_lt_succ hi))
  induction t with
  | sort _ => intros; rfl
  | var i => intro n ρ ht h; exact congrArg Pseudo.var (h i ht)
  | app _ _ ihf iha => intro n ρ ht h; simp only [Pseudo.rename, ihf ρ ht.1 h, iha ρ ht.2 h]
  | lam _ _ ihA ihb =>
    intro n ρ ht h
    simp only [Pseudo.rename, ihA ρ ht.1 h, ihb _ ht.2 (hl ρ h)]
  | pi _ _ ihA ihB =>
    intro n ρ ht h
    simp only [Pseudo.rename, ihA ρ ht.1 h, ihB _ ht.2 (hl ρ h)]

theorem subst_eq_scoped (t : Term) : ∀ {n} (σ : ℕ → Term), t.Scoped n →
    (∀ i < n, σ i = .var i) → t.subst σ = t := by
  have hl : ∀ {n} (σ : ℕ → Term), (∀ i < n, σ i = .var i) →
      ∀ i < n + 1, Pseudo.liftSub σ i = .var i := by
    intro n σ h i hi
    cases i with
    | zero => rfl
    | succ i => simp only [Pseudo.liftSub, h i (Nat.lt_of_succ_lt_succ hi), Pseudo.rename]
  induction t with
  | sort _ => intros; rfl
  | var i => intro n σ ht h; exact h i ht
  | app _ _ ihf iha => intro n σ ht h; simp only [Pseudo.subst, ihf σ ht.1 h, iha σ ht.2 h]
  | lam _ _ ihA ihb =>
    intro n σ ht h
    simp only [Pseudo.subst, ihA σ ht.1 h, ihb _ ht.2 (hl σ h)]
  | pi _ _ ihA ihB =>
    intro n σ ht h
    simp only [Pseudo.subst, ihA σ ht.1 h, ihB _ ht.2 (hl σ h)]

theorem assignment_scoped (F : ConstantAssignment) (t : Term) : ∀ {n}, t.Scoped n →
    (F.term t).Scoped n := by
  induction t with
  | sort a =>
    intro n _
    cases a with
    | sort _ => trivial
    | constant c => exact scoped_mono _ (Nat.zero_le n) (F.closed c)
  | var _ => exact fun h => h
  | app _ _ ihf iha => exact fun h => ⟨ihf h.1, iha h.2⟩
  | lam _ _ ihA ihb => exact fun h => ⟨ihA h.1, ihb h.2⟩
  | pi _ _ ihA ihB => exact fun h => ⟨ihA h.1, ihB h.2⟩

theorem assignment_rename (F : ConstantAssignment) (t : Term) (ρ : ℕ → ℕ) :
    F.term (t.rename ρ) = (F.term t).rename ρ := by
  induction t generalizing ρ with
  | sort a =>
    cases a with
    | sort _ => rfl
    | constant c => exact (rename_eq_scoped _ ρ (F.closed c) (by omega)).symm
  | var _ => rfl
  | app _ _ ihf iha => simp only [Pseudo.rename, ConstantAssignment.term, ihf, iha]
  | lam _ _ ihA ihb => simp only [Pseudo.rename, ConstantAssignment.term, ihA, ihb]
  | pi _ _ ihA ihB => simp only [Pseudo.rename, ConstantAssignment.term, ihA, ihB]

theorem assignment_subst (F : ConstantAssignment) (t : Term) (σ : ℕ → Term) :
    F.term (t.subst σ) = (F.term t).subst (fun i => F.term (σ i)) := by
  have hl : ∀ σ : ℕ → Term,
      (fun i => F.term (Pseudo.liftSub σ i)) = Pseudo.liftSub (fun i => F.term (σ i)) := by
    intro σ
    funext i
    cases i with
    | zero => rfl
    | succ i => exact assignment_rename F (σ i) Nat.succ
  induction t generalizing σ with
  | sort a =>
    cases a with
    | sort _ => rfl
    | constant c => exact (subst_eq_scoped _ _ (F.closed c) (by omega)).symm
  | var _ => rfl
  | app _ _ ihf iha => simp only [Pseudo.subst, ConstantAssignment.term, ihf, iha]
  | lam _ _ ihA ihb => simp only [Pseudo.subst, ConstantAssignment.term, ihA, ihb, hl]
  | pi _ _ ihA ihB => simp only [Pseudo.subst, ConstantAssignment.term, ihA, ihB, hl]

theorem assignment_substOne (F : ConstantAssignment) (b a : Term) :
    F.term (b.substOne a) = (F.term b).substOne (F.term a) := by
  rw [Pseudo.substOne, assignment_subst]
  congr 1
  funext i
  cases i <;> rfl

theorem conversion_subst {C : Calculus} {t u : Term} (h : C.Conversion t u) (σ : ℕ → Term) :
    C.Conversion (t.subst σ) (u.subst σ) := by
  induction h generalizing σ with
  | refl _ => exact .refl _
  | symm _ ih => exact .symm (ih σ)
  | trans _ _ ih₁ ih₂ => exact .trans (ih₁ σ) (ih₂ σ)
  | beta A b a =>
    simpa only [Pseudo.subst, Pseudo.subst_substOne] using
      (Calculus.Conversion.beta (C := C) (A.subst σ) (b.subst (Pseudo.liftSub σ)) (a.subst σ))
  | rewrite r hr τ =>
    simp only [Pseudo.subst_subst]
    exact .rewrite r hr (Pseudo.subst σ ∘ τ)
  | app _ _ ihf iha => exact .app (ihf σ) (iha σ)
  | lam _ _ ihA ihb => exact .lam (ihA σ) (ihb _)
  | pi _ _ ihA ihB => exact .pi (ihA σ) (ihB _)

theorem encoding_conversion {C D : TypedPresentation} (F : Encoding C D) {t u : Term}
    (h : C.calculus.Conversion t u) :
    D.calculus.Conversion (F.term t) (F.term u) := by
  induction h with
  | refl _ => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | beta A b a =>
    simpa only [ConstantAssignment.term, assignment_substOne] using
      (Calculus.Conversion.beta (C := D.calculus) (F.term A) (F.term b) (F.term a))
  | rewrite r hr σ =>
    simpa only [assignment_subst] using
      conversion_subst (F.rules r hr) (fun i => F.term (σ i))
  | app _ _ ihf iha => exact .app ihf iha
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | pi _ _ ihA ihB => exact .pi ihA ihB

theorem encoding_derives {C D : TypedPresentation} (F : Encoding C D)
    {H : Set Judgment} {J : Judgment} (h : Derives C.calculus H J) :
    Derives D.calculus (F.judgment '' H) (F.judgment J) := by
  induction h with
  | hyp h => exact .hyp ⟨_, h, rfl⟩
  | type => exact .type
  | constant hd _ _ => exact (F.declared hd).mono (Set.empty_subset _)
  | var _ ih =>
    simpa only [ConstantAssignment.judgment, ConstantAssignment.term, List.map_cons,
      assignment_rename] using Derives.var ih
  | weak _ _ iht ihB =>
    simpa only [ConstantAssignment.judgment, ConstantAssignment.term, List.map_cons,
      assignment_rename] using Derives.weak iht ihB
  | pi _ _ ihA ihB => exact .pi ihA ihB
  | lam _ _ ihb ihpi => exact .lam ihb ihpi
  | app _ _ ihf iha =>
    simpa only [ConstantAssignment.judgment, ConstantAssignment.term,
      assignment_substOne] using Derives.app ihf iha
  | conv _ heq _ iht ihB => exact .conv iht (encoding_conversion F heq) ihB

theorem assignment_identity (F : ConstantAssignment) (h : F.constants = Term.constant)
    (t : Term) : F.term t = t := by
  induction t with
  | sort a => cases a <;> simp only [ConstantAssignment.term, h]
  | var _ => rfl
  | app _ _ ihf iha => simp only [ConstantAssignment.term, ihf, iha]
  | lam _ _ ihA ihb => simp only [ConstantAssignment.term, ihA, ihb]
  | pi _ _ ihA ihB => simp only [ConstantAssignment.term, ihA, ihB]

theorem assignment_composition (F G K : ConstantAssignment)
    (h : ∀ c, K.constants c = G.term (F.constants c)) (t : Term) :
    K.term t = G.term (F.term t) := by
  induction t with
  | sort a => cases a with
    | sort _ => rfl
    | constant c => exact h c
  | var _ => rfl
  | app _ _ ihf iha => simp only [ConstantAssignment.term, ihf, iha]
  | lam _ _ ihA ihb => simp only [ConstantAssignment.term, ihA, ihb]
  | pi _ _ ihA ihB => simp only [ConstantAssignment.term, ihA, ihB]

theorem assignment_names (F : ConstantAssignment) (f : String → String)
    (h : ∀ c, F.constants c = Term.constant (f c)) (t : Term) :
    F.term t = t.mapConstants f := by
  induction t with
  | sort a => cases a with
    | sort _ => rfl
    | constant c => exact h c
  | var _ => rfl
  | app _ _ ihf iha => simp only [ConstantAssignment.term, Term.mapConstants, Pseudo.mapSorts, ihf, iha]
  | lam _ _ ihA ihb => simp only [ConstantAssignment.term, Term.mapConstants, Pseudo.mapSorts, ihA, ihb]
  | pi _ _ ihA ihB => simp only [ConstantAssignment.term, Term.mapConstants, Pseudo.mapSorts, ihA, ihB]

end Silmaril.Proofs.Logic.TypeTheory.LambdaPi

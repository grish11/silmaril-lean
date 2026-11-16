module

public import Silmaril.Logic.TypeTheory.LambdaPi.Generation.Defs

@[expose] public section

namespace Silmaril.Proofs.Logic.TypeTheory.LambdaPi

open Silmaril.Logic.TypeTheory.LambdaPi Silmaril.Calculi.LambdaCube

theorem rename_as_subst (t : Term) (ρ : ℕ → ℕ) : t.rename ρ = t.subst (fun i => .var (ρ i)) := by
  have hl : ∀ ρ : ℕ → ℕ, Pseudo.liftSub (fun i => (Pseudo.var (ρ i) : Term)) =
      (fun i => .var (Silmaril.DeBruijn.lift ρ i)) := by
    intro ρ
    funext i
    cases i <;> rfl
  induction t generalizing ρ with
  | sort _ => rfl
  | var _ => rfl
  | app _ _ ihf iha => simp only [Pseudo.rename, Pseudo.subst, ihf, iha]
  | lam _ _ ihA ihb => simp only [Pseudo.rename, Pseudo.subst, ihA, ihb, hl]
  | pi _ _ ihA ihB => simp only [Pseudo.rename, Pseudo.subst, ihA, ihB, hl]

theorem typed_weakening_assignment {C : Calculus} {Γ : List Term} {D : Term}
    (hD : Derives C ∅ ⟨Γ, D, Term.univ .type⟩) :
    TypedSubstitution C Γ (D :: Γ) (fun i => .var (Nat.succ i)) where
  target := .cons hD.contextOK hD
  entries hi := by
    have hv := Derives.weak (hi.derives hD.contextOK) hD
    simpa only [← rename_as_subst, Pseudo.rename] using hv

theorem weaken_beneath {C : Calculus} {Γ : List Term} {A b B D : Term}
    (h : Derives C ∅ ⟨A :: Γ, b, B⟩) (hA : Derives C ∅ ⟨Γ, A, Term.univ .type⟩)
    (hD : Derives C ∅ ⟨Γ, D, Term.univ .type⟩) :
    Derives C ∅ ⟨A.rename Nat.succ :: D :: Γ,
      b.rename (Silmaril.DeBruijn.lift Nat.succ), B.rename (Silmaril.DeBruijn.lift Nat.succ)⟩ := by
  have hσ := typed_weakening_assignment hD
  have hA' : Derives C ∅ ⟨D :: Γ, A.subst (fun i => .var (Nat.succ i)), Term.univ .type⟩ := by
    simpa only [← rename_as_subst, Pseudo.rename] using Derives.weak hA hD
  have ht := h.subst (hσ.lift hA')
  have hl : Pseudo.liftSub (fun i => (Pseudo.var (Nat.succ i) : Term)) =
      (fun i => .var (Silmaril.DeBruijn.lift Nat.succ i)) := by
    funext i
    cases i <;> rfl
  simpa only [hl, ← rename_as_subst] using ht

theorem product_formation {C : Calculus} {J : Judgment} (h : Derives C ∅ J) :
    ∀ A B, J.term = .pi A B →
      Derives C ∅ ⟨J.context, A, Term.univ .type⟩ ∧
      ∃ s, Derives C ∅ ⟨A :: J.context, B, Term.univ s⟩ := by
  induction h with
  | hyp h => exact False.elim h
  | type => intro A B he; cases he
  | constant _ _ _ => intro A B he; cases he
  | var _ _ => intro A B he; cases he
  | @weak Γ t T D ht hD ih _ =>
    show ∀ A B, t.rename Nat.succ = .pi A B →
      Derives C ∅ ⟨D :: Γ, A, Term.univ .type⟩ ∧
      ∃ s, Derives C ∅ ⟨A :: D :: Γ, B, Term.univ s⟩
    intro A B he
    cases t with
    | sort _ => cases he
    | var _ => cases he
    | app _ _ => cases he
    | lam _ _ => cases he
    | pi A₀ B₀ =>
      cases he
      obtain ⟨hA, s, hB⟩ := ih A₀ B₀ rfl
      exact ⟨Derives.weak hA hD, s, weaken_beneath hB hA hD⟩
  | @pi Γ A B s hA hB _ _ => intro A' B' he; cases he; exact ⟨hA, s, hB⟩
  | lam _ _ _ _ => intro A B he; cases he
  | app _ _ _ _ => intro A B he; cases he
  | conv _ _ _ ih _ => exact ih

theorem type_correctness {C : Calculus} {J : Judgment} (h : Derives C ∅ J) :
    J.type = Term.univ .kind ∨ ∃ s, Derives C ∅ ⟨J.context, J.type, Term.univ s⟩ := by
  induction h with
  | hyp h => exact False.elim h
  | type => exact .inl rfl
  | @constant c A s hd hA _ => exact .inr ⟨s, hA⟩
  | var hA _ => exact .inr ⟨.type, Derives.weak hA hA⟩
  | @weak Γ t A D ht hD iht _ =>
    rcases iht with he | ⟨s, hs⟩
    · change A = Term.univ .kind at he
      exact .inl (by change A.rename Nat.succ = Term.univ .kind; rw [he]; rfl)
    · exact .inr ⟨s, Derives.weak hs hD⟩
  | @pi Γ A B s hA hB _ _ =>
    cases s with
    | kind => exact .inl rfl
    | type => exact .inr ⟨.kind, Derives.type.weaken_closed hA.contextOK⟩
  | @lam Γ A b B s hb hpi _ _ => exact .inr ⟨s, hpi⟩
  | @app Γ f a A B hf ha ihf _ =>
    rcases ihf with he | ⟨s, hs⟩
    · cases he
    · obtain ⟨_, r, hB⟩ := product_formation hs A B rfl
      exact .inr ⟨r, hB.substOne ha⟩
  | @conv Γ t A B s ht he hB _ _ => exact .inr ⟨s, hB⟩

theorem beta_product_compatible (declared : String → Term → Prop) :
    (Calculus.lf declared).ProductCompatible := by
  intro A B A' B' h
  have hb := (Calculus.lf_conversion_iff declared _ _).mp h
  obtain ⟨v, h₁, h₂⟩ := hb.join
  obtain ⟨X, Y, hv, hA, hB⟩ := Pseudo.reflTransGen_par_pi_inv h₁
  obtain ⟨X', Y', hv', hA', hB'⟩ := Pseudo.reflTransGen_par_pi_inv h₂
  have he : Pseudo.pi X Y = .pi X' Y' := hv.symm.trans hv'
  cases he
  exact ⟨beta_conversion ((Pseudo.reflTransGen_par_toConv hA).trans
      (Pseudo.reflTransGen_par_toConv hA').symm),
    beta_conversion ((Pseudo.reflTransGen_par_toConv hB).trans
      (Pseudo.reflTransGen_par_toConv hB').symm)⟩


theorem application_generation {C : Calculus} {J : Judgment} (h : Derives C ∅ J) :
    ∀ f a, J.term = .app f a →
      ∃ A B, Derives C ∅ ⟨J.context, f, .pi A B⟩ ∧
        Derives C ∅ ⟨J.context, a, A⟩ ∧ C.Conversion (B.substOne a) J.type ∧
        ∃ s, Derives C ∅ ⟨J.context, J.type, Term.univ s⟩ := by
  induction h with
  | hyp h => exact False.elim h
  | type => intro f a he; cases he
  | constant _ _ _ => intro f a he; cases he
  | var _ _ => intro f a he; cases he
  | @weak Γ t T D ht hD ih _ =>
    show ∀ f a, t.rename Nat.succ = .app f a →
      ∃ A B, Derives C ∅ ⟨D :: Γ, f, .pi A B⟩ ∧
      Derives C ∅ ⟨D :: Γ, a, A⟩ ∧ C.Conversion (B.substOne a) (T.rename Nat.succ) ∧
      ∃ s, Derives C ∅ ⟨D :: Γ, T.rename Nat.succ, Term.univ s⟩
    intro f a he
    cases t with
    | sort _ => cases he
    | var _ => cases he
    | lam _ _ => cases he
    | pi _ _ => cases he
    | app f₀ a₀ =>
      cases he
      obtain ⟨A, B, hf, ha, hc, s, hs⟩ := ih f₀ a₀ rfl
      refine ⟨A.rename Nat.succ, B.rename (Silmaril.DeBruijn.lift Nat.succ),
        Derives.weak hf hD, Derives.weak ha hD, ?_, s, Derives.weak hs hD⟩
      simpa only [Pseudo.rename_substOne] using hc.rename Nat.succ
  | pi _ _ _ _ => intro f a he; cases he
  | lam _ _ _ _ => intro f a he; cases he
  | @app Γ f a A B hf ha _ _ =>
    intro f' a' he
    cases he
    rcases type_correctness hf with he | ⟨s, hs⟩
    · cases he
    · obtain ⟨_, r, hB⟩ := product_formation hs A B rfl
      exact ⟨A, B, hf, ha, .refl _, r, hB.substOne ha⟩
  | @conv Γ t T U s ht hc hU ih _ =>
    intro f a he
    obtain ⟨A, B, hf, ha, heq, _⟩ := ih f a he
    exact ⟨A, B, hf, ha, .trans heq hc, s, hU⟩

theorem abstraction_generation {C : Calculus} {J : Judgment} (h : Derives C ∅ J) :
    ∀ A b, J.term = .lam A b →
      ∃ B s, Derives C ∅ ⟨A :: J.context, b, B⟩ ∧
        Derives C ∅ ⟨J.context, .pi A B, Term.univ s⟩ ∧
        C.Conversion (.pi A B) J.type ∧
        ∃ r, Derives C ∅ ⟨J.context, J.type, Term.univ r⟩ := by
  induction h with
  | hyp h => exact False.elim h
  | type => intro A b he; cases he
  | constant _ _ _ => intro A b he; cases he
  | var _ _ => intro A b he; cases he
  | @weak Γ t T D ht hD ih _ =>
    show ∀ A b, t.rename Nat.succ = .lam A b →
      ∃ B s, Derives C ∅ ⟨A :: D :: Γ, b, B⟩ ∧
      Derives C ∅ ⟨D :: Γ, .pi A B, Term.univ s⟩ ∧
      C.Conversion (.pi A B) (T.rename Nat.succ) ∧
      ∃ r, Derives C ∅ ⟨D :: Γ, T.rename Nat.succ, Term.univ r⟩
    intro A b he
    cases t with
    | sort _ => cases he
    | var _ => cases he
    | app _ _ => cases he
    | pi _ _ => cases he
    | lam A₀ b₀ =>
      cases he
      obtain ⟨B, s, hb, hpi, hc, r, hs⟩ := ih A₀ b₀ rfl
      exact ⟨B.rename (Silmaril.DeBruijn.lift Nat.succ), s,
        weaken_beneath hb hpi.pi_domain hD, Derives.weak hpi hD,
        hc.rename Nat.succ, r, Derives.weak hs hD⟩
  | pi _ _ _ _ => intro A b he; cases he
  | @lam Γ A b B s hb hpi _ _ =>
    intro A' b' he
    cases he
    exact ⟨B, s, hb, hpi, .refl _, s, hpi⟩
  | app _ _ _ _ => intro A b he; cases he
  | @conv Γ t T U s ht hc hU ih _ =>
    intro A b he
    obtain ⟨B, r, hb, hpi, heq, _⟩ := ih A b he
    exact ⟨B, r, hb, hpi, .trans heq hc, s, hU⟩

theorem head_beta_subject_reduction {C : Calculus} (hC : C.ProductCompatible)
    {Γ : List Term} {A b a T : Term}
    (h : Derives C ∅ ⟨Γ, .app (.lam A b) a, T⟩) :
    Derives C ∅ ⟨Γ, b.substOne a, T⟩ := by
  obtain ⟨D, E, hf, ha, he, s, hs⟩ := application_generation h _ _ rfl
  obtain ⟨B, r, hb, hpi, hp, _⟩ := abstraction_generation hf _ _ rfl
  obtain ⟨hAD, hBE⟩ := hC hp
  have haA : Derives C ∅ ⟨Γ, a, A⟩ := .conv ha hAD.symm hpi.pi_domain
  have ht : Derives C ∅ ⟨Γ, b.substOne a, B.substOne a⟩ := hb.substOne haA
  exact .conv ht (.trans (hBE.subst _) he) hs

end Silmaril.Proofs.Logic.TypeTheory.LambdaPi

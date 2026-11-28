module

public import Silmaril.SSA.Isotope.LetCase.HandledTrace.Category.Coproduct.Defs

public section

namespace Silmaril.Isotope.LetCase.HandledTrace.CoproductProofs

open LocallyNameless Silmaril.Isotope.Semantics Silmaril.Elgot.ITree

universe u v e s

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {D : τ → Type (e + 1)} [ProductModel D] [UnitModel D] [CoproductModel D] [EmptyModel D]
  {Events : Type e → Type e} {State : Type s}
  {M : InstructionModel D Φ (Tree Events)} {policy : Handler State Events}
  {A B C : τ}

theorem run_inl (a : D A) :
    (Program.inl (Φ := Φ) A B).run M a =
      pure ((CoproductModel.coprodEquiv A B).symm (.inl a)) :=
  pure_bind _ _

theorem run_inr (b : D B) :
    (Program.inr (Φ := Φ) A B).run M b =
      pure ((CoproductModel.coprodEquiv A B).symm (.inr b)) :=
  pure_bind _ _

set_option backward.isDefEq.respectTransparency false in
theorem run_desc (left : Program Φ A C) (right : Program Φ B C) (x : D (coprod A B)) :
    (left.desc right).run M x =
      Sum.elim (left.run M) (right.run M) (CoproductModel.coprodEquiv A B x) := by
  let env : BoundEnv D (.snoc .nil (coprod A B)) :=
    BoundEnv.snoc (β := .nil) (fun i => i.elim0) x
  change ((pure x : Tree Events (D (coprod A B))) >>= fun value =>
    match CoproductModel.coprodEquiv A B value with
    | .inl a => left.2.underBinder.denote D M (fun n => Empty.elim n) (env.snoc a)
    | .inr b => right.2.underBinder.denote D M (fun n => Empty.elim n) (env.snoc b)) = _
  rw [pure_bind]
  cases CoproductModel.coprodEquiv A B x with
  | inl a => exact Program.run_underBinder left x a
  | inr b => exact Program.run_underBinder right x b

theorem desc_mono {left left' : Program Φ A C} {right right' : Program Φ B C}
    (hl : Program.Refines M policy left left') (hr : Program.Refines M policy right right') :
    Program.Refines M policy (left.desc right) (left'.desc right') := by
  intro x state
  rw [run_desc, run_desc]
  cases CoproductModel.coprodEquiv A B x with
  | inl a => exact hl a state
  | inr b => exact hr b state

theorem refines_sum_iff {p q : Program Φ (coprod A B) C} :
    Program.Refines M policy p q ↔
      Program.Refines M policy ((Program.inl A B).seq p) ((Program.inl A B).seq q) ∧
      Program.Refines M policy ((Program.inr A B).seq p) ((Program.inr A B).seq q) := by
  constructor
  · intro h
    exact ⟨Program.seq_mono (.refl M policy _) h, Program.seq_mono (.refl M policy _) h⟩
  · rintro ⟨hl, hr⟩ x state
    obtain ⟨tag, rfl⟩ := (CoproductModel.coprodEquiv (D := D) A B).symm.surjective x
    cases tag with
    | inl a => simpa only [Program.run_seq, run_inl, pure_bind] using hl a state
    | inr b => simpa only [Program.run_seq, run_inr, pure_bind] using hr b state

private theorem equiv_of_run_eq {X Y : τ} {p q : Program Φ X Y}
    (eq : ∀ a, p.run M a = q.run M a) : (Program.setoid M policy X Y).r p q :=
  ⟨fun a _ => eq a ▸ .refl _, fun a _ => (eq a).symm ▸ .refl _⟩

theorem inl_desc (left : Program Φ A C) (right : Program Φ B C) :
    (Program.setoid M policy A C).r ((Program.inl A B).seq (left.desc right)) left := by
  apply equiv_of_run_eq
  intro a
  rw [Program.run_seq, run_inl, pure_bind, run_desc, Equiv.apply_symm_apply]
  rfl

theorem inr_desc (left : Program Φ A C) (right : Program Φ B C) :
    (Program.setoid M policy B C).r ((Program.inr A B).seq (left.desc right)) right := by
  apply equiv_of_run_eq
  intro b
  rw [Program.run_seq, run_inr, pure_bind, run_desc, Equiv.apply_symm_apply]
  rfl

theorem empty_hom_eq {C : Interface M policy} (f g : Arrow (Interface.zero (M := M) (policy := policy)) C) :
    f = g := by
  induction f, g using Quotient.inductionOn₂
  exact Quotient.sound ⟨fun a => (EmptyModel.emptyEquiv (D := D) a).elim,
    fun a => (EmptyModel.emptyEquiv (D := D) a).elim⟩

end Silmaril.Isotope.LetCase.HandledTrace.CoproductProofs

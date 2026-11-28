module

public import Silmaril.SSA.Isotope.LetCase.HandledTrace.Category.Tensor.Premonoidal.Defs

public section

namespace Silmaril.Isotope.LetCase.HandledTrace.PremonoidalProofs

open CategoryTheory Silmaril.Isotope.Semantics Silmaril.Elgot.ITree

universe u v e s

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {D : τ → Type (e + 1)} [ProductModel D] [UnitModel D] [CoproductModel D] [EmptyModel D]
  {Events : Type e → Type e} {State : Type s}
  {M : InstructionModel D Φ (Tree Events)} {policy : Handler State Events}
  {A B C F : τ}

local notation "pack[" A "," B "]" => Equiv.symm (ProductModel.productEquiv (D := D) A B)

theorem run_eq_left_pure {p : Program Φ A B} (q : Program Φ C F) (hp : p.HasPureRun M)
    (input : D (product A C)) : (p.leftTensor q).run M input = (p.rightTensor q).run M input := by
  obtain ⟨value, eval⟩ := hp
  obtain ⟨⟨a, c⟩, rfl⟩ := pack[A, C].surjective input
  simp only [Program.leftTensor, Program.rightTensor, Program.run_seq, Program.run_whiskerLeft,
    Program.run_whiskerRight, eval, bind_assoc, pure_bind]

theorem run_eq_right_pure (p : Program Φ A B) {q : Program Φ C F} (hq : q.HasPureRun M)
    (input : D (product A C)) : (p.leftTensor q).run M input = (p.rightTensor q).run M input := by
  obtain ⟨value, eval⟩ := hq
  obtain ⟨⟨a, c⟩, rfl⟩ := pack[A, C].surjective input
  simp only [Program.leftTensor, Program.rightTensor, Program.run_seq, Program.run_whiskerLeft,
    Program.run_whiskerRight, eval, bind_assoc, pure_bind]

theorem fst_pure (A B : τ) : (Program.fst (Φ := Φ) A B).HasPureRun M := by
  refine ⟨fun input => (ProductModel.productEquiv A B input).1, ?_⟩
  intro input
  obtain ⟨⟨a, b⟩, rfl⟩ := pack[A, B].surjective input
  simp only [Program.run_fst, Equiv.apply_symm_apply]

theorem snd_pure (A B : τ) : (Program.snd (Φ := Φ) A B).HasPureRun M := by
  refine ⟨fun input => (ProductModel.productEquiv A B input).2, ?_⟩
  intro input
  obtain ⟨⟨a, b⟩, rfl⟩ := pack[A, B].surjective input
  simp only [Program.run_snd, Equiv.apply_symm_apply]

theorem assoc_pure (A B C : τ) : (Program.assocHom (Φ := Φ) A B C).HasPureRun M := by
  refine ⟨fun input =>
    let parts := ProductModel.productEquiv (D := D) (product A B) C input
    let ab := ProductModel.productEquiv (D := D) A B parts.1
    pack[A, product B C] (ab.1, pack[B, C] (ab.2, parts.2)), ?_⟩
  intro input
  obtain ⟨⟨ab, c⟩, rfl⟩ := pack[product A B, C].surjective input
  obtain ⟨⟨a, b⟩, rfl⟩ := pack[A, B].surjective ab
  simp only [Program.run_assocHom, Equiv.apply_symm_apply]

theorem pentagon (A B C F : τ) :
    (Program.setoid M policy (product (product (product A B) C) F) (product A (product B (product C F)))).r
      (((Program.assocHom A B C).whiskerRight F).seq
        ((Program.assocHom A (product B C) F).seq ((Program.assocHom B C F).whiskerLeft A)))
      ((Program.assocHom (product A B) C F).seq (Program.assocHom A B (product C F))) := by
  apply Program.equiv_of_run_eq
  intro input
  obtain ⟨⟨abc, f⟩, rfl⟩ := pack[product (product A B) C, F].surjective input
  obtain ⟨⟨ab, c⟩, rfl⟩ := pack[product A B, C].surjective abc
  obtain ⟨⟨a, b⟩, rfl⟩ := pack[A, B].surjective ab
  simp only [Program.run_seq, Program.run_whiskerLeft, Program.run_whiskerRight, Program.run_assocHom, pure_bind]

theorem triangle (A B : τ) :
    (Program.setoid M policy (product (product A unit) B) (product A B)).r
      ((Program.assocHom A unit B).seq ((Program.snd unit B).whiskerLeft A))
      ((Program.fst A unit).whiskerRight B) := by
  apply Program.equiv_of_run_eq
  intro input
  obtain ⟨⟨au, b⟩, rfl⟩ := pack[product A unit, B].surjective input
  obtain ⟨⟨a, u⟩, rfl⟩ := pack[A, unit].surjective au
  simp only [Program.run_seq, Program.run_assocHom, Program.run_whiskerLeft, Program.run_whiskerRight,
    Program.run_snd, Program.run_fst, pure_bind]

theorem isCentral_of_pureRun {X Y : Interface M policy}
    {p : Program Φ X.ty Y.ty} (hp : p.HasPureRun M) :
    @PremonoidalCategory.IsCentral _ _ (tensorStruct (M := M) (policy := policy))
      X Y (Arrow.ofProgram p) := by
  constructor
  · intro _ _ f
    exact Quotient.inductionOn f fun q =>
      Quotient.sound (Program.equiv_of_run_eq (run_eq_left_pure q hp))
  · intro _ _ f
    exact Quotient.inductionOn f fun q =>
      Quotient.sound (Program.equiv_of_run_eq (run_eq_right_pure q hp))

end Silmaril.Isotope.LetCase.HandledTrace.PremonoidalProofs

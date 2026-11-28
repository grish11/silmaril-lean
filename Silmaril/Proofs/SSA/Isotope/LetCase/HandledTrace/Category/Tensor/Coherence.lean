module

public import Silmaril.SSA.Isotope.LetCase.HandledTrace.Category.Tensor.Coherence.Defs

public section

namespace Silmaril.Isotope.LetCase.HandledTrace.TensorCoherenceProofs

open Silmaril.Isotope.Semantics Silmaril.Elgot.ITree

universe u v e s

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {D : τ → Type (e + 1)} [ProductModel D] [UnitModel D] [CoproductModel D] [EmptyModel D]
  {Events : Type e → Type e} {State : Type s}
  {M : InstructionModel D Φ (Tree Events)} {policy : Handler State Events}
  {A B C : τ}

local notation "pack[" A "," B "]" => Equiv.symm (ProductModel.productEquiv (D := D) A B)
local notation "unitVal" => Equiv.symm (UnitModel.unitEquiv (D := D)) PUnit.unit

private theorem run_id (a : D A) : (Program.id (Φ := Φ) A).run M a = pure a := rfl

private theorem run_unit (a : D A) : (Program.unitValue (Φ := Φ) A).run M a = pure unitVal := rfl

theorem run_assocHom (a : D A) (b : D B) (c : D C) :
    (Program.assocHom (Φ := Φ) A B C).run M (pack[product A B, C] (pack[A, B] (a, b), c)) =
      pure (pack[A, product B C] (a, pack[B, C] (b, c))) := by
  simp only [Program.assocHom, Program.run_pair, Program.run_seq,
    Program.run_fst, Program.run_snd, pure_bind]

theorem run_assocInv (a : D A) (b : D B) (c : D C) :
    (Program.assocInv (Φ := Φ) A B C).run M (pack[A, product B C] (a, pack[B, C] (b, c))) =
      pure (pack[product A B, C] (pack[A, B] (a, b), c)) := by
  simp only [Program.assocInv, Program.run_pair, Program.run_seq,
    Program.run_fst, Program.run_snd, pure_bind]

theorem assoc_hom_inv (A B C : τ) :
    (Program.setoid M policy (product (product A B) C) (product (product A B) C)).r
      ((Program.assocHom A B C).seq (Program.assocInv A B C)) (Program.id _) := by
  apply Program.equiv_of_run_eq
  intro input
  obtain ⟨⟨ab, c⟩, rfl⟩ := pack[product A B, C].surjective input
  obtain ⟨⟨a, b⟩, rfl⟩ := pack[A, B].surjective ab
  simp only [Program.run_seq, run_assocHom, run_assocInv, pure_bind, run_id]

theorem assoc_inv_hom (A B C : τ) :
    (Program.setoid M policy (product A (product B C)) (product A (product B C))).r
      ((Program.assocInv A B C).seq (Program.assocHom A B C)) (Program.id _) := by
  apply Program.equiv_of_run_eq
  intro input
  obtain ⟨⟨a, bc⟩, rfl⟩ := pack[A, product B C].surjective input
  obtain ⟨⟨b, c⟩, rfl⟩ := pack[B, C].surjective bc
  simp only [Program.run_seq, run_assocHom, run_assocInv, pure_bind, run_id]

theorem assoc_first {A' : τ} (f : Program Φ A A') :
    (Program.setoid M policy (product (product A B) C) (product A' (product B C))).r
      (((f.whiskerRight B).whiskerRight C).seq (Program.assocHom A' B C))
      ((Program.assocHom A B C).seq (f.whiskerRight (product B C))) := by
  apply Program.equiv_of_run_eq
  intro input
  obtain ⟨⟨ab, c⟩, rfl⟩ := pack[product A B, C].surjective input
  obtain ⟨⟨a, b⟩, rfl⟩ := pack[A, B].surjective ab
  simp only [Program.run_seq, Program.run_whiskerRight, run_assocHom, bind_assoc, pure_bind]

theorem assoc_middle {B' : τ} (f : Program Φ B B') :
    (Program.setoid M policy (product (product A B) C) (product A (product B' C))).r
      (((f.whiskerLeft A).whiskerRight C).seq (Program.assocHom A B' C))
      ((Program.assocHom A B C).seq ((f.whiskerRight C).whiskerLeft A)) := by
  apply Program.equiv_of_run_eq
  intro input
  obtain ⟨⟨ab, c⟩, rfl⟩ := pack[product A B, C].surjective input
  obtain ⟨⟨a, b⟩, rfl⟩ := pack[A, B].surjective ab
  simp only [Program.run_seq, Program.run_whiskerLeft, Program.run_whiskerRight,
    run_assocHom, bind_assoc, pure_bind]

theorem assoc_last {C' : τ} (f : Program Φ C C') :
    (Program.setoid M policy (product (product A B) C) (product A (product B C'))).r
      ((f.whiskerLeft (product A B)).seq (Program.assocHom A B C'))
      ((Program.assocHom A B C).seq ((f.whiskerLeft B).whiskerLeft A)) := by
  apply Program.equiv_of_run_eq
  intro input
  obtain ⟨⟨ab, c⟩, rfl⟩ := pack[product A B, C].surjective input
  obtain ⟨⟨a, b⟩, rfl⟩ := pack[A, B].surjective ab
  simp only [Program.run_seq, Program.run_whiskerLeft, run_assocHom, bind_assoc, pure_bind]

theorem run_leftUnitorInv (a : D A) :
    (Program.leftUnitorInv (Φ := Φ) A).run M a = pure (pack[unit, A] (unitVal, a)) := by
  simp only [Program.leftUnitorInv, Program.run_pair, run_unit, run_id, pure_bind]

theorem run_rightUnitorInv (a : D A) :
    (Program.rightUnitorInv (Φ := Φ) A).run M a = pure (pack[A, unit] (a, unitVal)) := by
  simp only [Program.rightUnitorInv, Program.run_pair, run_unit, run_id, pure_bind]

theorem left_hom_inv (A : τ) :
    (Program.setoid M policy (product unit A) (product unit A)).r
      ((Program.snd unit A).seq (Program.leftUnitorInv A)) (Program.id _) := by
  apply Program.equiv_of_run_eq
  intro input
  obtain ⟨⟨u, a⟩, rfl⟩ := pack[unit, A].surjective input
  obtain ⟨⟨⟩, rfl⟩ := (UnitModel.unitEquiv (D := D)).symm.surjective u
  simp only [Program.run_seq, Program.run_snd, run_leftUnitorInv, run_id, pure_bind]

theorem left_inv_hom (A : τ) :
    (Program.setoid M policy A A).r
      ((Program.leftUnitorInv A).seq (Program.snd unit A)) (Program.id _) := by
  apply Program.equiv_of_run_eq
  intro a
  simp only [Program.run_seq, Program.run_snd, run_leftUnitorInv, run_id, pure_bind]

theorem right_hom_inv (A : τ) :
    (Program.setoid M policy (product A unit) (product A unit)).r
      ((Program.fst A unit).seq (Program.rightUnitorInv A)) (Program.id _) := by
  apply Program.equiv_of_run_eq
  intro input
  obtain ⟨⟨a, u⟩, rfl⟩ := pack[A, unit].surjective input
  obtain ⟨⟨⟩, rfl⟩ := (UnitModel.unitEquiv (D := D)).symm.surjective u
  simp only [Program.run_seq, Program.run_fst, run_rightUnitorInv, run_id, pure_bind]

theorem right_inv_hom (A : τ) :
    (Program.setoid M policy A A).r
      ((Program.rightUnitorInv A).seq (Program.fst A unit)) (Program.id _) := by
  apply Program.equiv_of_run_eq
  intro a
  simp only [Program.run_seq, Program.run_fst, run_rightUnitorInv, run_id, pure_bind]

theorem left_natural (f : Program Φ A B) :
    (Program.setoid M policy (product unit A) B).r
      ((f.whiskerLeft unit).seq (Program.snd unit B)) ((Program.snd unit A).seq f) := by
  apply Program.equiv_of_run_eq
  intro input
  obtain ⟨⟨u, a⟩, rfl⟩ := pack[unit, A].surjective input
  simp only [Program.run_seq, Program.run_whiskerLeft, Program.run_snd, bind_assoc, pure_bind, bind_pure]

theorem right_natural (f : Program Φ A B) :
    (Program.setoid M policy (product A unit) B).r
      ((f.whiskerRight unit).seq (Program.fst B unit)) ((Program.fst A unit).seq f) := by
  apply Program.equiv_of_run_eq
  intro input
  obtain ⟨⟨a, u⟩, rfl⟩ := pack[A, unit].surjective input
  simp only [Program.run_seq, Program.run_whiskerRight, Program.run_fst, bind_assoc, pure_bind, bind_pure]

end Silmaril.Isotope.LetCase.HandledTrace.TensorCoherenceProofs

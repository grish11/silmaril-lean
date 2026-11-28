module

public import Silmaril.SSA.Isotope.LetCase.HandledTrace.Category.Tensor.Coherence.Defs
import Silmaril.Proofs.SSA.Isotope.LetCase.HandledTrace.Category.Tensor.Coherence

@[expose] public section

namespace Silmaril.Isotope.LetCase.HandledTrace

open CategoryTheory Silmaril.Isotope.Semantics Silmaril.Elgot.ITree

universe u v e s

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {D : τ → Type (e + 1)} [ProductModel D] [UnitModel D] [CoproductModel D] [EmptyModel D]
  {Events : Type e → Type e} {State : Type s}
  {M : InstructionModel D Φ (Tree Events)} {policy : Handler State Events}

local notation "pack[" A "," B "]" => Equiv.symm (ProductModel.productEquiv (D := D) A B)
local notation "unitVal" => Equiv.symm (UnitModel.unitEquiv (D := D)) PUnit.unit

namespace Program

variable {A B C : τ}

theorem run_assocHom (a : D A) (b : D B) (c : D C) :
    (assocHom (Φ := Φ) A B C).run M (pack[product A B, C] (pack[A, B] (a, b), c)) =
      pure (pack[A, product B C] (a, pack[B, C] (b, c))) :=
  TensorCoherenceProofs.run_assocHom a b c

theorem run_assocInv (a : D A) (b : D B) (c : D C) :
    (assocInv (Φ := Φ) A B C).run M (pack[A, product B C] (a, pack[B, C] (b, c))) =
      pure (pack[product A B, C] (pack[A, B] (a, b), c)) :=
  TensorCoherenceProofs.run_assocInv a b c

theorem run_leftUnitorInv (a : D A) :
    (leftUnitorInv (Φ := Φ) A).run M a = pure (pack[unit, A] (unitVal, a)) :=
  TensorCoherenceProofs.run_leftUnitorInv a

theorem run_rightUnitorInv (a : D A) :
    (rightUnitorInv (Φ := Φ) A).run M a = pure (pack[A, unit] (a, unitVal)) :=
  TensorCoherenceProofs.run_rightUnitorInv a

end Program

namespace Arrow

/-- The pure reassociation isomorphism on native product types. -/
def associator (A B C : Interface M policy) : (A.tensor B).tensor C ≅ A.tensor (B.tensor C) where
  hom := ofProgram (Program.assocHom A.ty B.ty C.ty)
  inv := ofProgram (Program.assocInv A.ty B.ty C.ty)
  hom_inv_id := by exact Quotient.sound (TensorCoherenceProofs.assoc_hom_inv _ _ _)
  inv_hom_id := by exact Quotient.sound (TensorCoherenceProofs.assoc_inv_hom _ _ _)

/-- Naturality when only the first component carries a program. -/
theorem associator_natural_first {A A' : Interface M policy} (f : A ⟶ A')
    (B C : Interface M policy) :
    whiskerRight (whiskerRight f B) C ≫ (associator A' B C).hom =
      (associator A B C).hom ≫ whiskerRight f (B.tensor C) :=
  Quotient.inductionOn f fun p => Quotient.sound (TensorCoherenceProofs.assoc_first p)

/-- Naturality when only the middle component carries a program. -/
theorem associator_natural_middle (A : Interface M policy) {B B' : Interface M policy}
    (f : B ⟶ B') (C : Interface M policy) :
    whiskerRight (whiskerLeft A f) C ≫ (associator A B' C).hom =
      (associator A B C).hom ≫ whiskerLeft A (whiskerRight f C) :=
  Quotient.inductionOn f fun p => Quotient.sound (TensorCoherenceProofs.assoc_middle p)

/-- Naturality when only the last component carries a program. -/
theorem associator_natural_last (A B : Interface M policy) {C C' : Interface M policy}
    (f : C ⟶ C') :
    whiskerLeft (A.tensor B) f ≫ (associator A B C').hom =
      (associator A B C).hom ≫ whiskerLeft A (whiskerLeft B f) :=
  Quotient.inductionOn f fun p => Quotient.sound (TensorCoherenceProofs.assoc_last p)

/-- Drop the left unit through a pure projection and insert it by pure pairing. -/
def leftUnitor (A : Interface M policy) : Interface.tensorUnit.tensor A ≅ A where
  hom := ofProgram (Program.snd unit A.ty)
  inv := ofProgram (Program.leftUnitorInv A.ty)
  hom_inv_id := by exact Quotient.sound (TensorCoherenceProofs.left_hom_inv _)
  inv_hom_id := by exact Quotient.sound (TensorCoherenceProofs.left_inv_hom _)

/-- Drop the right unit through a pure projection and insert it by pure pairing. -/
def rightUnitor (A : Interface M policy) : A.tensor Interface.tensorUnit ≅ A where
  hom := ofProgram (Program.fst A.ty unit)
  inv := ofProgram (Program.rightUnitorInv A.ty)
  hom_inv_id := by exact Quotient.sound (TensorCoherenceProofs.right_hom_inv _)
  inv_hom_id := by exact Quotient.sound (TensorCoherenceProofs.right_inv_hom _)

end Arrow

/-- The left unit projections are natural for the fixed-left action. -/
def tensorLeftUnitIso :
    tensorLeft (Interface.tensorUnit (M := M) (policy := policy)) ≅ 𝟭 (Interface M policy) :=
  NatIso.ofComponents Arrow.leftUnitor (by
    intro A B f
    exact Quotient.inductionOn f fun p => Quotient.sound (TensorCoherenceProofs.left_natural p))

/-- The right unit projections are natural for the fixed-right action. -/
def tensorRightUnitIso :
    tensorRight (Interface.tensorUnit (M := M) (policy := policy)) ≅ 𝟭 (Interface M policy) :=
  NatIso.ofComponents Arrow.rightUnitor (by
    intro A B f
    exact Quotient.inductionOn f fun p => Quotient.sound (TensorCoherenceProofs.right_natural p))

end Silmaril.Isotope.LetCase.HandledTrace

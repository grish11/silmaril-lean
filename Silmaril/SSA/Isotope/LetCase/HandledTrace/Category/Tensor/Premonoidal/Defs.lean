module

public import Silmaril.SSA.Isotope.LetCase.HandledTrace.Category.Tensor.Coherence.Thms
public import Silmaril.Semantics.Categories.Thms

@[expose] public section

namespace Silmaril.Isotope.LetCase.HandledTrace

open CategoryTheory Silmaril.Isotope.Semantics Silmaril.Elgot.ITree

universe u v e s

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {D : τ → Type (e + 1)} [ProductModel D] [UnitModel D] [CoproductModel D] [EmptyModel D]
  {Events : Type e → Type e} {State : Type s}
  {M : InstructionModel D Φ (Tree Events)} {policy : Handler State Events}

namespace Program

variable {A B C F : τ}

/-- Every typed input returns the value of a pure function in the fixed model. -/
def HasPureRun (M : InstructionModel D Φ (Tree Events)) (p : Program Φ A B) : Prop :=
  ∃ value : D A → D B, ∀ a, p.run M a = pure (value a)

/-- The native tensor order that evaluates the left program first. -/
def leftTensor (p : Program Φ A B) (q : Program Φ C F) : Program Φ (product A C) (product B F) :=
  (p.whiskerRight C).seq (q.whiskerLeft B)

/-- The native tensor order that evaluates the right program first. -/
def rightTensor (p : Program Φ A B) (q : Program Φ C F) : Program Φ (product A C) (product B F) :=
  (q.whiskerLeft A).seq (p.whiskerRight F)

end Program

/-- Use left sequential tensor as the designated operation on pairs of arrows. -/
@[instance_reducible] def tensorStruct : MonoidalCategoryStruct (Interface M policy) where
  tensorObj := Interface.tensor
  whiskerLeft K {_ _} f := Arrow.whiskerLeft K f
  whiskerRight := Arrow.whiskerRight
  tensorHom p q := Arrow.whiskerRight p _ ≫ Arrow.whiskerLeft _ q
  tensorUnit := Interface.tensorUnit
  associator := Arrow.associator
  leftUnitor := Arrow.leftUnitor
  rightUnitor := Arrow.rightUnitor

end Silmaril.Isotope.LetCase.HandledTrace

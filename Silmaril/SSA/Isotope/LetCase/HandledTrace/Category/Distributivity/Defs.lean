module

public import Silmaril.SSA.Isotope.LetCase.HandledTrace.Category.Coproduct.Thms
public import Silmaril.SSA.Isotope.LetCase.HandledTrace.Category.Tensor.Premonoidal.Thms

@[expose] public section

namespace Silmaril.Isotope.LetCase.HandledTrace.Program

open LocallyNameless

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- Destructure a product and carry its left component into the selected arm. -/
def distribLeft (K A B : τ) :
    Program Φ (product K (coprod A B)) (coprod (product K A) (product K B)) :=
  ⟨.let₂ (.bv 0) (.case (.bv 0) (.inl (.pair (.bv 2) (.bv 0))) (.inr (.pair (.bv 2) (.bv 0)))),
    .let₂ .bv (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv)))⟩

/-- Destructure a product and carry its right component into the selected arm. -/
def distribRight (A B K : τ) :
    Program Φ (product (coprod A B) K) (coprod (product A K) (product B K)) :=
  ⟨.let₂ (.bv 0) (.case (.bv 1) (.inl (.pair (.bv 0) (.bv 1))) (.inr (.pair (.bv 0) (.bv 1)))),
    .let₂ .bv (.case .bv (.inl (.pair .bv .bv)) (.inr (.pair .bv .bv)))⟩

/-- Case on the distributed sum and put the tag beside the retained left value. -/
def mergeLeft (K A B : τ) :
    Program Φ (coprod (product K A) (product K B)) (product K (coprod A B)) :=
  ((inl A B).whiskerLeft K).desc ((inr A B).whiskerLeft K)

/-- Case on the distributed sum and put the tag beside the retained right value. -/
def mergeRight (A B K : τ) :
    Program Φ (coprod (product A K) (product B K)) (product (coprod A B) K) :=
  ((inl A B).whiskerRight K).desc ((inr A B).whiskerRight K)

end Silmaril.Isotope.LetCase.HandledTrace.Program

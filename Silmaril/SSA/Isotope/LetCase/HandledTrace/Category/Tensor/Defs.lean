module

public import Silmaril.SSA.Isotope.LetCase.HandledTrace.Category.Thms

@[expose] public section

namespace Silmaril.Isotope.LetCase.HandledTrace

open CategoryTheory LocallyNameless Silmaril.Isotope.Semantics Silmaril.Elgot.ITree

universe u v e s

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {D : τ → Type (e + 1)} [ProductModel D] [UnitModel D] [CoproductModel D] [EmptyModel D]
  {Events : Type e → Type e} {State : Type s}
  {M : InstructionModel D Φ (Tree Events)} {policy : Handler State Events}

namespace Program

/-- Destructure the typed input and return its left component. -/
def fst (A B : τ) : Program Φ (product A B) A :=
  ⟨.let₂ (.bv 0) (.bv 1), .let₂ .bv .bv⟩

/-- Destructure the typed input and return its right component. -/
def snd (A B : τ) : Program Φ (product A B) B :=
  ⟨.let₂ (.bv 0) (.bv 0), .let₂ .bv .bv⟩

/-- The native pair syntax evaluates its left operand before its right operand
at the original input. -/
def pair {A B C : τ} (left : Program Φ A B) (right : Program Φ A C) :
    Program Φ A (product B C) :=
  ⟨.pair left.1 right.1, .pair left.2 right.2⟩

/-- Keep the left input and run the given program on the right input. -/
def whiskerLeft {A B : τ} (K : τ) (p : Program Φ A B) :
    Program Φ (product K A) (product K B) :=
  (fst K A).pair ((snd K A).seq p)

/-- Run the given program on the left input and keep the right input. -/
def whiskerRight {A B : τ} (p : Program Φ A B) (K : τ) :
    Program Φ (product A K) (product B K) :=
  ((fst A K).seq p).pair (snd A K)

end Program

namespace Interface

/-- The native product type at this fixed model and policy. -/
def tensor (A B : Interface M policy) : Interface M policy := ⟨product A.ty B.ty⟩

end Interface
end Silmaril.Isotope.LetCase.HandledTrace

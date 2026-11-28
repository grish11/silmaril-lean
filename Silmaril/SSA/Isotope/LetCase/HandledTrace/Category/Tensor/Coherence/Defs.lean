module

public import Silmaril.SSA.Isotope.LetCase.HandledTrace.Category.Tensor.Thms

@[expose] public section

namespace Silmaril.Isotope.LetCase.HandledTrace

open Silmaril.Isotope.Semantics Silmaril.Elgot.ITree

universe u v e s

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {D : τ → Type (e + 1)} [ProductModel D] [UnitModel D] [CoproductModel D] [EmptyModel D]
  {Events : Type e → Type e} {State : Type s}
  {M : InstructionModel D Φ (Tree Events)} {policy : Handler State Events}

namespace Interface

/-- The native unit type. -/
def tensorUnit : Interface M policy := ⟨unit⟩

end Interface

namespace Program

/-- The written unit value, independent of the input slot. -/
def unitValue (A : τ) : Program Φ A (unit : τ) := ⟨.unit, .unit⟩

/-- Reassociate the three projected input components by pure pairing. -/
def assocHom (A B C : τ) : Program Φ (product (product A B) C) (product A (product B C)) :=
  let ab := fst (product A B) C
  (ab.seq (fst A B)).pair ((ab.seq (snd A B)).pair (snd (product A B) C))

/-- Reassociate in the opposite direction by pure pairing. -/
def assocInv (A B C : τ) : Program Φ (product A (product B C)) (product (product A B) C) :=
  let bc := snd A (product B C)
  ((fst A (product B C)).pair (bc.seq (fst B C))).pair (bc.seq (snd B C))

def leftUnitorInv (A : τ) : Program Φ A (product unit A) :=
  (unitValue A).pair (id A)

def rightUnitorInv (A : τ) : Program Φ A (product A unit) :=
  (id A).pair (unitValue A)

end Program
end Silmaril.Isotope.LetCase.HandledTrace

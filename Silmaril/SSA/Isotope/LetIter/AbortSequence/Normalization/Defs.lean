module

public import Silmaril.SSA.Isotope.LetIter.AbortSequence.Defs

/-! # Sequencing of empty elimination in LetIter terms -/

@[expose] public section

universe v w

namespace Silmaril.Isotope.LetIter.LocallyNameless.AbortNormalization

variable {ν : Type w} {Φ : Type v}

/-- Sequence a normalized empty scrutinee before eliminating the newest variable. -/
def sequenceAborts : {n : Nat} → Tm ν Φ n → Tm ν Φ n
  | _, .fv x => .fv x
  | _, .bv i => .bv i
  | _, .op f a => .op f (sequenceAborts a)
  | _, .let₁ a b => .let₁ (sequenceAborts a) (sequenceAborts b)
  | _, .unit => .unit
  | _, .pair a b => .pair (sequenceAborts a) (sequenceAborts b)
  | _, .let₂ a b => .let₂ (sequenceAborts a) (sequenceAborts b)
  | _, .inl a => .inl (sequenceAborts a)
  | _, .inr a => .inr (sequenceAborts a)
  | _, .case a b c => .case (sequenceAborts a) (sequenceAborts b) (sequenceAborts c)
  | _, .abort a => .let₁ (sequenceAborts a) (.abort (.bv 0))
  | _, .iter a b => .iter (sequenceAborts a) (sequenceAborts b)

end Silmaril.Isotope.LetIter.LocallyNameless.AbortNormalization

module

public import Silmaril.Logic.TypeTheory.LambdaPi.Institution.Defs

@[expose] public section

namespace Silmaril.Logic.TypeTheory.LambdaPi

/-- Actual typing inference is sound for closed-theory models. -/
theorem Calculus.logic_sound (C : Calculus) : C.logic.Sound := by
  intro S H J h
  exact (Silmaril.Logic.Institution.Syntactic.derives_iff_entails C.entailment H J).mp h

/-- Generated theories witness completeness of this syntactic model class. -/
theorem Calculus.logic_complete (C : Calculus) : C.logic.Complete := by
  intro S H J h
  exact (Silmaril.Logic.Institution.Syntactic.derives_iff_entails C.entailment H J).mpr h

end Silmaril.Logic.TypeTheory.LambdaPi

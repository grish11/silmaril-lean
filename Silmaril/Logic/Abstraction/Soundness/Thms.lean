module

public import Silmaril.Logic.Abstraction.Soundness.Defs
public import Silmaril.Logic.Abstraction.Thms
public import Mathlib.Data.Set.Finite.Basic
import Silmaril.Proofs.Logic.Abstraction.Soundness

@[expose] public section

namespace Silmaril.Logic.Abstraction

variable {S : Signature}

/-- Every derivable judgment has a finite premise set. -/
theorem Derives.finite {theory : Set (Rule S)} {Γ : Set (Premise S)} {t : Term S 0}
    (h : Derives theory Γ t) : Γ.Finite :=
  Proofs.Logic.Abstraction.Soundness.finite h

/-- Appendix C soundness for every model with admissible valuations, including general models. -/
theorem Rule.Derivable.sound {theory : Set (Rule S)} {r : Rule S}
    (h : r.Derivable theory) (M : Model S) (hM : ∀ a ∈ theory, M.Sat a) : M.Sat r :=
  Proofs.Logic.Abstraction.Soundness.sat h M hM

/-- A derivable rule is a semantic consequence of the presentation at its signature. -/
theorem Rule.Derivable.entails {theory : Set (Rule S)} {r : Rule S}
    (h : r.Derivable theory) : (institution.obj S).Entails theory r :=
  fun M hM => h.sound M hM

end Silmaril.Logic.Abstraction

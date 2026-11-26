module

public import Silmaril.SSA.Isotope.Institution.Relational.Inclusions.Thms

/-! # Relational institutions for the exact sequential let family -/

public section

namespace Silmaril.Isotope.Institution.Relational

open Silmaril.Logic.Institution Semantics

universe u v

variable {τ ε ν : Type u} [DecidableEq ν] [TypeFormers τ]
variable (D : τ → Type v) [ProductModel D] [UnitModel D] [CoproductModel D] (Γ : Ctx ν τ)

/-- LetSeq and LetCase have the same models and reducts on the common value structure. -/
theorem letSeq_modelFunctor_eq_letCase :
    modelFunctor (LetSeq.institution (ε := ε) D Γ) =
      modelFunctor (LetCase.institution (ε := ε) D Γ) := rfl

/-- LetCase and LetIter have the same models and reducts. -/
theorem letCase_modelFunctor_eq_letIter :
    modelFunctor (LetCase.institution (ε := ε) D Γ) =
      modelFunctor (LetIter.institution (ε := ε) D Γ) := rfl

end Silmaril.Isotope.Institution.Relational

module

public import Silmaril.Logic.Institution.Examples.FirstOrder

@[expose] public section
namespace Silmaril.Logic.FirstOrder.FiniteConnectives
open Silmaril.Logic.Institution.Examples
variable {Sg : FOL.Signature} {k : Nat} {Γ : Fin k → Sg.S}

/-- Derived actual FOL disjunction. -/
def disj (p q : FOL.Formula Sg Γ) : FOL.Formula Sg Γ := .not (.and (.not p) (.not q))

/-- A finite disjunction; the empty family is false syntax `not true`. -/
def finiteOr : List (FOL.Formula Sg Γ) → FOL.Formula Sg Γ
  | [] => .not .tt
  | p :: ps => disj p (finiteOr ps)

/-- A finite conjunction; the empty family is true syntax. -/
def finiteAnd : List (FOL.Formula Sg Γ) → FOL.Formula Sg Γ
  | [] => .tt
  | p :: ps => .and p (finiteAnd ps)

end Silmaril.Logic.FirstOrder.FiniteConnectives

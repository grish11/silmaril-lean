module

public import Silmaril.Games.Abstract.SessionIter2.Defs

/-!
# Session iteration of total bodies: call prefixes (definitions)

For a session loop body `t : ObsTriple E S A ((B ⊕ A) ⊕ PUnit)` (`SessionIter.iterS`),
`contSatP t s a` is the set of call prefixes of the body reached after a finite chain of
continuing returns (`SessionIter2.ContS`) from `(s, a)`, with the log of the chain in front.

Theorems in `Silmaril.Games.Abstract.SessionIter3.Thms`.
-/

@[expose] public section

namespace Silmaril.Games.Abstract.SessionIter3

open Silmaril.Games Silmaril.Games.Abstract.StratObs Silmaril.Games.Abstract.SessionIter2

universe u

variable {E : Sig.{u}} {S A B : Type u}

/-- **Call prefixes after continuing iterations**: a finite chain of continuing body returns
from `(s, a)` with log `c₁`, then a call prefix `(c₂, m)` of the body, giving `(c₁ ++ c₂, m)`. -/
def contSatP (t : ObsTriple E S A ((B ⊕ A) ⊕ PUnit.{u + 1})) : Pending E S A := fun s a =>
  {x | ∃ c₁ s' a' c₂, ContS t s a c₁ s' a' ∧ (c₂, x.2) ∈ satP t s' a' ∧ x.1 = c₁ ++ c₂}

end Silmaril.Games.Abstract.SessionIter3

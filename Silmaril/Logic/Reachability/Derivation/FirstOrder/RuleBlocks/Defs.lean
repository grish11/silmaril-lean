module

public import Silmaril.Logic.Reachability.Derivation.FirstOrder.Defs
public import Silmaril.Logic.FirstOrder.FiniteConnectives.Thms

@[expose] public section
namespace Silmaril.Logic.Reachability.Derivation.FirstOrder
open Silmaril.Logic.Institution.Examples
open Silmaril.Logic.FirstOrder.Variables
variable {Sg : FOL.Signature}

/-- Actual formula syntax of a rule with its own independently valued telescope. -/
abbrev RulePattern (cfg : Sg.S) (xs : List Sg.S) :=
  Pattern Sg cfg (blockContext emptyContext xs)

/-- Lift only the rule's variables into the prefixed rule block, preserving cfg0.
Outer claim captures are fresh and remain absent from this actual formula. -/
def liftRule {k : Nat} (cfg : Sg.S) (Γ : Fin k → Sg.S) (xs : List Sg.S)
    (p : RulePattern cfg xs) : Pattern Sg cfg (blockContext Γ xs) :=
  rename (liftIndex (prefixIndex xs)) (capturedPrefixSort cfg Γ xs) p

end Silmaril.Logic.Reachability.Derivation.FirstOrder

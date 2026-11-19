module

public import Silmaril.Semantics.Region.Queries.Thms
public import Silmaril.Semantics.Region.Examples.Thms

@[expose] public section
namespace Silmaril.Semantics.Region.Queries.Examples

/-- Explicit nondeterminism: an entry may leave at either 1 or 2. -/
def fork : TransitionSystem Nat Nat Empty Empty where
  pc := id
  step s es t := s = 0 ∧ es = [] ∧ (t = 1 ∨ t = 2)
  halt _ _ := False

end Silmaril.Semantics.Region.Queries.Examples

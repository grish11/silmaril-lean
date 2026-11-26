module

import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Thms
import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Thms

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Tests

open CategoryTheory CategoryTheory.Limits
open EmptySequencing

private abbrev exampleEquation := equation [.unit]

/-- The two rendered terms share the original two-position exit interface.
Only the empty scrutinee changes how it is sequenced. -/
example :
    (grammarCase exampleEquation).2.1.1 =
      .let₁ (.abort (.op true .unit)) (.let₁ (.bv 0) (.inl (.bv 0))) ∧
    (grammarCase exampleEquation).2.2.1 =
      .let₁ (.let₁ (.op true .unit) (.abort (.bv 0))) (.let₁ (.bv 0) (.inl (.bv 0))) :=
  ⟨rfl, rfl⟩

example : ¬ Derivable false exampleEquation := unprovable [.unit]

/-- The reverse compiler supplies actual ranked tables whose exact forward
outputs are this pair of terms. -/
example : grammarCase (readGrammar (numberGrammar exampleEquation)) = grammarCase exampleEquation :=
  grammarCase_roundTrip exampleEquation

variable {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] {J : V ⥤ C} [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J]

example (K : (rankedRoom J signature).Mod) :
    (rankedRoom J signature).Sat K (numberGrammar exampleEquation) :=
  (sat_numberGrammar K exampleEquation).mpr (sat [.unit] _)

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Tests

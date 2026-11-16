module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Rules.Defs

@[expose] public section

/-! # Closed derivations in the W extension

`Leaf` has one constructor with no recursive positions. The examples below
exercise formation, introduction, dependent elimination and its computation rule
in the object calculus, with no judgment hypotheses.
-/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Examples

/-- The W-type of one nullary constructor. -/
def Leaf {k : ℕ} : Tm k := .wtype .unit .empty

/-- The unique possible child map has empty domain. -/
def noChildren {k : ℕ} : Tm k := .abs .empty (.absurd Leaf (.bv 0))

/-- A closed inhabitant of the nullary W-type. -/
def leaf {k : ℕ} : Tm k := .sup .unit .empty .star noChildren

/-- The constant-unit elimination step, ignoring its three arguments. -/
def unitStep {k : ℕ} : Tm k :=
  .abs .unit (.abs (.pi .empty Leaf) (.abs (.pi .empty .unit) .star))

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Examples

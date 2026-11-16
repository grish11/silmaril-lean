module

public import Silmaril.Logic.TypeTheory.CIC.Semantics.Defs

@[expose] public section

/-! # Pulling explicit global assignments through universe substitution -/

namespace Silmaril.Logic.TypeTheory.CIC.SetSemantics

universe u

/-- A source global occurrence is assigned the value of its universe-substituted target occurrence.

This reindexes existing optional assignments. It supplies no missing value,
no inhabitant and no declaration-soundness assumption.
-/
def GlobalValues.pullbackUniverses (σ : LevelName → Universe) (globals : GlobalValues.{u}) : GlobalValues.{u} where
  constant name ui := globals.constant name (ui.map (UniverseExpr.subst σ))
  inductiveType reference ui := globals.inductiveType reference (ui.map (UniverseExpr.subst σ))
  constructor reference index ui := globals.constructor reference index (ui.map (UniverseExpr.subst σ))

end Silmaril.Logic.TypeTheory.CIC.SetSemantics

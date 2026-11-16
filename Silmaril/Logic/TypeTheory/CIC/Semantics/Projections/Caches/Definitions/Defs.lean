module

public import Silmaril.Logic.TypeTheory.CIC.Semantics.Constructors.Definitions.Thms
public import Silmaril.Logic.TypeTheory.CIC.Semantics.Projections.Caches.Thms

@[expose] public section

namespace Silmaril.Logic.TypeTheory.CIC.SetSemantics

universe u

/-- The actual tagged record tuples whose runtime parameter prefix is fixed.
Source definitions occur in the computed telescope data, not in this prefix. -/
noncomputable def SourceTelescopeData.recordLayer {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}}
    {globals : GlobalValues.{u}} {values : LocalValues.{u}} {declarations : Context}
    (data : SourceTelescopeData ρ universes globals values declarations)
    (parameterCount : ℕ) (parameters : LocalValues.{u}) : Value.{u} :=
  ZFSet.range fun xs : {xs : data.telescope.Points // (data.telescope.arguments xs).take parameterCount = parameters} =>
    constructorValue 0 (data.telescope.arguments xs.val)

end Silmaril.Logic.TypeTheory.CIC.SetSemantics

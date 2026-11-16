module

public import Silmaril.Logic.TypeTheory.CIC.Semantics.Constructors.Recursive.Defs
public import Silmaril.Logic.TypeTheory.CIC.Semantics.Substitution.Thms

@[expose] public section

namespace Silmaril.Logic.TypeTheory.CIC.SetSemantics

universe u

/-- Actual oldest-first source domains and local definition values. Definitions
occupy source binders but contribute no runtime constructor argument. No
semantic field telescope or interpretation of a smashed cache is supplied. -/
inductive SourceTelescopeData (ρ : LevelName → ℕ) (universes : ℕ → Value.{u})
    (globals : GlobalValues.{u}) : LocalValues.{u} → Context → Type (u + 1) where
  | nil {values} : SourceTelescopeData ρ universes globals values []
  | assumption {values na type declarations} (A : Value.{u})
      (htype : Evaluates ρ universes globals values type A)
      (rest : ∀ x : A, SourceTelescopeData ρ universes globals (x.val :: values) declarations) :
      SourceTelescopeData ρ universes globals values ({ binder := na, type := type } :: declarations)
  | definition {values na value type declarations} (A a : Value.{u})
      (htype : Evaluates ρ universes globals values type A)
      (hvalue : Evaluates ρ universes globals values value a) (hmember : a ∈ A)
      (rest : SourceTelescopeData ρ universes globals (a :: values) declarations) :
      SourceTelescopeData ρ universes globals values
        ({ binder := na, type := type, value := some value } :: declarations)

/-- Compute the dependent runtime telescope, retaining only source assumptions. -/
def SourceTelescopeData.telescope {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}}
    {globals : GlobalValues.{u}} {values : LocalValues.{u}} {declarations : Context} :
    SourceTelescopeData ρ universes globals values declarations → ValueTelescope.{u}
  | .nil => .nil
  | .assumption A _ rest => .bind A (fun x => (rest x).telescope)
  | .definition _ _ _ _ _ rest => rest.telescope

/-- All source values, including evaluated definitions, in application order. -/
def SourceTelescopeData.sourceValues {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}}
    {globals : GlobalValues.{u}} {values : LocalValues.{u}} {declarations : Context}
    (data : SourceTelescopeData ρ universes globals values declarations) : data.telescope.Points → LocalValues.{u} :=
  match data with
  | .nil => fun _ => []
  | .assumption _ _ rest => fun xs => xs.1.val :: (rest xs.1).sourceValues xs.2
  | .definition _ a _ _ _ rest => fun xs => a :: rest.sourceValues xs

end Silmaril.Logic.TypeTheory.CIC.SetSemantics

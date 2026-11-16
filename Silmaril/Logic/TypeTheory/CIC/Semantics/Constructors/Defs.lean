module

public import Silmaril.Logic.TypeTheory.CIC.Semantics.Defs

@[expose] public section

/-! # Actual dependent constructor telescopes and their tagged value domains

Each binder ranges over an actual ZFSet. Points therefore form a small
dependent tuple type, and its tagged image is an actual ZFSet with proved
inversion. This constructs a constructor layer over supplied field domains;
it does not construct a fixed point for every strictly-positive declaration.
-/

namespace Silmaril.Logic.TypeTheory.CIC.SetSemantics

universe u

inductive ValueTelescope : Type (u + 1) where
  | nil
  | bind (domain : Value.{u}) (rest : domain → ValueTelescope)

def ValueTelescope.Points : ValueTelescope.{u} → Type (u + 1)
  | .nil => PUnit
  | .bind A rest => (x : A) × (rest x).Points

instance ValueTelescope.small_points (T : ValueTelescope.{u}) : Small.{u} T.Points := by
  induction T with
  | nil =>
      simp only [ValueTelescope.Points]
      infer_instance
  | bind A rest ih =>
      have (x : A) : Small.{u} (rest x).Points := ih x
      exact small_sigma _

def ValueTelescope.arguments : (T : ValueTelescope.{u}) → T.Points → LocalValues.{u}
  | .nil, _ => []
  | .bind _ rest, ⟨x, xs⟩ => (x : Value.{u}) :: (rest x).arguments xs

noncomputable def ValueTelescope.pi : (T : ValueTelescope.{u}) → (T.Points → Value.{u}) → Value.{u}
  | .nil, B => B PUnit.unit
  | .bind A rest, B => tracePi A (fun x => (rest x).pi (fun xs => B ⟨x, xs⟩))

noncomputable def ValueTelescope.trace : (T : ValueTelescope.{u}) → (T.Points → Value.{u}) → Value.{u}
  | .nil, f => f PUnit.unit
  | .bind A rest, f => traceLambda A (fun x => (rest x).trace (fun xs => f ⟨x, xs⟩))

/-- Every declaration is interpreted in its actual preceding source scope; telescopes are oldest-first. -/
inductive InterpretsTelescope (ρ : LevelName → ℕ) (universes : ℕ → Value.{u}) (globals : GlobalValues.{u}) :
    LocalValues.{u} → Context → ValueTelescope.{u} → Prop where
  | nil {values} : InterpretsTelescope ρ universes globals values [] .nil
  | assumption {values na type declarations A rest} : Evaluates ρ universes globals values type A →
      (∀ x : A, InterpretsTelescope ρ universes globals ((x : Value.{u}) :: values) declarations (rest x)) →
      InterpretsTelescope ρ universes globals values ({ binder := na, type := type } :: declarations) (.bind A rest)

/-- Finite tagged constructor images over genuine dependent tuples, with fixed parameter values. -/
noncomputable def constructorLayer (count : ℕ) (telescopes : Fin count → ValueTelescope.{u})
    (parameters : LocalValues.{u}) : Value.{u} :=
  ZFSet.range fun point : (index : Fin count) × (telescopes index).Points =>
    constructorValue point.1.val (parameters ++ (telescopes point.1).arguments point.2)

noncomputable def constructorLayerPoint {count : ℕ} (telescopes : Fin count → ValueTelescope.{u})
    (parameters : LocalValues.{u}) (index : Fin count) (xs : (telescopes index).Points) :
    ↥(constructorLayer count telescopes parameters) :=
  ⟨constructorValue index.val (parameters ++ (telescopes index).arguments xs),
    ZFSet.mem_range.mpr ⟨⟨index, xs⟩, rfl⟩⟩

end Silmaril.Logic.TypeTheory.CIC.SetSemantics

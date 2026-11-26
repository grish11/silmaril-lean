module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton.Thms
public import Mathlib.CategoryTheory.Category.Cat

/-! # Seed-parametric raw singleton homs with branch normalization -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.Singleton

open CategoryTheory
open OrderedPairSingleton (Rep)

/-- A seed together with the exact normalization criterion for its raw relation. -/
structure NormalizedSeed (τ : Type u) [TypeFormers τ] (Φ : Type v) [HasTy Φ τ] where
  step : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop
  /-- The raw generators may have unbound branch arguments. -/
  rawStep : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop := AddBinding step
  eqv_iff_normalized {Γ r s L} (hr : HasType Γ r L) (hs : HasType Γ s L) :
    Extension.Eqv rawStep Γ r s L ↔
      Extension.Eqv step Γ r.bindBranchArguments s.bindBranchArguments L

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] (S : NormalizedSeed τ Φ)
  {A B : τ}

def rawSetoid (A B : τ) : Setoid (Rep (Φ := Φ) A B) where
  r r s := Extension.Eqv S.rawStep [A] r.val s.val [B]
  iseqv := ⟨fun r => Extension.Eqv.refl r.property, Extension.Eqv.symm, Extension.Eqv.trans⟩

abbrev RawHom (A B : τ) := Quotient (rawSetoid S A B)

def rawClass {r : Region Φ} (hr : HasType [A] r [B]) : RawHom S A B :=
  Quotient.mk _ ⟨r, hr⟩

open Paper.Extension.Singleton (ofType ofRegion ofRegion_eq_iff)

/-- The map is branch normalization on exactly typed representatives. -/
def normalizeHom (f : RawHom S A B) : ofType S.step A ⟶ ofType S.step B :=
  Quotient.liftOn f (fun r => ofRegion S.step r.property.bindBranchArguments)
    (fun r s e => (ofRegion_eq_iff S.step r.property.bindBranchArguments s.property.bindBranchArguments).mpr
      ((S.eqv_iff_normalized r.property s.property).mp e))

/-- The identity representative is the literal variable branch. -/
def identity (A : τ) : RawHom S A A :=
  rawClass S (.br (ℓ := 0) rfl (.var (i := 0) rfl))

/-- Objects are syntax types at the selected seed. -/
structure RawTypeCategory (S : NormalizedSeed τ Φ) where
  as : τ

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.Singleton

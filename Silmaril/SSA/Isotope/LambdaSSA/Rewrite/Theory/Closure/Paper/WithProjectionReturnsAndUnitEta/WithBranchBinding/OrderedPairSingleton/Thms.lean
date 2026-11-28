module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OrderedPairBranchBinding

/-! # The raw singleton category and its normalization functor -/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton

open CategoryTheory
open Paper.Extension.Singleton (ofType ofRegion)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

local notation "Seed" => WithPairReturns.JoinedStep (τ := τ) (Φ := Φ) pe
local notation "Guarded" => Extension.Singleton.TypeCategory Seed
local notation "G" => ofType (Φ := Φ) Seed

variable {A B C : τ}

theorem normalize_guarded {r : Region Φ} (hr : ValueBranches [A] r [B]) :
    normalizeHom pe (rawClass pe hr.hasType) = ofRegion Seed hr :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OrderedPairBranchBinding.normalize_guarded pe hr

theorem normalizeHom_injective : Function.Injective (normalizeHom (Φ := Φ) pe (A := A) (B := B)) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OrderedPairBranchBinding.normalizeHom_injective pe

theorem normalizeHom_surjective : Function.Surjective (normalizeHom (Φ := Φ) pe (A := A) (B := B)) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OrderedPairBranchBinding.normalizeHom_surjective pe

/-- The literal bind-first composite commutes with normalization for any guarded quotient seed. -/
theorem ofRegion_bind_compRep (Step : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)
    (r : Rep (Φ := Φ) A B) (s : Rep (Φ := Φ) B C) :
    ofRegion Step (composeRep r s).property.bindBranchArguments =
      ofRegion Step r.property.bindBranchArguments ≫ ofRegion Step s.property.bindBranchArguments :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OrderedPairBranchBinding.ofRegion_bind_compRep Step r s

theorem composeRep_respects {r r' : Rep (Φ := Φ) A B} {s s' : Rep (Φ := Φ) B C}
    (hr : (rawSetoid pe A B).r r r') (hs : (rawSetoid pe B C).r s s') :
    (rawSetoid pe A C).r (composeRep r s) (composeRep r' s') :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OrderedPairBranchBinding.composeRep_respects pe hr hs

/-- Compose the literal representatives by binding the producer before substituting the consumer. -/
def compose (f : RawHom (Φ := Φ) pe A B) (g : RawHom (Φ := Φ) pe B C) : RawHom (Φ := Φ) pe A C :=
  Quotient.map₂ composeRep (fun _ _ hr _ _ hs => composeRep_respects pe hr hs) f g

@[simp] theorem normalize_identity :
    normalizeHom pe (identity (Φ := Φ) pe A) = 𝟙 (G A) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OrderedPairBranchBinding.normalize_identity pe

@[simp] theorem normalize_compose (f : RawHom (Φ := Φ) pe A B) (g : RawHom (Φ := Φ) pe B C) :
    normalizeHom pe (compose pe f g) = normalizeHom pe f ≫ normalizeHom pe g :=
  Quotient.inductionOn₂ f g (Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OrderedPairBranchBinding.normalize_compRep pe)

-- The comparison proves the category laws for operations already defined on representatives.
instance rawCategory : Category.{v} (RawTypeCategory (τ := τ) Φ pe) where
  Hom X Y := RawHom (Φ := Φ) pe X.as Y.as
  id X := identity pe X.as
  comp f g := compose pe f g
  id_comp f := normalizeHom_injective pe (by simp)
  comp_id f := normalizeHom_injective pe (by simp)
  assoc f g h := normalizeHom_injective pe (by simp [Category.assoc])

def normalizeFunctor : RawTypeCategory (τ := τ) Φ pe ⥤ Guarded where
  obj X := G X.as
  map := normalizeHom pe
  map_id _ := normalize_identity pe
  map_comp _ _ := normalize_compose pe _ _

noncomputable def homEquiv (A B : τ) : RawHom (Φ := Φ) pe A B ≃ (G A ⟶ G B) :=
  Equiv.ofBijective (normalizeHom pe) ⟨normalizeHom_injective pe, normalizeHom_surjective pe⟩

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton

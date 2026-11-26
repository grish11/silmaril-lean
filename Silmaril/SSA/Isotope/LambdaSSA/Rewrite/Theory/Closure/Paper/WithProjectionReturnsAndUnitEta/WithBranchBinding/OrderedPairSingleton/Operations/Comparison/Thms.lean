module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton.Operations.Comparison.Defs

/-! # Normalization as the bundled operation comparison -/

public section

universe u v w

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton.Operations

open CategoryTheory
open Paper.Extension.Singleton (ofType)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

local notation "Join" => WithPairReturns.JoinedStep (τ := τ) (Φ := Φ) pe
local notation "G" => ofType (Φ := Φ) Join

/-- The hom equivalences of the strict raw/guarded category isomorphism
preserve the named computation and structural operations. -/
@[expose] noncomputable def operationIso : OperationIso (τ := τ) (Φ := Φ) pe where
  homEquiv := OrderedPairSingleton.homEquiv pe
  map_id := fun _ => normalize_identity pe
  map_comp := normalize_compose pe
  map_whiskerLeft := fun X {A B} f => normalize_whiskerLeft pe (A := A) (B := B) X f
  map_whiskerRight := fun X {A B} f => normalize_whiskerRight pe (A := A) (B := B) X f
  map_exactCopair := normalize_exactCopair pe
  map_iterateSum := normalize_iterateSum pe
  map_primitive := normalize_primitive pe
  map_discard := normalize_discard pe
  map_diagonal := normalize_diagonal pe
  map_productFst := normalize_productFst pe
  map_productSnd := normalize_productSnd pe
  map_sumInl := normalize_sumInl pe
  map_sumInr := normalize_sumInr pe
  map_fromEmpty := normalize_fromEmpty pe
  map_braid := normalize_braid pe
  map_associate := normalize_associate pe
  map_unassociate := normalize_unassociate pe
  map_unitProjectionLeft := normalize_unitProjectionLeft pe
  map_unitProjectionRight := normalize_unitProjectionRight pe
  map_leftUnitSection := normalize_leftUnitSection pe
  map_rightUnitSection := normalize_rightUnitSection pe

@[simp] theorem operationIso_apply {A B : τ} (f : RawHom (Φ := Φ) pe A B) :
    (operationIso pe).homEquiv A B f = normalizeHom pe f :=
  rfl

@[simp] theorem operationIso_symm_apply {A B : τ} (f : G A ⟶ G B) :
    ((operationIso pe).homEquiv A B).symm f = toRawHom pe f :=
  rfl

/-- The forward map is the functor of the existing strict category isomorphism. -/
theorem operationIso_apply_eq_categoryIso_hom_map {A B : τ} (f : RawHom (Φ := Φ) pe A B) :
    (operationIso pe).homEquiv A B f =
      (categoryIso (τ := τ) (Φ := Φ) pe).hom.toFunctor.map (X := ⟨A⟩) (Y := ⟨B⟩) f :=
  rfl

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton.Operations

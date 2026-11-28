module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton.Operations.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OrderedPairOperationsCoproducts

/-! # The raw category actions and exact coproducts respect the singleton comparison -/

public section

universe u v w

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton.Operations

open Silmaril CategoryTheory CategoryTheory.Limits
open Paper.Extension.Singleton (ofType ofRegion)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

local notation "Join" => WithPairReturns.JoinedStep (τ := τ) (Φ := Φ) pe
local notation "Raw" => RawTypeCategory (τ := τ) Φ pe
local notation "G" => ofType (Φ := Φ) Join

/-- The literal raw fixed-left operation acts functorially. -/
@[expose] def whiskerLeftFunctor (X : τ) : Raw ⥤ Raw where
  obj Y := ⟨product X Y.as⟩
  map := whiskerLeft pe X
  map_id Y := normalizeHom_injective pe (by
    change normalizeHom pe (whiskerLeft pe X (identity pe Y.as)) =
      normalizeHom pe (identity pe (product X Y.as))
    rw [normalize_whiskerLeft, normalize_identity, normalize_identity]
    exact (Extension.Singleton.whiskerLeftFunctor Join (G X)).map_id (G Y.as))
  map_comp f g := normalizeHom_injective pe (by
    change normalizeHom pe (whiskerLeft pe X (compose pe f g)) =
      normalizeHom pe (compose pe (whiskerLeft pe X f) (whiskerLeft pe X g))
    rw [normalize_whiskerLeft, normalize_compose, normalize_compose, normalize_whiskerLeft,
      normalize_whiskerLeft]
    exact (Extension.Singleton.whiskerLeftFunctor Join (G X)).map_comp (normalizeHom pe f) (normalizeHom pe g))

/-- The literal raw fixed-right operation acts functorially. -/
@[expose] def whiskerRightFunctor (X : τ) : Raw ⥤ Raw where
  obj Y := ⟨product Y.as X⟩
  map := whiskerRight pe X
  map_id Y := normalizeHom_injective pe (by
    change normalizeHom pe (whiskerRight pe X (identity pe Y.as)) =
      normalizeHom pe (identity pe (product Y.as X))
    rw [normalize_whiskerRight, normalize_identity, normalize_identity]
    exact (Extension.Singleton.whiskerRightFunctor Join (G X)).map_id (G Y.as))
  map_comp f g := normalizeHom_injective pe (by
    change normalizeHom pe (whiskerRight pe X (compose pe f g)) =
      normalizeHom pe (compose pe (whiskerRight pe X f) (whiskerRight pe X g))
    rw [normalize_whiskerRight, normalize_compose, normalize_compose, normalize_whiskerRight,
      normalize_whiskerRight]
    exact (Extension.Singleton.whiskerRightFunctor Join (G X)).map_comp (normalizeHom pe f) (normalizeHom pe g))

theorem whiskerLeftFunctor_comp_normalize (X : τ) :
    whiskerLeftFunctor pe X ⋙ normalizeFunctor pe =
      normalizeFunctor pe ⋙ Extension.Singleton.whiskerLeftFunctor Join (G X) :=
  Functor.hext (fun _ => rfl) (fun _ _ f => heq_of_eq (normalize_whiskerLeft pe X f))

theorem whiskerRightFunctor_comp_normalize (X : τ) :
    whiskerRightFunctor pe X ⋙ normalizeFunctor pe =
      normalizeFunctor pe ⋙ Extension.Singleton.whiskerRightFunctor Join (G X) :=
  Functor.hext (fun _ => rfl) (fun _ _ f => heq_of_eq (normalize_whiskerRight pe X f))

/-- The raw case operation supplies the coproduct mediating arrow. -/
noncomputable def sumCofanIsColimit (A B : τ) : IsColimit (sumCofan (Φ := Φ) pe A B) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OrderedPairOperationsCoproducts.sumCofanIsColimit pe A B

/-- The raw class of the guarded empty decoder supplies the initial map. -/
noncomputable def emptyIsInitial : IsInitial (⟨Silmaril.empty⟩ : Raw) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OrderedPairOperationsCoproducts.emptyIsInitial (Φ := Φ) (τ := τ) pe

/-- The mediating arrow of the exact raw coproduct is the literal case operation. -/
theorem sumCofan_desc {A B : τ} {Z : Raw} (f : (⟨A⟩ : Raw) ⟶ Z) (g : (⟨B⟩ : Raw) ⟶ Z) :
    (sumCofanIsColimit pe A B).desc (BinaryCofan.mk f g) = exactCopair pe f g :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OrderedPairOperationsCoproducts.sumCofan_desc pe f g

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton.Operations

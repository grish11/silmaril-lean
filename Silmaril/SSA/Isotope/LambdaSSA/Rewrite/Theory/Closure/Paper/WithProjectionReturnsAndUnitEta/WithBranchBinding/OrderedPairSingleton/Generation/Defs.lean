module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton.Operations.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton.Iteration.Thms

/-! # Generation by the literal raw singleton operations -/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton.Generation

open Silmaril CategoryTheory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

local notation "Raw" => RawTypeCategory (τ := τ) Φ pe
local notation "H" => RawHom (Φ := Φ) pe

abbrev rawType (A : τ) : Raw := ⟨A⟩

/-- Generate raw arrows with the literal raw operations. -/
inductive Generated : {A B : τ} → H A B → Prop where
  | id (A : τ) : Generated (identity pe A)
  | comp {A B D : τ} {f : H A B} {g : H B D} :
      Generated f → Generated g → Generated (compose pe f g)
  | inv {A B : τ} (i : rawType (Φ := Φ) pe A ≅ rawType pe B) :
      Generated (A := A) (B := B) i.hom → Generated (A := B) (B := A) i.inv
  | discard (A : τ) : Generated (Operations.discard pe A)
  | fst (A B : τ) : Generated (Operations.productFst pe A B)
  | snd (A B : τ) : Generated (Operations.productSnd pe A B)
  | copy (A : τ) : Generated (Operations.diagonal pe A)
  | primitive (p : Φ) : Generated (Operations.primitive (τ := τ) pe p)
  | initial {A : τ} (f : H empty A) : Generated f
  | inl (A B : τ) : Generated (Operations.sumInl pe A B)
  | inr (A B : τ) : Generated (Operations.sumInr pe A B)
  | copair {A B D : τ} {f : H A D} {g : H B D} :
      Generated f → Generated g → Generated (Operations.exactCopair pe f g)
  | left (X : τ) {A B : τ} {f : H A B} :
      Generated f → Generated (Operations.whiskerLeft pe X f)
  | right (X : τ) {A B : τ} {f : H A B} :
      Generated f → Generated (Operations.whiskerRight pe X f)
  | iterate {A B : τ} {f : H A (coprod B A)} :
      Generated f → Generated (iterateSum pe f)

/-- The multiplicative property underlying the raw generated wide subcategory. -/
def generatedArrows : MorphismProperty Raw :=
  fun A B f => Generated (τ := τ) (Φ := Φ) pe (A := A.as) (B := B.as) f

instance generatedArrows_multiplicative : (generatedArrows (τ := τ) (Φ := Φ) pe).IsMultiplicative where
  id_mem A := Generated.id A.as
  comp_mem _ _ hf hg := Generated.comp hf hg

abbrev Category := WideSubcategory (generatedArrows (τ := τ) (Φ := Φ) pe)

abbrev ofType (A : τ) : Category (τ := τ) (Φ := Φ) pe := ⟨rawType pe A⟩

def ofGenerated {A B : τ} {f : H A B} (hf : Generated pe f) :
    ofType (Φ := Φ) pe A ⟶ ofType pe B := ⟨f, hf⟩

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton.Generation

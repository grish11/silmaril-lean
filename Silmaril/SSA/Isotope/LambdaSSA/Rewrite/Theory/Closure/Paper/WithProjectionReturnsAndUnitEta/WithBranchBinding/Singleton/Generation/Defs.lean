module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.Singleton.Operations.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.Singleton.Iteration.Thms

/-! # Generation by the literal raw singleton operations -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.Singleton.Generation

open Silmaril CategoryTheory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (S : NormalizedSeed τ Φ)

local notation "Raw" => RawTypeCategory S
local notation "H" => RawHom S

abbrev rawType (A : τ) : Raw := ⟨A⟩

/-- Generate raw arrows with the literal raw operations. -/
inductive Generated : {A B : τ} → H A B → Prop where
  | id (A : τ) : Generated (identity S A)
  | comp {A B D : τ} {f : H A B} {g : H B D} :
      Generated f → Generated g → Generated (compose S f g)
  | inv {A B : τ} (i : rawType S A ≅ rawType S B) :
      Generated (A := A) (B := B) i.hom → Generated (A := B) (B := A) i.inv
  | discard (A : τ) : Generated (discard S A)
  | fst (A B : τ) : Generated (productFst S A B)
  | snd (A B : τ) : Generated (productSnd S A B)
  | copy (A : τ) : Generated (diagonal S A)
  | primitive (p : Φ) : Generated (primitive S p)
  | initial {A : τ} (f : H empty A) : Generated f
  | inl (A B : τ) : Generated (sumInl S A B)
  | inr (A B : τ) : Generated (sumInr S A B)
  | copair {A B D : τ} {f : H A D} {g : H B D} :
      Generated f → Generated g → Generated (exactCopair S f g)
  | left (X : τ) {A B : τ} {f : H A B} :
      Generated f → Generated (whiskerLeft S X f)
  | right (X : τ) {A B : τ} {f : H A B} :
      Generated f → Generated (whiskerRight S X f)
  | iterate {A B : τ} {f : H A (coprod B A)} :
      Generated f → Generated (iterateSum S f)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.Singleton.Generation

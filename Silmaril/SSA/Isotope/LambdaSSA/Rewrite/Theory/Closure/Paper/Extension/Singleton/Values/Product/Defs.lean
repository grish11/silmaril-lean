module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Values.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Values.Constructors.Defs

/-! # Projections and discard in an extended Paper singleton quotient -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory CategoryTheory.Limits
open CfgEta.TypeCategory (productFstBranches productSndBranches)

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

set_option hygiene false in
local notation "P" => projection Seed
set_option hygiene false in
local notation "obj" => ofType (Φ := Φ) Seed

abbrev productFst (A B : τ) : obj (product A B) ⟶ obj A := ofRegion Seed (productFstBranches A B)
abbrev productSnd (A B : τ) : obj (product A B) ⟶ obj B := ofRegion Seed (productSndBranches A B)
abbrev discardArrow (A : τ) : obj A ⟶ obj (Silmaril.unit : τ) := (P).map (Paper.TypeCategory.discardArrow A)

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton

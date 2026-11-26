module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton.Operations.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Generation.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Normalization.Transport.Thms

/-! # Normalization of the literal representative operations -/

public section

universe u v w

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OrderedPairOperations

open Silmaril CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper
open Paper.Extension.Singleton (ofType ofRegion)

open Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton.Operations

open CfgEta.TypeCategory (whiskerLeftRegion_typed whiskerRightRegion_typed caseValueBranches)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

local notation "Join" => WithPairReturns.JoinedStep (τ := τ) (Φ := Φ) pe
local notation "G" => ofType (Φ := Φ) Join

variable {A B D : τ}

section

variable (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

theorem ofRegion_bind_whiskerLeftRep (X : τ) (r : Rep (Φ := Φ) A B) :
    ofRegion Seed (whiskerLeftRep X r).property.bindBranchArguments =
      Extension.Singleton.whiskerLeft Seed (ofType Seed X) (ofRegion Seed r.property.bindBranchArguments) := by
  have hr := whiskerLeftRegion_typed X r.property.bindBranchArguments
  have h := (Extension.Singleton.ofRegion_eq_iff Seed hr.hasType.bindBranchArguments hr).mpr
    (.paper (.cfgEta (.native hr.bindBranchArguments_equiv.symm)))
  change ofRegion Seed hr.hasType.bindBranchArguments = _
  rw [h]
  change _ = (Extension.Singleton.whiskerLeftFunctor Seed (ofType Seed X)).map
    ((Extension.Singleton.projection Seed).map (Paper.TypeCategory.ofRegion r.property.bindBranchArguments))
  rw [Extension.Singleton.whiskerLeft_map, Paper.TypeCategory.whiskerLeft_ofRegion]
  rfl

theorem ofRegion_bind_whiskerRightRep (X : τ) (r : Rep (Φ := Φ) A B) :
    ofRegion Seed (whiskerRightRep X r).property.bindBranchArguments =
      Extension.Singleton.whiskerRight Seed (ofRegion Seed r.property.bindBranchArguments) (ofType Seed X) := by
  have hr := whiskerRightRegion_typed X r.property.bindBranchArguments
  have h := (Extension.Singleton.ofRegion_eq_iff Seed hr.hasType.bindBranchArguments hr).mpr
    (.paper (.cfgEta (.native hr.bindBranchArguments_equiv.symm)))
  change ofRegion Seed hr.hasType.bindBranchArguments = _
  rw [h]
  change _ = (Extension.Singleton.whiskerRightFunctor Seed (ofType Seed X)).map
    ((Extension.Singleton.projection Seed).map (Paper.TypeCategory.ofRegion r.property.bindBranchArguments))
  rw [Extension.Singleton.whiskerRight_map, Paper.TypeCategory.whiskerRight_ofRegion]
  rfl

theorem ofRegion_bind_copairRep (r : Rep (Φ := Φ) A D) (s : Rep (Φ := Φ) B D) :
    ofRegion Seed (copairRep r s).property.bindBranchArguments =
      Extension.Singleton.ValueCoproducts.exactCopair Seed
        (ofRegion Seed r.property.bindBranchArguments) (ofRegion Seed s.property.bindBranchArguments) := by
  rw [Extension.Singleton.Generation.exactCopair_ofRegion]
  apply (Extension.Singleton.ofRegion_eq_iff Seed _ _).mpr
  have h := Extension.Eqv.refl (Seed := Seed)
    (caseValueBranches r.property.bindBranchArguments s.property.bindBranchArguments).hasType
  simpa only [copairRep, bindBranchArguments, renameVars_eq_substVars, bindBranchArguments_substVars] using h

end

theorem normalize_whiskerLeftRep (X : τ) (r : Rep (Φ := Φ) A B) :
    normalizeHom pe (Quotient.mk _ (whiskerLeftRep X r)) =
      Extension.Singleton.whiskerLeft Join (G X) (normalizeHom pe (Quotient.mk _ r)) :=
  ofRegion_bind_whiskerLeftRep Join X r

theorem normalize_whiskerRightRep (X : τ) (r : Rep (Φ := Φ) A B) :
    normalizeHom pe (Quotient.mk _ (whiskerRightRep X r)) =
      Extension.Singleton.whiskerRight Join (normalizeHom pe (Quotient.mk _ r)) (G X) :=
  ofRegion_bind_whiskerRightRep Join X r

theorem normalize_copairRep (r : Rep (Φ := Φ) A D) (s : Rep (Φ := Φ) B D) :
    normalizeHom pe (Quotient.mk _ (copairRep r s)) =
      Extension.Singleton.ValueCoproducts.exactCopair Join
        (normalizeHom pe (Quotient.mk _ r)) (normalizeHom pe (Quotient.mk _ s)) :=
  ofRegion_bind_copairRep Join r s

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OrderedPairOperations

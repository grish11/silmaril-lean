module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback.Dispatcher.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Generation.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithUnaryReturns.LiveTable.Dispatcher

/-! # Read back each guarded dispatcher from its ordered row representatives -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory CategoryTheory.Limits
open CfgEta.TypeCategory (seqValueBranches caseValueBranches productSndBranches)
open CfgEta.TypeCategory.Retained (distributorRegion_typed)
open Paper.WithCaseReturns.BinaryFold.WithTripling (capturedDispatcher)
open Paper.Extension.Singleton (ofRegion projection emptyIsInitial productSnd)
open Paper.Extension.Singleton.Generation (exactCopair_ofRegion)

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

set_option hygiene false in
local notation "T" => Paper.WithCaseReturns.BinaryFold.WithTripling.Step (τ := τ) (Φ := Φ) pe
local notation "Lit" => ofRegion T

/-- The assembled captured dispatcher runs the literal distributive split
at each entry of the original ordered row list. -/
theorem capturedDispatcher_ofRep (X D : τ) (L : LCtx τ)
    (rows : ∀ i : Fin L.length, {r : Region Φ // ValueBranches [product X (L.get i)] r [D]}) :
    capturedDispatcher pe X L (fun i => Lit (rows i).property) =
      Lit (dispatcherRep X L rows).property :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithUnaryReturns.LiveTable.capturedDispatcher_ofRep
    pe X D L rows

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback

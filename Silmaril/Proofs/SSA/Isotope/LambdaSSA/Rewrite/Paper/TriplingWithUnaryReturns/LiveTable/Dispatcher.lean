module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback.Dispatcher.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Generation.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithUnaryReturns.LiveTable

open Silmaril.Isotope.LambdaSSA.Region
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback
  (emptyDispatchRep dispatcherRep)

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

set_option backward.isDefEq.respectTransparency false

private theorem composition {A B D : τ} {r s : Region Φ}
    (hr : ValueBranches [A] r [B]) (hs : ValueBranches [B] s [D]) :
    Lit hr ≫ Lit hs = Lit (seqValueBranches hr hs) :=
  ((projection T).map_comp (Paper.TypeCategory.ofRegion hr) (Paper.TypeCategory.ofRegion hs)).symm.trans
    (congrArg (projection T).map (Paper.TypeCategory.ofRegion_comp hr hs (seqValueBranches hr hs)))

theorem capturedDispatcher_ofRep (X D : τ) (L : LCtx τ)
    (rows : ∀ i : Fin L.length, {r : Region Φ // ValueBranches [product X (L.get i)] r [D]}) :
    capturedDispatcher pe X L (fun i => Lit (rows i).property) =
      Lit (dispatcherRep X L rows).property := by
  induction L with
  | nil =>
    rw [capturedDispatcher, dispatcherRep]
    have empty : (emptyIsInitial T).to _ = Lit (emptyDispatchRep (Φ := Φ) D).property :=
      (emptyIsInitial T).hom_ext _ _
    rw [empty]
    exact composition pe _ _
  | cons A L ih =>
    rw [capturedDispatcher, dispatcherRep, ih, exactCopair_ofRegion]
    exact composition pe _ _

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithUnaryReturns.LiveTable

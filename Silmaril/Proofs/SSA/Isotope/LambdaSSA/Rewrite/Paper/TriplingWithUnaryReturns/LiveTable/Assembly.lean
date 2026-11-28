module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback.Dispatcher.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithUnaryReturns.LiveTable

open Silmaril.Isotope.LambdaSSA.Region
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns (Step Eqv fromWithComputedCalls)
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback
  (Readback entry_route orderedRow orderedRows capturedDispatcher_ofRep dispatcherRep packedReadbackRep)

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory
open CfgEta.TypeCategory (seqValueBranches caseValueBranches)
open Paper.Extension.Singleton (ofRegion ofRegion_eq_iff ofType projection iterateSum iterateSum_map)
open Paper.WithCaseReturns.BinaryFold.WithTripling (capturedDispatcher)
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls (fromWithTripling)
open Paper.Extension.Singleton.ValueCoproducts (exactCopair)
open Paper.Extension.Singleton.Generation (exactCopair_ofRegion)

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

set_option hygiene false in
local notation "S" => Step (τ := τ) (Φ := Φ) pe
local notation "Lit" => ofRegion S

set_option backward.isDefEq.respectTransparency false

theorem readback_iff_eqv {n : Nat} (R : Fin n → τ) {X D : τ} {e : Region Φ}
    {blocks : Fin n → Region Φ} (he : ValueBranches [X] e (List.ofFn R ++ [D]))
    (hb : ∀ i, ValueBranches [R i, X] (blocks i) (List.ofFn R ++ [D])) :
    Readback pe R he hb ↔ Eqv pe [X] (.cfg e n blocks) (packedReadbackRep R he hb).val [D] := by
  let dispatcher := dispatcherRep X (List.ofFn R) (orderedRow R hb)
  let hid : ValueBranches [D] (.br 0 (.var 0) : Region Φ) [D] :=
    .br (ℓ := 0) rfl (.var (i := 0) rfl)
  let loop := SyntacticCategory.iterateRegion_valueBranches dispatcher.property
  have hId : 𝟙 (ofType S D) = Lit hid :=
    ((projection S).map_id (Paper.TypeCategory.ofType D)).symm.trans
      (congrArg (projection S).map (Paper.TypeCategory.ofRegion_id (Φ := Φ) D).symm)
  have hIter : iterateSum S (Lit dispatcher.property) = Lit loop :=
    (iterateSum_map S (Paper.TypeCategory.ofRegion dispatcher.property)).trans
      (congrArg (projection S).map (Paper.TypeCategory.iterateSum_ofRegion dispatcher.property))
  have rhs : Lit (entry_route R he) ≫ exactCopair S (Lit hid) (Lit loop) =
      Lit (packedReadbackRep R he hb).property := by
    rw [exactCopair_ofRegion]
    exact ((projection S).map_comp
      (Paper.TypeCategory.ofRegion (entry_route R he))
      (Paper.TypeCategory.ofRegion (caseValueBranches hid loop))).symm.trans
      (congrArg (projection S).map
        (Paper.TypeCategory.ofRegion_comp (entry_route R he) (caseValueBranches hid loop)
          (seqValueBranches (entry_route R he) (caseValueBranches hid loop))))
  have hStep : (fromWithTripling pe ⋙ fromWithComputedCalls pe).map
      (capturedDispatcher pe X (List.ofFn R) (orderedRows pe R hb)) = Lit dispatcher.property :=
    congrArg (fromWithTripling pe ⋙ fromWithComputedCalls pe).map
      (capturedDispatcher_ofRep pe X _ (List.ofFn R) (orderedRow R hb))
  dsimp only [Readback]
  rw [hStep]
  change (Lit (.cfg R he hb) = Lit (entry_route R he) ≫
    exactCopair S (𝟙 (ofType S D)) (iterateSum S (Lit dispatcher.property))) ↔ _
  rw [hId, hIter, rhs]
  exact ofRegion_eq_iff S _ _

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithUnaryReturns.LiveTable

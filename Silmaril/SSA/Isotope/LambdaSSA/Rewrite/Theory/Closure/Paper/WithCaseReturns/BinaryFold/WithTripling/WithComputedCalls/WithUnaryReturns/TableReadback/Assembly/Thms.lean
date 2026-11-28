module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback.Dispatcher.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithUnaryReturns.LiveTable.Assembly

/-! # The exact native law for assembling an arbitrary live CFG -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory
open CfgEta.TypeCategory (seqValueBranches caseValueBranches)
open Paper.Extension.Singleton (ofRegion ofRegion_eq_iff ofType projection iterateSum iterateSum_map)
open Paper.Extension.Singleton.ValueCoproducts (exactCopair)
open Paper.Extension.Singleton.Generation (exactCopair_ofRegion)

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

set_option hygiene false in
local notation "S" => Step (τ := τ) (Φ := Φ) pe
local notation "Lit" => ofRegion S

/-- The quotient-level readback is precisely the contextual equation
between the written table and the guarded one-label assembly. -/
theorem readback_iff_eqv {n : Nat} (R : Fin n → τ) {X D : τ} {e : Region Φ}
    {blocks : Fin n → Region Φ} (he : ValueBranches [X] e (List.ofFn R ++ [D]))
    (hb : ∀ i, ValueBranches [R i, X] (blocks i) (List.ofFn R ++ [D])) :
    Readback pe R he hb ↔ Eqv pe [X] (.cfg e n blocks) (packedReadbackRep R he hb).val [D] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithUnaryReturns.LiveTable.readback_iff_eqv
    pe R he hb

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback

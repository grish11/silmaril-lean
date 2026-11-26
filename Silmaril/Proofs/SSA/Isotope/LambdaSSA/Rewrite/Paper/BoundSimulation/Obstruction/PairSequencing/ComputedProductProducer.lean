module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProductDestructureReturns.Example.Computed.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.BinaryLet.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.ProductDestructureReturn
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.Soundness

/-! # A computed product distinguishes the two guarded singleton producers -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithComputedCallReturns.Example (Atom Payload)
open Paper.RetainedLet.Generation.Example (Op)
open Paper.WithProductDestructureReturns.Example.Computed (Packet Seed)
open Paper.RetainedLet (returnOnce unpackBody unpackTerm unpackTerm_typed)
open Paper.SingletonReification.BinaryLet (returnPair)
open CfgEta.TypeCategory (returnRegion returnRegion_rename)
open Silmaril.Isotope.LambdaSSA.Semantics (extend)
open scoped Paper.BoundSimulation.Obstruction Observer.CanonicalUnit
open _root_.Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Observer
  (EnvTy Result)
open _root_.Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.Observer
  (TermObservation SameWith extension_same evalReturnRegion evalRegionWith evalTermWith
    computes)

private def productObservation : TermObservation (α := Atom) Op where
  computedRegionLet₂ := true
  evaluateCallOperand := true
  unitCall _ := true
  unitCall_typed _ _ _ := .base

private theorem computedCall_same {Γ L : List (Ty Atom)} {r s : Region Op}
    (step : Paper.WithComputedCallReturns.Step Γ r s L) : SameWith productObservation Γ r s := by
  cases step with
  | @seq a p ha =>
    intro env he
    let inner : Tm.HasType (instrSrc p :: Γ) (.op p (.var 0)) (instrTrg p) := .op (.var rfl)
    rw [evalReturnRegion (.op ha) he, evalReturnRegion (.let₁ ha inner) he]
    simp only [evalTermWith, show productObservation.evaluateCallOperand = true from rfl,
      show productObservation.unitCall p = true from rfl, ite_true, extend]
    cases evalTermWith productObservation a env <;> rfl

private theorem productDestructure_same {Γ L : List (Ty Atom)} {r s : Region Op}
    (step : Paper.WithProductDestructureReturns.Step Γ r s L) : SameWith productObservation Γ r s := by
  cases step with
  | @unpack X A D body hb =>
    intro env he
    rw [evalReturnRegion (unpackTerm_typed hb) he]
    unfold unpackBody unpackTerm
    rw [← returnRegion_rename]
    have value := he (rfl : At [product X A] 0 (product X A))
    cases read : env 0 with
    | pair x a =>
      rw [read] at value
      cases value with
      | pair hx ha =>
        simp only [evalRegionWith, evalTermWith, productObservation, computes, Bool.and_false,
          Bool.false_eq_true, ite_false, read]
        let ren := ((Ren.wk [] (product X A)).lift X).lift A
        exact evalReturnRegion (hb.rename ren) ((he.extend hx).extend ha)
    | atom a => exact a.elim
    | unit => rw [read] at value; cases value
    | inl a => rw [read] at value; cases value
    | inr a => rw [read] at value; cases value

private theorem productJoin_same {Γ L : List (Ty Atom)} {r s : Region Op}
    (eq : Paper.Extension.Eqv Seed Γ r s L) : SameWith productObservation Γ r s :=
  extension_same (fun step =>
    step.elim (computedCallSeed_same rfl rfl (fun call => computedCall_same call)) productDestructure_same) eq

private theorem env_typed : EnvTy [Payload] (fun _ => .unit) := by
  intro i A atInput
  cases i with
  | zero => cases Option.some.inj atInput; exact .base
  | succ i => simp [At] at atInput

theorem computed_product_producer_fails :
    ¬ Paper.Extension.Eqv Seed [Payload]
      (returnPair (.pair (.var 0) (.op Op.produce (.var 0))))
      (returnOnce (.pair (.var 0) (.op Op.produce (.var 0)))) [Packet] := by
  intro eq
  have seen := productJoin_same eq (fun _ => .unit) env_typed
  change Result.fault = .jump 0 (.pair .unit .unit) at seen
  cases seen

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing

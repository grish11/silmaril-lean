module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseAndUnaryReturns.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.Obstruction.PairSequencing.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.CaseReturns
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Values.Product.Thms

/-! # Pair sequencing in the case-return and unary-forwarding quotient -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open scoped Paper.BoundSimulation.Obstruction
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.UnaryReturn.Beta.Constructors (pairSequence)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.UnaryReturn.Beta.Constructors.Example (source)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedLet (returnOnce)

open scoped Observer.CanonicalUnit
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Observer (EnvTy Result)

open Paper.Extension.Singleton (ofRegion pairArrows)
open CfgEta.TypeCategory (returnRegion_typed)

local instance : HasEff Empty Bool := ⟨Empty.elim⟩

local notation "Join" => Paper.WithCaseAndUnaryReturns.JoinedStep (τ := Ty Empty) (Φ := Empty) false

private theorem env_typed : EnvTy [source] (fun _ => .inl .unit) := by
  intro i A hi
  cases i with
  | zero => cases Option.some.inj hi; exact .inl .unit
  | succ i => simp [At] at hi

private theorem join_same {Γ L : List (Ty Empty)} {r s : Region Empty}
    (h : Paper.Extension.Eqv Join Γ r s L) : Observer.SameWith { pairLet := true } Γ r s :=
  Observer.extension_same
    (fun step => step.elim
      projectionUnitSeed_same
      (fun returned => returned.elim (Observer.unary_fusion_same rfl) (caseReturnSeed_same rfl))) h

theorem case_unary_pair_sequence_fails :
    ¬ Paper.Extension.Eqv Join [source]
      (returnOnce (.pair (.let₁ (.var 0) (.var 0)) (.var 0)))
      (pairSequence (.let₁ (.var 0) (.var 0)) (.var 0)) [product source source] := by
  intro h
  have obs := join_same h (fun _ => .inl .unit) env_typed
  change Result.fault = .jump 0 (.pair (.inl .unit) (.inl .unit)) at obs
  cases obs

set_option backward.isDefEq.respectTransparency false in
theorem case_unary_returnPair_ne_pairArrows
    (ha : Tm.HasType [source] (.let₁ (.var 0) (.var 0) : Tm Empty) source)
    (hb : Tm.HasType [source] (.var 0 : Tm Empty) source) :
    ofRegion Join (returnRegion_typed (.pair ha hb)) ≠
      pairArrows Join (ofRegion Join (returnRegion_typed ha)) (ofRegion Join (returnRegion_typed hb)) := by
  intro e
  let P := Paper.Extension.Singleton.projection Join
  change P.map (Paper.TypeCategory.returnTerm (.pair ha hb)) =
    pairArrows Join (P.map (Paper.TypeCategory.returnTerm ha)) (P.map (Paper.TypeCategory.returnTerm hb)) at e
  rw [← Paper.Extension.Singleton.map_pairArrows Join, Paper.TypeCategory.pairArrows_returnTerm ha hb] at e
  have seqTyped := Tm.HasType.let₁ ha (.let₁ (hb.rename (Ren.wk [source] source))
    (.pair (.var (i := 1) (show At [source, source, source] 1 source from rfl)) (.var (i := 0) rfl)))
  have eq := (Paper.Extension.Singleton.ofRegion_eq_iff Join
    (returnRegion_typed (.pair ha hb)) (returnRegion_typed seqTyped)).1 e
  have obs := join_same eq (fun _ => .inl .unit) env_typed
  rw [Observer.evalReturnRegion (.pair ha hb) env_typed, Observer.evalReturnRegion seqTyped env_typed] at obs
  change Result.fault = .jump 0 (.pair (.inl .unit) (.inl .unit)) at obs
  cases obs

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing

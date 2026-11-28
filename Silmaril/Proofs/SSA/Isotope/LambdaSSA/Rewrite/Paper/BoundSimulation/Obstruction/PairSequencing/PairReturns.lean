module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.CaseReturns
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.ConstructorSoundness
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.Defs

/-! # Typed observations preserved by the ordered-pair join -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.Observer

open Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open scoped Paper.BoundSimulation.Obstruction
open scoped _root_.Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Observer.CanonicalUnit

universe u v w
variable {α : Type u} {Φ : Type v} [HasTy Φ (Ty α)] {ε : Type w} [HasEff Φ ε] {pe : ε}

theorem pair_join_same {observation : TermObservation (α := α) Φ}
    (unmarkedCase : observation.caseTerm = false) (unmarkedPair : observation.pairLet = false)
    (unmarkedLet : observation.boundUnaryLet = false)
    {Γ L : List (Ty α)} {r s : Region Φ}
    (h : Paper.Extension.Eqv (Paper.WithPairReturns.JoinedStep pe) Γ r s L) :
    SameWith observation Γ r s := by
  apply extension_same (observation := observation) _ h
  intro Γ L r s step
  rcases step with (base | returned) | pair
  · exact projectionUnitSeed_same base
  · exact returned.elim (unary_fusion_same unmarkedLet) (caseReturnSeed_same unmarkedCase)
  · cases pair with
    | seq ha hb => exact fun env _ => sequence_pair unmarkedPair unmarkedLet _ _ env

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.Observer

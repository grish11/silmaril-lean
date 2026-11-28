module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProductDestructureReturns.Example.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProductDestructureReturns.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProductDestructureReturns.BranchBinding.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.ProductDestructureReturn

/-! # Separation of a returned destructure and generation in the opt-in join -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProductDestructureReturns.Example

open Silmaril Silmaril.Isotope.LambdaSSA
open CfgEta.TypeCategory (returnRegion returnRegion_typed)
open Paper.RetainedLet (unpackBody unpackTerm unpackTerm_typed)
open Paper.Extension.Singleton (ofRegion)
open Paper.Extension.Singleton.Generation (Generated)
open Paper.WithPairReturns (ReturnFragmentWithCalls)
open Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding (AddBinding guarded_eqv_iff_of_guardedSeed)

universe u v w

section Separation

variable {α : Type u} {Φ : Type v} [HasTy Φ (Ty α)] {ε : Type w} [HasEff Φ ε]

/-- The existing join separates region and term destructuring for a body that
binds and returns the pair rebuilt from its two fields. -/
theorem product_destructure_return_fails (pe : ε) :
    ¬ Extension.Eqv (WithComputedCallReturns.JoinedStep pe) [product (U α) (U α)]
      (unpackBody (returnRegion (body : Tm Φ))) (returnRegion (unpackTerm body)) [product (U α) (U α)] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.product_destructure_return_fails pe

/-- Raw branch binding preserves this separation on the two guarded witnesses. -/
theorem product_destructure_return_with_branch_binding_fails (pe : ε) :
    ¬ Extension.Eqv (AddBinding (WithComputedCallReturns.JoinedStep pe)) [product (U α) (U α)]
      (unpackBody (returnRegion (body : Tm Φ))) (returnRegion (unpackTerm body)) [product (U α) (U α)] :=
  let ⟨hr, hs⟩ := (Step.unpack (body_typed (α := α) (Φ := Φ))).valueBranches
  fun h => product_destructure_return_fails pe ((guarded_eqv_iff_of_guardedSeed computedJoin_valueBranches hr hs).1 h)

/-- The witness's returned destructure is outside the previous recursive grammar. -/
theorem witness_outside_previous_fragment (pe : ε) :
    ¬ ReturnFragmentWithCalls pe true (unpackTerm_typed (body_typed (α := α) (Φ := Φ))) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.witness_outside_previous_fragment pe

theorem packedBody_typed :
    Tm.HasType [product (U α) (U α)] (.let₁ (.var 0) (.var 0) : Tm Φ) (product (U α) (U α)) :=
  .let₁ (.var (i := 0) rfl) (.var (i := 0) rfl)

/-- The new constructor generates the term of the separated witness. -/
theorem witness_generated (pe : ε) :
    Generated (JoinedStep (τ := Ty α) (Φ := Φ) pe)
      (ofRegion (JoinedStep pe) (returnRegion_typed (unpackTerm_typed body_typed))) :=
  let input : Tm.BranchValue [product (U α) (U α)] (.var 0 : Tm Φ) (product (U α) (U α)) := .var rfl
  generated_returnFragment pe (.destructure (hc := packedBody_typed) rfl (.seq (.value input) (.value input)))

end Separation

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProductDestructureReturns.Example

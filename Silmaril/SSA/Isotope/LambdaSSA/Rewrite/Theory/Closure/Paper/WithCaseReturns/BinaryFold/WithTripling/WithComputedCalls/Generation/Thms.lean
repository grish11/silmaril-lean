module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.Generation.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Generation.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithComputedCalls.Generation

/-! # Generation of returned computed calls and their literal binders -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls

open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory
open CfgEta.TypeCategory (returnRegion returnRegion_typed caseValueBranches
  seqValueBranches whiskerLeftRegion_typed)
open Paper.Extension.Singleton (ofType ofRegion ofRegion_eq_iff projection whiskerLeftFunctor whiskerLeft_map)
open Paper.Extension.Singleton.Generation (Generated generated_branchValue generated_primitive_branchValue)
open Paper.RetainedLet (returnOnce_typed unpackBody_typed diagonal_typed)

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

set_option hygiene false in
local notation "S" => Step (τ := τ) (Φ := Φ) pe
local notation "Lit" => ofRegion S

/-- A generated operand followed by the primitive generates the written
call, even when the operand contains further computed calls. -/
theorem generated_call {X : τ} {a : Tm Φ}
    (p : Φ) (ha : Tm.HasType [X] a (instrSrc p))
    (ga : Generated S (Lit (returnRegion_typed ha))) :
    Generated S (Lit (returnRegion_typed (.op (f := p) ha))) :=
  TriplingWithComputedCalls.generated_call pe p ha ga

/-- Induction on the typed fragment yields generation of the original
lowered return at its exact singleton interface. -/
theorem generated_returnFragment {X D : τ} {a : Tm Φ} {ha : Tm.HasType [X] a D}
    (h : ReturnFragment pe ha) : Generated S (Lit (returnRegion_typed ha)) :=
  TriplingWithComputedCalls.generated_returnFragment pe h

/-- The literal binder retains the input and evaluates the producer once.
The extra comparison is automatic for a primitive call, whose returned
region is definitionally its single-bind return. -/
theorem generated_literalLet {X A D : τ} {a : Tm Φ} {r : Region Φ}
    (ha : Tm.HasType [X] a A) (hr : ValueBranches [A, X] r [D])
    (agree : Lit (returnRegion_typed ha) = Lit (returnOnce_typed ha))
    (ga : Generated S (Lit (returnRegion_typed ha)))
    (gr : Generated S (Lit (unpackBody_typed hr))) :
    Generated S (Lit (.let₁ ha hr)) :=
  TriplingWithComputedCalls.generated_literalLet pe ha hr agree ga gr

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls

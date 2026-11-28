module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.Generation.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedLet.Generation.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithUnaryReturns.Generation

/-! # Generation of literal unary binders with computed producers -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory
open CfgEta.TypeCategory (returnRegion_typed)
open Paper.Extension.Singleton (ofRegion ofRegion_eq_iff)
open Paper.Extension.Singleton.Generation (Generated)
open Paper.RetainedLet (returnOnce_typed unpackBody_typed)
open Paper.PackedBody (applyPackedTerm_typed)
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls (ReturnFragment)

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

set_option hygiene false in
local notation "S" => Step (τ := τ) (Φ := Φ) pe
local notation "Lit" => ofRegion S

open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithUnaryReturns (includeReturn)

/-- The call rule composes a generated operand with the primitive. -/
theorem generated_call {X : τ} {a : Tm Φ}
    (p : Φ) (ha : Tm.HasType [X] a (instrSrc p))
    (ga : Generated S (Lit (returnRegion_typed ha))) :
    Generated S (Lit (returnRegion_typed (.op (f := p) ha))) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithUnaryReturns.generated_call pe p ha ga

/-- All previously generated return forms are generated in the unary quotient. -/
theorem generated_returnFragment {X D : τ} {a : Tm Φ} {ht : Tm.HasType [X] a D}
    (h : ReturnFragment pe ht) : Generated S (Lit (returnRegion_typed ht)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithUnaryReturns.generated_returnFragment pe h

/-- A generated lowered producer and a generated packed body suffice for
every literal unary region. Lowering supplies the producer comparison. -/
theorem generated_literalLet {X A D : τ} {a : Tm Φ} {r : Region Φ} (ha : Tm.HasType [X] a A)
    (hr : ValueBranches [A, X] r [D]) (ga : Generated S (Lit (returnRegion_typed ha)))
    (gr : Generated S (Lit (unpackBody_typed hr))) :
    Generated S (Lit (.let₁ ha hr)) :=
  Paper.WithCaseAndUnaryReturns.generated_returnLet pe S (includeReturn pe) ha hr ga gr

/-- For the written term binder, generation of the decoded returned
body suffices even if it was given in the original two-variable context. -/
theorem generated_returnLet_of_packedBody {X A D : τ} {a b : Tm Φ}
    (ha : Tm.HasType [X] a A) (hb : Tm.HasType [A, X] b D)
    (ga : Generated S (Lit (returnRegion_typed ha)))
    (gb : Generated S (Lit (unpackBody_typed (returnRegion_typed hb)))) :
    Generated S (Lit (returnRegion_typed (.let₁ ha hb))) :=
  Paper.WithCaseAndUnaryReturns.generated_retained_returnLet pe S (includeReturn pe) ha hb ga gb

/-- A returned unary term can keep both the original input and the computed
value in its generated packed body. -/
theorem generated_packed_returnLet {X A D : τ} {a c : Tm Φ} (ha : Tm.HasType [X] a A)
    (hc : Tm.HasType [product X A] c D) (ga : Generated S (Lit (returnRegion_typed ha)))
    (gc : Generated S (Lit (returnRegion_typed hc))) :
    Generated S (Lit (returnRegion_typed (.let₁ ha (applyPackedTerm_typed hc)))) :=
  Paper.RetainedLet.generated_packed_returnLet S pe (includeReturn pe) ha hc ga gc

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns

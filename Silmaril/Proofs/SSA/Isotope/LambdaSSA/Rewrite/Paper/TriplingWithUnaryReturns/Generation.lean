module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.Generation.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedLet.Generation.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithUnaryReturns

open Silmaril.Isotope.LambdaSSA.Region
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns (Step)
open Paper.Extension.Singleton.Generation (generated_branchValue generated_primitive_branchValue)

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

theorem includeReturn {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (h : Paper.WithCaseAndUnaryReturns.Step pe Γ r s L) : S Γ r s L :=
  h.elim Or.inr (fun e => .inl (.inl (.inl (.inl (.inr e)))))

set_option backward.isDefEq.respectTransparency false

theorem generated_call {X : τ} {a : Tm Φ}
    (p : Φ) (ha : Tm.HasType [X] a (instrSrc p))
    (ga : Generated S (Lit (returnRegion_typed ha))) :
    Generated S (Lit (returnRegion_typed (.op (f := p) ha))) := by
  let hv : Tm.BranchValue [instrSrc p] (.var 0 : Tm Φ) (instrSrc p : τ) := .var rfl
  let hc := Tm.HasType.op (f := p) hv.hasType
  have eq : Lit (returnRegion_typed (.op (f := p) ha)) =
      Lit (returnRegion_typed (.let₁ ha (hc.rename ((Ren.wk [] X).lift (instrSrc p))))) :=
    (ofRegion_eq_iff S _ _).2
      ((Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.computedCall pe p ha).mapSeed Or.inl)
  rw [eq, Paper.WithCaseAndUnaryReturns.returnLet_eq_comp S ha hc]
  exact .comp ga (generated_primitive_branchValue S p hv)

theorem generated_returnFragment {X D : τ} {a : Tm Φ} {ht : Tm.HasType [X] a D}
    (h : ReturnFragment pe ht) : Generated S (Lit (returnRegion_typed ht)) := by
  induction h with
  | value hv =>
    exact ((ofRegion_eq_iff S _ (.br (ℓ := 0) rfl hv)).2
      (.paper (.cfgEta (.native (.base (CfgEta.TypeCategory.returnRegion_branchValue hv)))))).symm ▸
      generated_branchValue S hv
  | @call X a p ha _ ih => exact generated_call pe p ha ih
  | @seq X A D a b ha hb _ _ ga gb =>
    rw [Paper.WithCaseAndUnaryReturns.returnLet_eq_comp S ha hb]
    exact .comp ga gb
  | @caseInput A B D a b ha hb pa pb _ _ ga gb =>
    rw [Paper.WithCaseAndUnaryReturns.returnCase_eq_copair pe S (includeReturn pe) ha hb pa pb]
    exact .copair ga gb

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithUnaryReturns

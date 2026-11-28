module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.Generation.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedLet.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseAndUnaryReturns.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithComputedCalls

open Silmaril.Isotope.LambdaSSA.Region
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls (Step ReturnFragment computedCall)
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

set_option backward.isDefEq.respectTransparency false

theorem generated_call {X : τ} {a : Tm Φ}
    (p : Φ) (ha : Tm.HasType [X] a (instrSrc p))
    (ga : Generated S (Lit (returnRegion_typed ha))) :
    Generated S (Lit (returnRegion_typed (.op (f := p) ha))) := by
  let hv : Tm.BranchValue [instrSrc p] (.var 0 : Tm Φ) (instrSrc p : τ) := .var rfl
  let hc := Tm.HasType.op (f := p) hv.hasType
  have eq : Lit (returnRegion_typed (.op (f := p) ha)) =
      Lit (returnRegion_typed (.let₁ ha (hc.rename ((Ren.wk [] X).lift (instrSrc p))))) :=
    (ofRegion_eq_iff S _ _).2 (computedCall pe p ha)
  rw [eq, Paper.WithCaseAndUnaryReturns.returnLet_eq_comp S ha hc]
  exact .comp ga (generated_primitive_branchValue S p hv)

theorem generated_returnFragment {X D : τ} {a : Tm Φ} {ha : Tm.HasType [X] a D}
    (h : ReturnFragment pe ha) : Generated S (Lit (returnRegion_typed ha)) := by
  induction h with
  | value hv =>
    exact ((ofRegion_eq_iff S _ (.br (ℓ := 0) rfl hv)).2
      (.paper (.cfgEta (.native (.base (CfgEta.TypeCategory.returnRegion_branchValue hv)))))).symm ▸
      generated_branchValue S hv
  | @call X a p ha _ ga => exact generated_call pe p ha ga
  | @seq X A D a b ha hb _ _ ga gb =>
    rw [Paper.WithCaseAndUnaryReturns.returnLet_eq_comp S ha hb]
    exact .comp ga gb
  | @caseInput A B D a b ha hb pa pb _ _ ga gb =>
    let lhs := returnRegion_typed (.case (.var (i := 0) rfl)
      (ha.rename ((Ren.wk [] (coprod A B)).lift A)) (hb.rename ((Ren.wk [] (coprod A B)).lift B)))
    let rhs := caseValueBranches (returnRegion_typed ha) (returnRegion_typed hb)
    have eq : Lit lhs = Lit rhs := (ofRegion_eq_iff S lhs rhs).2
      (.extra lhs.hasType rhs.hasType (.inl (.inl (.inl (.inr (.split ha hb pa pb))))))
    exact eq.symm ▸ Generated.caseOnInput S _ _ ga gb

private theorem map_sequence {X A D : τ} {r s : Region Φ}
    (hr : ValueBranches [X] r [A]) (hs : ValueBranches [A] s [D]) :
    Lit hr ≫ Lit hs = Lit (seqValueBranches hr hs) :=
  ((projection S).map_comp (Paper.TypeCategory.ofRegion hr) (Paper.TypeCategory.ofRegion hs)).symm.trans
    (congrArg (projection S).map (Paper.TypeCategory.ofRegion_comp hr hs (seqValueBranches hr hs)))

theorem generated_literalLet {X A D : τ} {a : Tm Φ} {r : Region Φ}
    (ha : Tm.HasType [X] a A) (hr : ValueBranches [A, X] r [D])
    (agree : Lit (returnRegion_typed ha) = Lit (returnOnce_typed ha))
    (ga : Generated S (Lit (returnRegion_typed ha)))
    (gr : Generated S (Lit (unpackBody_typed hr))) :
    Generated S (Lit (.let₁ ha hr)) := by
  let prod := returnOnce_typed ha
  let packed := unpackBody_typed hr
  let assembly := seqValueBranches (seqValueBranches (diagonal_typed X) (whiskerLeftRegion_typed X prod)) packed
  have rewrite := (ofRegion_eq_iff S assembly (.let₁ ha hr)).2
    (.paper (Paper.RetainedLet.literal_let ha hr.hasType))
  have left : (whiskerLeftFunctor S (ofType S X)).map (Lit prod) = Lit (whiskerLeftRegion_typed X prod) :=
    (whiskerLeft_map S (Paper.TypeCategory.ofRegion prod)).trans
      (congrArg (projection S).map (Paper.TypeCategory.whiskerLeft_ofRegion X prod))
  have assembled : Lit assembly =
      (Lit (diagonal_typed X) ≫ Lit (whiskerLeftRegion_typed X prod)) ≫ Lit packed :=
    (map_sequence pe (seqValueBranches (diagonal_typed X) (whiskerLeftRegion_typed X prod)) packed).symm.trans
      (congrArg (· ≫ Lit packed) (map_sequence pe (diagonal_typed X) (whiskerLeftRegion_typed X prod)).symm)
  rw [← rewrite, assembled, ← left, ← agree]
  exact .comp (.comp (.copy X) (.left X ga)) gr

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithComputedCalls

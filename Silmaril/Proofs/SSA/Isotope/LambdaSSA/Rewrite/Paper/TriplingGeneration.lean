module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.Generation.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Generation.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseAndUnaryReturns.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedLet.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedCase.Distributor.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingGeneration

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region CategoryTheory CategoryTheory.Limits
open Paper.WithCaseReturns.BinaryFold.WithTripling (Step GuardedFragment capturedDispatcher)
open Paper.Extension.Singleton
open Paper.Extension.Singleton.Generation (Generated generated_branchValue generated_primitive_branchValue)
open CfgEta.TypeCategory (returnRegion returnRegion_typed seqValueBranches caseValueBranches
  whiskerLeftRegion_typed whiskerRightRegion_typed productFstBranches productSndBranches)
open Paper.RetainedLet (returnOnce_typed diagonal_typed unpackBody_typed)
open Paper.SingletonReification.BinaryLet (applyPackedPair_typed returnPair_typed)
open Paper.RetainedCase (returnSum_typed)
open Paper.Extension.Singleton.ValueCoproducts (exactCopair)
open CfgEta.TypeCategory.Retained (distributorRegion_typed)

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

set_option hygiene false in
local notation "T" => Step (τ := τ) (Φ := Φ) pe
local notation "Lit" => ofRegion T
local notation "P" => projection T
local notation "Obj" => ofType T

set_option backward.isDefEq.respectTransparency false

theorem generated_returnFragment {X D : τ} {a : Tm Φ} {ha : Tm.HasType [X] a D}
    (h : Paper.WithCaseAndUnaryReturns.ReturnFragment pe ha) :
    Generated T (Lit (returnRegion_typed ha)) := by
  induction h with
  | value hv =>
    exact ((ofRegion_eq_iff T _ (.br (ℓ := 0) rfl hv)).2
      (.paper (.cfgEta (.native (.base (CfgEta.TypeCategory.returnRegion_branchValue hv)))))).symm ▸
      generated_branchValue T hv
  | primitive p hv => exact generated_primitive_branchValue T p hv
  | @seq X A D a b ha hb _ _ ga gb =>
    rw [Paper.WithCaseAndUnaryReturns.returnLet_eq_comp T ha hb]
    exact .comp ga gb
  | @caseInput A B D a b ha hb pa pb _ _ ga gb =>
    let lhs := returnRegion_typed (.case (.var (i := 0) rfl)
      (ha.rename ((Ren.wk [] (coprod A B)).lift A)) (hb.rename ((Ren.wk [] (coprod A B)).lift B)))
    let rhs := caseValueBranches (returnRegion_typed ha) (returnRegion_typed hb)
    have eq : Lit lhs = Lit rhs := (ofRegion_eq_iff T lhs rhs).2
      (.extra lhs.hasType rhs.hasType (.inl (.inl (.inr (.split ha hb pa pb)))))
    exact eq.symm ▸ Generated.caseOnInput T _ _ ga gb

theorem generated_computedCall_of_rewrite {X : τ} {a : Tm Φ}
    (p : Φ) (ha : Tm.HasType [X] a (instrSrc p))
    (rewrite : Paper.WithCaseReturns.BinaryFold.WithTripling.Eqv pe [X]
      (returnRegion (.op p a)) (returnRegion (.let₁ a (.op p (.var 0)))) [instrTrg p])
    (ga : Generated T (Lit (returnRegion_typed ha))) :
    Generated T (Lit (returnRegion_typed (.op (f := p) ha))) := by
  let hv : Tm.BranchValue [instrSrc p] (.var 0 : Tm Φ) (instrSrc p : τ) := .var rfl
  let hc := Tm.HasType.op (f := p) hv.hasType
  let body := hc.rename ((Ren.wk [] X).lift (instrSrc p))
  have eq : Lit (returnRegion_typed (.op (f := p) ha)) =
      Lit (returnRegion_typed (.let₁ ha body)) :=
    (ofRegion_eq_iff T _ _).2 rewrite
  rw [eq, Paper.WithCaseAndUnaryReturns.returnLet_eq_comp T ha hc]
  exact .comp ga (generated_primitive_branchValue T p hv)

private theorem generated_seq {X A D : τ} {r s : Region Φ}
    (hr : ValueBranches [X] r [A]) (hs : ValueBranches [A] s [D])
    (gr : Generated T (Lit hr)) (gs : Generated T (Lit hs)) :
    Generated T (Lit (seqValueBranches hr hs)) := by
  have eq : Lit hr ≫ Lit hs = Lit (seqValueBranches hr hs) :=
    ((P).map_comp (Paper.TypeCategory.ofRegion hr) (Paper.TypeCategory.ofRegion hs)).symm.trans
      (congrArg (P).map (Paper.TypeCategory.ofRegion_comp hr hs (seqValueBranches hr hs)))
  exact eq ▸ .comp gr gs

private theorem generated_left (X : τ) {A D : τ} {r : Region Φ} (hr : ValueBranches [A] r [D])
    (gr : Generated T (Lit hr)) :
    Generated T (Lit (whiskerLeftRegion_typed X hr)) := by
  have eq : (whiskerLeftFunctor T (ofType T X)).map (Lit hr) =
      Lit (whiskerLeftRegion_typed X hr) :=
    (whiskerLeft_map T (Paper.TypeCategory.ofRegion hr)).trans
      (congrArg (P).map (Paper.TypeCategory.whiskerLeft_ofRegion X hr))
  exact eq ▸ Generated.left X gr

private theorem generated_right (X : τ) {A D : τ} {r : Region Φ} (hr : ValueBranches [A] r [D])
    (gr : Generated T (Lit hr)) :
    Generated T (Lit (whiskerRightRegion_typed X hr)) := by
  have eq : (whiskerRightFunctor T (ofType T X)).map (Lit hr) =
      Lit (whiskerRightRegion_typed X hr) :=
    (whiskerRight_map T (Paper.TypeCategory.ofRegion hr)).trans
      (congrArg (P).map (Paper.TypeCategory.whiskerRight_ofRegion X hr))
  exact eq ▸ Generated.right X gr

private theorem generated_retained {X A D : τ} {a b : Region Φ}
    (ha : ValueBranches [X] a [A]) (hb : ValueBranches [product X A] b [D])
    (ga : Generated T (Lit ha)) (gb : Generated T (Lit hb)) :
    Generated T (Lit (seqValueBranches
      (seqValueBranches (diagonal_typed X) (whiskerLeftRegion_typed X ha)) hb)) := by
  exact generated_seq pe _ _ (generated_seq pe _ _ (.copy X) (generated_left pe X ha ga)) gb

theorem generated_guardedFragment {X D : τ} {r : Region Φ} {hr : ValueBranches [X] r [D]}
    (h : GuardedFragment pe hr) : Generated T (Lit hr) := by
  induction h with
  | initial h => exact .initial (Lit h)
  | branch hv => exact generated_branchValue T hv
  | returned h => exact generated_returnFragment pe h
  | fst A B => exact .fst A B
  | snd A B => exact .snd A B
  | @seq X A D r s hr hs _ _ gr gs => exact generated_seq pe hr hs gr gs
  | @left X A D r hr _ gr => exact generated_left pe X hr gr
  | @right X A D r hr _ gr => exact generated_right pe X hr gr
  | @let₁ X A D a r ha hr _ _ ga gr =>
    let body := unpackBody_typed hr
    let assembled := seqValueBranches
      (seqValueBranches (diagonal_typed X) (whiskerLeftRegion_typed X (returnOnce_typed ha))) body
    have eq := (ofRegion_eq_iff T assembled (.let₁ ha hr)).2
      (.paper (Paper.RetainedLet.literal_let ha hr.hasType))
    exact eq ▸ generated_retained pe (returnOnce_typed ha) body ga gr
  | @let₂ X A B D a p ha hp _ _ ga gp =>
    let assembled := seqValueBranches
      (seqValueBranches (diagonal_typed X) (whiskerLeftRegion_typed X (returnPair_typed ha))) hp
    have eq := (ofRegion_eq_iff T assembled (.let₂ ha (applyPackedPair_typed hp))).2
      (.paper (Paper.SingletonReification.BinaryLet.literal_let₂ ha hp))
    exact eq ▸ generated_retained pe (returnPair_typed ha) hp ga gp
  | @caseInput A B D l r hl hr _ _ gl gr => exact Generated.caseOnInput T hl hr gl gr
  | @caseRetained X A B D a l r ha hl hr _ _ _ ga gl gr =>
    exact Generated.retainedCase T ha hl hr ga gl gr
  | @cfgZero X D e he blocks _ ge =>
    have eq := (ofRegion_eq_iff T (.cfg Fin.elim0 he (fun i => i.elim0)) he).2
      (.paper (.cfgEta (.native (.base (.entry (.cfgZero he.hasType blocks))))))
    exact eq.symm ▸ ge
  | @iterate X D r hr _ gr =>
    have eq : iterateSum T (Lit hr) = Lit (SyntacticCategory.iterateRegion_valueBranches hr) :=
      (iterateSum_map T (Paper.TypeCategory.ofRegion hr)).trans
        (congrArg (P).map (Paper.TypeCategory.iterateSum_ofRegion hr))
    exact eq ▸ Generated.iterate gr
  | @eqv X D r s hr hs eq _ gr => exact ((ofRegion_eq_iff T hr hs).2 eq) ▸ gr

theorem generated_iff_representatives :
    (∀ {X D : τ} (f : ofType T X ⟶ ofType T D), Generated T f) ↔
    (∀ {X D : τ} {r : Region Φ} (hr : ValueBranches [X] r [D]), Generated T (Lit hr)) := by
  refine ⟨fun all {_ _ _} hr => all (Lit hr), ?_⟩
  intro all X D f
  obtain ⟨p, rfl⟩ := (P).map_surjective f
  obtain ⟨r, hr, rfl⟩ := Paper.TypeCategory.exists_ofRegion p
  exact all hr

theorem generated_capturedDispatcher (X D : τ) (L : LCtx τ)
    (rows : ∀ i : Fin L.length, ofType T (product X (L.get i)) ⟶ ofType T D)
    (generated : ∀ i, Generated T (rows i)) :
    Generated T (capturedDispatcher pe X L rows) := by
  induction L with
  | nil =>
    rw [capturedDispatcher]
    exact .comp (.snd X Silmaril.empty) (.initial _)

  | cons A L tail =>
    rw [capturedDispatcher]
    exact .comp (Paper.Extension.Singleton.Generation.generated_distributor T X A (packedExitType L))
      (.copair (generated 0) (tail (fun i => rows i.succ) (fun i => generated i.succ)))

theorem capturedDispatcher_head_tail (X A D : τ) (L : LCtx τ)
    (rows : ∀ i : Fin (A :: L).length, Obj (product X ((A :: L).get i)) ⟶ Obj D) :
    let whisker := whiskerLeftFunctor T (Obj X)
    let sum := sumCofan T A (packedExitType L)
    (whisker.map sum.inl ≫ capturedDispatcher pe X (A :: L) rows = rows 0) ∧
      (whisker.map sum.inr ≫ capturedDispatcher pe X (A :: L) rows =
        capturedDispatcher pe X L (fun i => rows i.succ)) := by
  let S := packedExitType L
  let left := rows 0
  let right := capturedDispatcher pe X L (fun i => rows i.succ)
  let dist := Lit (distributorRegion_typed X A S)
  let sum := sumCofan T A S
  let out := sumCofan T (product X A) (product X S)
  let whisker := whiskerLeftFunctor T (Obj X)
  have inl : whisker.map sum.inl ≫ dist = out.inl := by
    rw [show whisker.map sum.inl = (P).map (Paper.TypeCategory.whiskerLeft
      (Paper.TypeCategory.ofType X) (Paper.TypeCategory.sumCofan A S).inl) from rfl,
      ← (P).map_comp]
    exact congrArg (P).map (Paper.RetainedCase.left_distributor_inl (Φ := Φ) X A S)
  have inr : whisker.map sum.inr ≫ dist = out.inr := by
    rw [show whisker.map sum.inr = (P).map (Paper.TypeCategory.whiskerLeft
      (Paper.TypeCategory.ofType X) (Paper.TypeCategory.sumCofan A S).inr) from rfl,
      ← (P).map_comp]
    exact congrArg (P).map (Paper.RetainedCase.left_distributor_inr (Φ := Φ) X A S)
  change (whisker.map sum.inl ≫ dist ≫ exactCopair T left right = left) ∧
    (whisker.map sum.inr ≫ dist ≫ exactCopair T left right = right)
  constructor
  · rw [← Category.assoc, inl]
    exact (sumCofanIsColimit T (product X A) (product X S)).fac (BinaryCofan.mk left right) ⟨WalkingPair.left⟩
  · rw [← Category.assoc, inr]
    exact (sumCofanIsColimit T (product X A) (product X S)).fac (BinaryCofan.mk left right) ⟨WalkingPair.right⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingGeneration

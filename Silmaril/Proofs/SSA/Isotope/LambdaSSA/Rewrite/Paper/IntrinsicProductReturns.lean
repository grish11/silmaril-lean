module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedLet.Generation.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.Thms

/-! # Exact elaboration of the intrinsic product-return fragment -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.IntrinsicProductReturns

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region CategoryTheory
open Paper.WithComputedProductProducers.Intrinsic (Term Program)
open Paper.WithPairReturns (ReturnFragmentWithRules)
open Paper.WithProductDestructureReturns (GuardedFragmentWithProducts)
open Paper.Extension.Singleton (ofRegion ofRegion_eq_iff ofType)
open Paper.SingletonReification.BinaryLet (returnPair_typed applyPackedPair_typed literal_let₂)
open Paper.RetainedLet (returnOnce_typed diagonal_typed unpackBody_typed unpackTerm_typed
  unpack_return_applyPackedTerm)
open Paper.PackedBody (applyPackedTerm_typed)
open CfgEta.TypeCategory (returnRegion_typed returnRegion_branchValue seqValueBranches whiskerLeftRegion_typed)

universe u v w

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

set_option hygiene false in
local notation "Join" => Paper.WithComputedProductProducers.JoinedStep (τ := τ) (Φ := Φ) pe

local notation "P" => Paper.Extension.Singleton.projection Join

set_option backward.isDefEq.respectTransparency false in
theorem term_fragment {X D : τ} (t : Term Φ X D) :
    ReturnFragmentWithRules pe true true t.elaborate.property := by
  induction t with
  | input => exact .value (.var rfl)
  | unit => exact .value .unit
  | call p _ ih => exact .call p rfl ih
  | pair _ _ ia ib => exact .pair ia ib
  | seq _ _ ia ib => exact .seq ia ib
  | fst A B => exact .fst A B
  | snd A B => exact .snd A B
  | destructure _ _ _ ih => exact .destructure rfl ih

set_option backward.isDefEq.respectTransparency false in
theorem program_fragment {X D : τ} (p : Program Φ X D) :
    GuardedFragmentWithProducts pe true p.elaborate.property := by
  induction p with
  | returned t => exact .returned (term_fragment pe t)
  | branchInput => exact .branch (.var rfl)
  | let₂ _ _ a _ ih => exact .let₂Computed (term_fragment pe a) ih

private theorem pairSeed {Γ L : List τ} {r s : Region Φ}
    (h : Paper.WithPairReturns.JoinedStep pe Γ r s L) : Join Γ r s L :=
  .inl (.inl (.inl h))

private theorem unarySeed {Γ L : List τ} {r s : Region Φ}
    (h : Paper.UnaryReturn.Step Γ r s L) : Join Γ r s L :=
  pairSeed pe (.inl (.inr (.inl h)))

private theorem ofBranchInput (X : τ) :
    ofRegion Join (.br (ℓ := 0) rfl (.var (i := 0) rfl) : ValueBranches [X] (.br 0 (.var 0)) [X]) =
      𝟙 (ofType Join X) :=
  (congrArg (P).map (Paper.TypeCategory.ofRegion_id (τ := τ) (Φ := Φ) X)).trans ((P).map_id _)

private theorem return_branch {X A : τ} {a : Tm Φ} (ha : Tm.BranchValue [X] a A) :
    ofRegion Join (returnRegion_typed ha.hasType) = ofRegion Join (.br (ℓ := 0) rfl ha) :=
  (ofRegion_eq_iff Join _ _).2 (.paper (.cfgEta (.native (.base (returnRegion_branchValue ha)))))

set_option backward.isDefEq.respectTransparency false in
theorem term_arrow_eq_generator {X D : τ} (t : Term Φ X D) :
    ofRegion Join (returnRegion_typed t.elaborate.property) = t.generatorArrow Join := by
  induction t with
  | @input X =>
    exact (return_branch pe (.var (i := 0) rfl)).trans (ofBranchInput pe X)
  | unit => exact return_branch pe .unit
  | @call X p a ih =>
    let ha := a.elaborate.property
    let inner : Tm.HasType [instrSrc (τ := τ) p] (.op p (.var 0)) (instrTrg (τ := τ) p) := .op (.var rfl)
    let step := Paper.WithComputedCallReturns.Step.seq p ha
    have comparison := (ofRegion_eq_iff Join (returnRegion_typed (.op ha))
      (returnRegion_typed (.let₁ ha (inner.rename ((Ren.wk [] X).lift (instrSrc (τ := τ) p)))))).2
      (.extra step.valueBranches.1.hasType step.valueBranches.2.hasType (.inl (.inl (.inr step))))
    simp only [Term.elaborate, Term.generatorArrow]
    rw [comparison, Paper.WithCaseAndUnaryReturns.returnLet_eq_comp Join ha inner, ih]
    rfl
  | pair a b ia ib =>
    simp only [Term.elaborate, Term.generatorArrow]
    rw [Paper.WithPairReturns.returnPair_eq_pairArrows Join (fun step => pairSeed pe (.inr step))
      (unarySeed pe) a.elaborate.property b.elaborate.property, ia, ib]
  | seq a b ia ib =>
    simp only [Term.elaborate, Term.generatorArrow]
    rw [Paper.WithCaseAndUnaryReturns.returnLet_eq_comp Join a.elaborate.property b.elaborate.property, ia, ib]
  | fst A B =>
    let step := Paper.WithProjectionReturns.Step.fst (Φ := Φ) A B
    exact (ofRegion_eq_iff Join _ _).2
      (.extra step.valueBranches.1.hasType step.valueBranches.2.hasType (pairSeed pe (.inl (.inl (.inl step)))))
  | snd A B =>
    let step := Paper.WithProjectionReturns.Step.snd (Φ := Φ) A B
    exact (ofRegion_eq_iff Join _ _).2
      (.extra step.valueBranches.1.hasType step.valueBranches.2.hasType (pairSeed pe (.inl (.inl (.inl step)))))
  | destructure A B body ih =>
    let ht := applyPackedTerm_typed body.elaborate.property
    let step := Paper.WithProductDestructureReturns.Step.unpack ht
    have eq := (ofRegion_eq_iff Join (unpackBody_typed (returnRegion_typed ht))
      (returnRegion_typed (unpackTerm_typed ht))).2
      (.extra step.valueBranches.1.hasType step.valueBranches.2.hasType (.inl (.inr step)))
    exact eq.symm.trans ((unpack_return_applyPackedTerm Join (unarySeed pe) body.elaborate.property).trans ih)

private theorem seq_arrow {X A D : τ} {r s : Region Φ}
    (hr : ValueBranches [X] r [A]) (hs : ValueBranches [A] s [D]) :
    ofRegion Join (seqValueBranches hr hs) = ofRegion Join hr ≫ ofRegion Join hs :=
  (congrArg (P).map (Paper.TypeCategory.ofRegion_comp hr hs (seqValueBranches hr hs)).symm).trans
    ((P).map_comp (Paper.TypeCategory.ofRegion hr) (Paper.TypeCategory.ofRegion hs))

private theorem left_arrow (X : τ) {A D : τ} {r : Region Φ} (hr : ValueBranches [A] r [D]) :
    ofRegion Join (whiskerLeftRegion_typed X hr) =
      (Paper.Extension.Singleton.whiskerLeftFunctor Join (ofType Join X)).map (ofRegion Join hr) :=
  (congrArg (P).map (Paper.TypeCategory.whiskerLeft_ofRegion X hr).symm).trans
    (Paper.Extension.Singleton.whiskerLeft_map Join (Paper.TypeCategory.ofRegion hr)).symm

set_option backward.isDefEq.respectTransparency false in
theorem program_arrow_eq_generator {X D : τ} (p : Program Φ X D) :
    p.arrow pe = p.generatorArrow Join := by
  induction p with
  | returned t => exact term_arrow_eq_generator pe t
  | branchInput => exact ofBranchInput pe _
  | @let₂ X D A B a body ih =>
    let ha := a.elaborate.property
    let hp := body.elaborate.property
    let producer := returnPair_typed ha
    let diag := diagonal_typed (Φ := Φ) X
    have producer_eq : ofRegion Join producer = a.generatorArrow Join :=
      ((ofRegion_eq_iff Join producer (returnOnce_typed ha)).2
        (Paper.WithComputedProductProducers.productProducerAgreement pe ha)).trans
          (((ofRegion_eq_iff Join (returnRegion_typed ha) (returnOnce_typed ha)).2
            (Paper.UnaryReturn.returnRegion_eq_returnOnce (unarySeed pe) ha)).symm.trans
              (term_arrow_eq_generator pe a))
    let step := whiskerLeftRegion_typed X producer
    let retained := seqValueBranches diag step
    have assemble := (ofRegion_eq_iff Join (seqValueBranches retained hp) (.let₂ ha (applyPackedPair_typed hp))).2
      (.paper (literal_let₂ ha hp))
    change ofRegion Join hp = body.generatorArrow Join at ih
    simp only [Program.arrow, Program.elaborate, Program.generatorArrow]
    rw [← assemble, seq_arrow pe retained hp, seq_arrow pe diag step, left_arrow pe X producer, producer_eq, ih]
    rfl

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.IntrinsicProductReturns

module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProductDestructureReturns.Generation.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProductDestructureReturns.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseAndUnaryReturns.Thms

/-! # Generation of the guarded singleton representative grammar -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.GuardedSingletonGeneration

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithProductDestructureReturns
open Paper.RetainedCase (returnSum_typed)
open Paper.WithPairReturns (ReturnFragmentWithRules generated_returnFragment_with_rules)
open Paper.PackedBody (applyPacked_typed unpack_applyPacked)
open Paper.RetainedLet (diagonal_typed returnOnce_typed unpackBody_typed)
open Paper.SingletonReification.BinaryLet
open Paper.Extension.Singleton (ofRegion ofRegion_eq_iff)
open Paper.Extension.Singleton.Generation (Generated generated_branchValue)
open CfgEta.TypeCategory (returnRegion_typed seqValueBranches
  caseValueBranches whiskerLeftRegion_typed whiskerRightRegion_typed)
open CategoryTheory

universe u v w

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

variable (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)
  (includeJoin : ∀ {Γ L r s}, JoinedStep pe Γ r s L → Seed Γ r s L)

local notation "P" => Paper.Extension.Singleton.projection Seed

include includeJoin in
private theorem includeCaseUnary {Γ L : List τ} {r s : Region Φ}
    (h : Paper.WithCaseAndUnaryReturns.Step pe Γ r s L) : Seed Γ r s L :=
  includeJoin (.inl (.inl (.inl (.inr h))))

include includeJoin in
private theorem generated_term {X D : τ} {a : Tm Φ} {ha : Tm.HasType [X] a D}
    (h : ReturnFragmentWithRules pe true true ha) : Generated Seed (ofRegion Seed (returnRegion_typed ha)) := by
  apply generated_returnFragment_with_rules pe Seed (fun step => includeJoin (.inl (.inl step))) _ _ h
  · intro _ _ _ p ht
    let step := Paper.WithComputedCallReturns.Step.seq p ht
    exact .extra step.valueBranches.1.hasType step.valueBranches.2.hasType (includeJoin (.inl (.inr step)))
  · intro _ _ _ _ _ hb
    let step := Step.unpack hb
    exact .extra step.valueBranches.1.hasType step.valueBranches.2.hasType (includeJoin (.inr step))

set_option backward.isDefEq.respectTransparency false in
private theorem generated_seq {X A D : τ} {r s : Region Φ}
    (hr : ValueBranches [X] r [A]) (hs : ValueBranches [A] s [D])
    (gr : Generated Seed (ofRegion Seed hr)) (gs : Generated Seed (ofRegion Seed hs)) :
    Generated Seed (ofRegion Seed (seqValueBranches hr hs)) := by
  have eq : ofRegion Seed hr ≫ ofRegion Seed hs = ofRegion Seed (seqValueBranches hr hs) :=
    ((P).map_comp (Paper.TypeCategory.ofRegion hr) (Paper.TypeCategory.ofRegion hs)).symm.trans
      (congrArg (P).map (Paper.TypeCategory.ofRegion_comp hr hs (seqValueBranches hr hs)))
  exact eq ▸ Generated.comp gr gs

set_option backward.isDefEq.respectTransparency false in
private theorem generated_left (X : τ) {A D : τ} {r : Region Φ} (hr : ValueBranches [A] r [D])
    (gr : Generated Seed (ofRegion Seed hr)) :
    Generated Seed (ofRegion Seed (whiskerLeftRegion_typed X hr)) := by
  have eq : (Paper.Extension.Singleton.whiskerLeftFunctor Seed
        (Paper.Extension.Singleton.ofType Seed X)).map (ofRegion Seed hr) =
      ofRegion Seed (whiskerLeftRegion_typed X hr) :=
    (Paper.Extension.Singleton.whiskerLeft_map Seed (Paper.TypeCategory.ofRegion hr)).trans
      (congrArg (P).map (Paper.TypeCategory.whiskerLeft_ofRegion X hr))
  exact eq ▸ Generated.left X gr

set_option backward.isDefEq.respectTransparency false in
private theorem generated_right (X : τ) {A D : τ} {r : Region Φ} (hr : ValueBranches [A] r [D])
    (gr : Generated Seed (ofRegion Seed hr)) :
    Generated Seed (ofRegion Seed (whiskerRightRegion_typed X hr)) := by
  have eq : (Paper.Extension.Singleton.whiskerRightFunctor Seed
        (Paper.Extension.Singleton.ofType Seed X)).map (ofRegion Seed hr) =
      ofRegion Seed (whiskerRightRegion_typed X hr) :=
    (Paper.Extension.Singleton.whiskerRight_map Seed (Paper.TypeCategory.ofRegion hr)).trans
      (congrArg (P).map (Paper.TypeCategory.whiskerRight_ofRegion X hr))
  exact eq ▸ Generated.right X gr

private theorem generated_unpack {X A D : τ} {p : Region Φ} (hp : ValueBranches [product X A] p [D])
    (gp : Generated Seed (ofRegion Seed hp)) :
    Generated Seed (ofRegion Seed (unpackBody_typed (applyPacked_typed hp))) :=
  ((ofRegion_eq_iff Seed _ hp).2 (.paper (unpack_applyPacked hp))).symm ▸ gp

set_option backward.isDefEq.respectTransparency false in
include includeJoin in
private theorem generated_once {X A : τ} {a : Tm Φ} {ha : Tm.HasType [X] a A}
    (producer : ReturnFragmentWithRules pe true true ha) :
    Generated Seed (ofRegion Seed (returnOnce_typed ha)) := by
  have eq := (ofRegion_eq_iff Seed (returnRegion_typed ha) (returnOnce_typed ha)).2
    (Paper.UnaryReturn.returnRegion_eq_returnOnce (fun step => includeCaseUnary pe Seed includeJoin (.inl step)) ha)
  exact eq ▸ generated_term pe Seed includeJoin producer

set_option backward.isDefEq.respectTransparency false in
include includeJoin in
private theorem generated_product {X A B : τ} {a : Tm Φ} {ha : Tm.HasType [X] a (product A B)}
    (h : ConstructorProduct ha) : Generated Seed (ofRegion Seed (returnPair_typed ha)) := by
  cases h with
  | var hi =>
    exact ((ofRegion_eq_iff Seed _ _).2 (.paper (returnPair_variable hi))).symm ▸
      generated_once pe Seed includeJoin (.value (.var hi))
  | pair hl hr =>
    exact ((ofRegion_eq_iff Seed _ _).2 (.paper (returnPair_pair hl hr))).symm ▸
      generated_once pe Seed includeJoin (.value (.pair hl hr))

set_option backward.isDefEq.respectTransparency false in
private theorem generated_binary {X A B D : τ} {a : Tm Φ} {p : Region Φ}
    (ha : Tm.HasType [X] a (product A B)) (hp : ValueBranches [product X (product A B)] p [D])
    (ga : Generated Seed (ofRegion Seed (returnPair_typed ha)))
    (gp : Generated Seed (ofRegion Seed hp)) :
    Generated Seed (ofRegion Seed (.let₂ ha (applyPackedPair_typed hp))) := by
  let diag := diagonal_typed (Φ := Φ) X
  let step := whiskerLeftRegion_typed X (returnPair_typed ha)
  let retained := seqValueBranches diag step
  have eq := (ofRegion_eq_iff Seed (seqValueBranches retained hp) (.let₂ ha (applyPackedPair_typed hp))).2
    (.paper (literal_let₂ ha hp))
  exact eq ▸ generated_seq Seed retained hp (generated_seq Seed diag step (.copy X) (generated_left Seed X _ ga)) gp

set_option backward.isDefEq.respectTransparency false in
include includeJoin in
theorem generated_let₂_of_returnPair_eq_returnOnce {X A B D : τ} {a : Tm Φ} {p : Region Φ}
    {ha : Tm.HasType [X] a (product A B)} {hp : ValueBranches [product X (product A B)] p [D]}
    (producer : ReturnFragmentWithRules pe true true ha)
    (eq : Paper.Extension.Eqv Seed [X] (returnPair a) (Paper.RetainedLet.returnOnce a) [product A B])
    (body : Generated Seed (ofRegion Seed hp)) :
    Generated Seed (ofRegion Seed (.let₂ ha (applyPackedPair_typed hp))) :=
  generated_binary Seed ha hp
    (((ofRegion_eq_iff Seed (returnPair_typed ha) (returnOnce_typed ha)).2 eq).symm ▸
      generated_once pe Seed includeJoin producer) body

set_option backward.isDefEq.respectTransparency false in
include includeJoin in
private theorem generated_tagLeft {X A B : τ} {a : Tm Φ} {ha : Tm.HasType [X] a A}
    (producer : ReturnFragmentWithRules pe true true ha) :
    Generated Seed (ofRegion Seed
      (returnSum_typed (.inl ha : Tm.HasType [X] (.inl a) (coprod A B)))) := by
  let left : Tm.BranchValue [A] (.inl (.var 0) : Tm Φ) (coprod A B) := .inl (.var rfl)
  have result := generated_seq Seed (returnOnce_typed ha) (.br (ℓ := 0) rfl left)
    (generated_once pe Seed includeJoin producer) (generated_branchValue Seed left)
  refine ((ofRegion_eq_iff Seed _ (seqValueBranches (returnOnce_typed ha) (.br (ℓ := 0) rfl left))).2 ?_).symm ▸ result
  exact .paper (.cfgEta (.native (.base
    (.caseInl ha (.br rfl (.inl (.var rfl))) (.br rfl (.inr (.var rfl)))))))

set_option backward.isDefEq.respectTransparency false in
include includeJoin in
private theorem generated_tagRight {X A B : τ} {a : Tm Φ} {ha : Tm.HasType [X] a B}
    (producer : ReturnFragmentWithRules pe true true ha) :
    Generated Seed (ofRegion Seed
      (returnSum_typed (.inr ha : Tm.HasType [X] (.inr a) (coprod A B)))) := by
  let right : Tm.BranchValue [B] (.inr (.var 0) : Tm Φ) (coprod A B) := .inr (.var rfl)
  have result := generated_seq Seed (returnOnce_typed ha) (.br (ℓ := 0) rfl right)
    (generated_once pe Seed includeJoin producer) (generated_branchValue Seed right)
  refine ((ofRegion_eq_iff Seed _ (seqValueBranches (returnOnce_typed ha) (.br (ℓ := 0) rfl right))).2 ?_).symm ▸ result
  exact .paper (.cfgEta (.native (.base
    (.caseInr ha (.br rfl (.inl (.var rfl))) (.br rfl (.inr (.var rfl)))))))

set_option backward.isDefEq.respectTransparency false in
include includeJoin in
theorem generated_guardedFragment {computedProducts : Bool}
    (products : computedProducts = true → ProductProducerAgreement Seed)
    {X D : τ} {r : Region Φ} {hr : ValueBranches [X] r [D]}
    (h : GuardedFragmentWithProducts pe computedProducts hr) : Generated Seed (ofRegion Seed hr) := by
  induction h with
  | initial hr => exact .initial (ofRegion Seed hr)
  | branch hv => exact generated_branchValue Seed hv
  | returned h => exact generated_term pe Seed includeJoin h
  | @seq X A D r s hr hs _ _ gr gs => exact generated_seq Seed hr hs gr gs
  | @left X A D r hr _ gr => exact generated_left Seed X hr gr
  | @right X A D r hr _ gr => exact generated_right Seed X hr gr
  | @let₁ X A D a p ha hp ga _ gp =>
    exact Paper.WithCaseAndUnaryReturns.generated_returnLet pe Seed (includeCaseUnary pe Seed includeJoin) ha
      (applyPacked_typed hp) (generated_term pe Seed includeJoin ga) (generated_unpack Seed hp gp)
  | @let₂ X A B D a p ha hp producer _ gp =>
    cases computedProducts with
    | false => exact generated_binary Seed ha hp (generated_product pe Seed includeJoin producer) gp
    | true =>
      rcases producer with ctor | computed
      · exact generated_binary Seed ha hp (generated_product pe Seed includeJoin ctor) gp
      · exact generated_let₂_of_returnPair_eq_returnOnce pe Seed includeJoin computed (products rfl ha) gp
  | @caseInput A B D l r hl hr _ _ gl gr => exact Generated.caseOnInput Seed hl hr gl gr
  | tagLeft producer => exact generated_tagLeft pe Seed includeJoin producer
  | tagRight producer => exact generated_tagRight pe Seed includeJoin producer
  | @caseRetained X A B D a l r ha hl hr _ _ _ ga gl gr =>
    exact Generated.retainedCase Seed ha (applyPacked_typed hl) (applyPacked_typed hr) ga
      (generated_unpack Seed hl gl) (generated_unpack Seed hr gr)
  | @cfgZero X D r hr blocks _ gr =>
    have eq := (ofRegion_eq_iff Seed (.cfg Fin.elim0 hr (fun i => i.elim0)) hr).2
      (.paper (.cfgEta (.native (.base (.entry (.cfgZero hr.hasType blocks))))))
    exact eq.symm ▸ gr
  | @iterate X D r hr _ gr =>
    have eq : Paper.Extension.Singleton.iterateSum Seed (ofRegion Seed hr) =
        ofRegion Seed (SyntacticCategory.iterateRegion_valueBranches hr) :=
      (Paper.Extension.Singleton.iterateSum_map Seed (Paper.TypeCategory.ofRegion hr)).trans
        (congrArg (P).map (Paper.TypeCategory.iterateSum_ofRegion hr))
    exact eq ▸ Generated.iterate gr

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.GuardedSingletonGeneration

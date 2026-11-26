module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Calls.SumBind.Continuation.Defs
import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Calls.SumBind.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.BranchNormalization.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.ReturnFusion.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedCallReturns.OrderedPairs.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.Thms

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Native.SumBind.Continuation

open Region (HasType ValueBranches)
open Region.Paper
open Region.Paper.RetainedLet (returnOnce)
open Region.Paper.UnaryReturn.Beta.Constructors (inlSequence inrSequence)
open Region.CfgEta.TypeCategory (returnRegion)
open Region.Paper.WithComputedCallReturns
open Silmaril.DeBruijn (lift)
open Morphism.CaseSSA (erase erase_hasType)
open CategoryTheory CategoryTheory.Limits
open LambdaSSA.Semantics.Categorical
open LetIter.Semantics.Categorical (TypeModel InstructionModel)
open scoped MonoidalCategory

set_option backward.isDefEq.respectTransparency false

universe u v w u₁ u₂ v₁ v₂

section Native

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {ε : Type w} [HasEff Φ ε]
  {pe : ε} {Γ Δ : VCtx τ} {L : LCtx τ} {A B D : τ} {f : Φ} {p q : Region Φ}
  {e l r : Tm Φ}

theorem ofSums_proof (h : SumBind.Eqv pe Γ p q L) : Eqv pe Γ p q L :=
  WithProjectionReturnsAndUnitEta.WithBranchBinding.mapSeed Or.inl h

theorem split_return_proof (he : Tm.HasType Γ e (coprod A B)) (hl : Tm.HasType (A :: Γ) l D)
    (hr : Tm.HasType (B :: Γ) r D) :
    Eqv pe Γ (returnOnce (.case e l r)) (.case e (returnOnce l) (returnOnce r)) [D] :=
  .extra (UnaryReturn.returnOnce_valueBranches (.case he hl hr)).hasType
    (.case he (UnaryReturn.returnOnce_valueBranches hl).hasType (UnaryReturn.returnOnce_valueBranches hr).hasType)
    (.inr (.split he hl hr))

theorem split_let₂_proof {a b : Tm Φ}
    (ha : Tm.HasType Γ a (product A B)) (hb : Tm.HasType (B :: A :: Γ) b D) :
    Eqv pe Γ (returnOnce (.let₂ a b)) (.let₂ a (returnOnce b)) [D] :=
  .extra (UnaryReturn.returnOnce_valueBranches (.let₂ ha hb)).hasType
    (.let₂ ha (UnaryReturn.returnOnce_valueBranches hb).hasType)
    (.inr (.splitPair ha hb))

theorem split_inl_proof {a : Tm Φ} (ha : Tm.HasType Γ a A) :
    Eqv pe Γ (returnOnce (.inl a)) (inlSequence a) [coprod A B] :=
  .extra (UnaryReturn.returnOnce_valueBranches (.inl ha)).hasType
    (.let₁ ha (.br (ℓ := 0) rfl (.inl (.var (i := 0) rfl)))) (.inr (.splitInl ha))

theorem split_inr_proof {a : Tm Φ} (ha : Tm.HasType Γ a B) :
    Eqv pe Γ (returnOnce (.inr a)) (inrSequence a) [coprod A B] :=
  .extra (UnaryReturn.returnOnce_valueBranches (.inr ha)).hasType
    (.let₁ ha (.br (ℓ := 0) rfl (.inr (.var (i := 0) rfl)))) (.inr (.splitInr ha))

theorem split_abort_proof {a : Tm Φ} (ha : Tm.HasType Γ a empty) :
    Eqv pe Γ (returnOnce (.abort a)) (.let₁ a (returnOnce (.abort (.var 0)))) [D] :=
  .extra (UnaryReturn.returnOnce_valueBranches (.abort ha)).hasType
    (.let₁ ha (UnaryReturn.returnOnce_valueBranches (.abort (.var (i := 0) rfl))).hasType)
    (.inr (.splitAbort ha))

private theorem invoke_typed (hq : HasType (instrTrg f :: Γ) q L) :
    HasType (instrSrc f :: Γ) (invoke f q) L :=
  .let₁ (.op (.var (i := 0) rfl)) (hq.renameVars ((Ren.wk Γ (instrSrc f)).lift (instrTrg f)))

private theorem call_return_post (f : Φ) (e l r : Tm Φ) (q : Region Φ) :
    (returnRegion (.let₁ (.case e l r) (.op f (.var 0)))).lsubst (fun _ => q) =
      .let₁ (.case e l r) (invoke f q) := by
  change (((Region.br 0 (.case e l r)).bindBranchArguments.lsubst (fun _ =>
    (Region.br 0 (.op f (.var 0))).bindBranchArguments)).lsubst (fun _ => q)) = _
  rw [Region.lsubst_bindBranchArguments_br]
  change Region.let₁ (.case e l r) ((Region.br 0 (.op f (.var 0))).bindBranchArguments.lsubst
    (Region.liftLSubstVars (fun _ => q))) = _
  rw [Region.lsubst_bindBranchArguments_br]
  rfl

theorem call_replay_proof (he : Tm.HasType Γ e (coprod A B)) (hl : Tm.HasType (A :: Γ) l (instrSrc f))
    (hr : Tm.HasType (B :: Γ) r (instrSrc f)) (hq : HasType (instrTrg f :: Γ) q L)
    (scheduled : ValueBranches Γ p [instrSrc f])
    (producer : Eqv pe Γ (.case e (returnOnce l) (returnOnce r)) p [instrSrc f]) :
    Eqv pe Γ (.let₁ (.op f (.case e l r)) q) (p.lsubst (fun _ => invoke f q)) L := by
  let step := Step.seq f (.case he hl hr)
  have sequenced : ConstructorJoin.Eqv pe Γ _ _ [instrTrg f] :=
    ConstructorJoin.ofCall step
  have converted := Extension.Eqv.lsubstPost (K := L) (σ := fun _ => q)
    (ofSums_proof (SumBind.ofProducts (ProductBind.ofPairs (OrderedPairs.ofCalls sequenced))))
    step.valueBranches.1 step.valueBranches.2
    (fun _ _ hi => (List.mem_singleton.mp (List.mem_of_getElem? hi)).symm ▸ hq)
  rw [call_return_post] at converted
  change Eqv pe Γ ((Region.br 0 (.op f (.case e l r))).bindBranchArguments.lsubst (fun _ => q)) _ L
    at converted
  rw [Region.lsubst_bindBranchArguments_br] at converted
  have exposed := (split_return_proof (pe := pe) he hl hr).trans producer
  have plugged := Extension.Eqv.lsubstPost (K := L) (σ := fun _ => invoke f q) exposed
    (UnaryReturn.returnOnce_valueBranches (.case he hl hr)) scheduled
    (fun _ _ hi => (List.mem_singleton.mp (List.mem_of_getElem? hi)).symm ▸ invoke_typed hq)
  change Eqv pe Γ ((Region.br 0 (.case _ _ _)).bindBranchArguments.lsubst _) _ L at plugged
  rw [Region.lsubst_bindBranchArguments_br] at plugged
  exact converted.trans plugged

theorem sound_proof {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
    [CartesianMonoidalCategory V] [SymmetricCategory V]
    [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
    [HasFiniteCoproducts V] [HasFiniteCoproducts C]
    [DistributiveTensor V] [DistributivePremonoidalCategory C]
    [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
    [FreydCategory.CentralUnit J] (M : TypeModel τ V) [InstructionModel J M Φ]
    [RegionTypingCoherent (Φ := Φ) J M]
    (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
      Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h)
    (h : Eqv pe Γ p q L) (hp : HasType Γ p L) (hq : HasType Γ q L) :
    denoteRegion J M hp = denoteRegion J M hq := by
  apply Extension.Eqv.sound J M shared _ h hp hq
  intro _ _ _ _ seed tp tq
  cases seed with
  | inl old =>
    have eq := SumBind.sound J M shared (.extra tp tq old) tp tq
    exact ⟨_, denoteRegion_spec J M tp, eq.symm ▸ denoteRegion_spec J M tq⟩
  | inr split =>
    cases split with
    | split he hl hr =>
      have native := denote_case_boundReturn_fusion J M (L := [_]) (i := 0) rfl he hl hr
      change denoteRegion J M tq = denoteRegion J M tp at native
      exact ⟨_, denoteRegion_spec J M tp, native ▸ denoteRegion_spec J M tq⟩
    | splitPair ha hb =>
      have native := denote_let₂_boundReturn_fusion J M (L := [_]) (i := 0) rfl ha hb
      change denoteRegion J M tq = denoteRegion J M tp at native
      exact ⟨_, denoteRegion_spec J M tp, native ▸ denoteRegion_spec J M tq⟩
    | @splitInl X Y _ ha =>
      have native := denote_inl_boundReturn_sequencing J M (L := [coprod X Y]) (i := 0) rfl ha
      change denoteRegion J M tp = denoteRegion J M tq at native
      exact ⟨_, denoteRegion_spec J M tp, native.symm ▸ denoteRegion_spec J M tq⟩
    | @splitInr X Y _ ha =>
      have native := denote_inr_boundReturn_sequencing J M (L := [coprod X Y]) (i := 0) rfl ha
      change denoteRegion J M tp = denoteRegion J M tq at native
      exact ⟨_, denoteRegion_spec J M tp, native.symm ▸ denoteRegion_spec J M tq⟩
    | @splitAbort D _ ha =>
      have native := denote_abort_boundReturn_sequencing J M (L := [D]) (i := 0) rfl ha
      change denoteRegion J M tp = denoteRegion J M tq at native
      exact ⟨_, denoteRegion_spec J M tp, native.symm ▸ denoteRegion_spec J M tq⟩

end Native

section Schedule

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {Γ Δ : VCtx τ} {S L : LCtx τ} {f : Φ} {p q : Region Φ}
  {before after : List (List Φ × Nat)}

theorem rename_schedule_proof {ρ : Nat → Nat}
    (h : Schedule Γ p L before) (typed : Ren Γ Δ ρ) :
    Schedule Δ (p.renameVars ρ) L before := by
  have move {a : Tm Φ} {A : τ} {Γ Δ : VCtx τ} {ρ : Nat → Nat}
      (value : Tm.BranchValue Γ a A) (ren : Ren Γ Δ ρ) :
      Tm.BranchValue Δ (a.rename ρ) A := by
    rw [Tm.rename_eq_subst]
    exact value.subst (fun _ _ hi => .var (ren hi))
  induction h generalizing Δ ρ with
  | ret exit value => exact .ret exit (move value typed)
  | call value _ ih => exact .call (move value typed) (ih (typed.lift _))
  | caseVar value _ _ ihl ihr => exact .caseVar (typed value) (ihl (typed.lift _)) (ihr (typed.lift _))
  | unpackVar value _ ih => exact .unpackVar (typed value) (ih ((typed.lift _).lift _))
  | abortValue value _ ih => exact .abortValue (move value typed) (ih (typed.lift _))

private theorem invoke_subst (f : Φ) (a : Tm Φ) (q : Region Φ) :
    (invoke f q).substVars (Tm.singleSubst a) = .let₁ (.op f a) q := by
  change Region.let₁ (.op f a) ((q.renameVars (lift Nat.succ)).substVars (Tm.liftSubst (Tm.singleSubst a))) = _
  rw [Region.substVars_renameVars]
  have drop : Tm.liftSubst (Tm.singleSubst a) ∘ lift Nat.succ = Tm.var := by
    funext i
    cases i <;> rfl
  rw [drop, Region.substVars_var]

private theorem invoke_lift (f : Φ) (q : Region Φ) :
    Region.liftLSubstVars (fun _ => invoke f q) = fun _ => invoke f (q.renameVars (lift Nat.succ)) := by
  funext i
  change Region.let₁ (.op f (.var 0)) ((q.renameVars (lift Nat.succ)).renameVars (lift (lift Nat.succ))) =
    Region.let₁ (.op f (.var 0)) ((q.renameVars (lift Nat.succ)).renameVars (lift Nat.succ))
  rw [Region.renameVars_comp, Region.renameVars_comp]
  congr 2
  funext j
  cases j <;> rfl

theorem splice_proof (producer : Schedule Γ p S before) (body : Schedule (instrTrg f :: Γ) q L after)
    (single : S = [instrSrc f]) :
    Schedule Γ (p.lsubst (fun _ => invoke f q)) L (callPaths f before after) := by
  induction producer generalizing q with
  | ret exit value =>
    cases single
    have eq := List.mem_singleton.mp (List.mem_of_getElem? exit)
    cases eq
    rw [Region.lsubst, invoke_subst]
    simpa only [callPaths, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append]
      using Schedule.call value body
  | @call Γ _ g _ _ _ value _ ih =>
    rw [Region.lsubst, invoke_lift]
    have moved := rename_schedule_proof body ((Ren.wk Γ (instrTrg g)).lift (instrTrg f))
    simpa only [callPaths, List.flatMap_map, List.map_flatMap, List.map_map, Function.comp_def, List.cons_append]
      using Schedule.call value (ih moved single)
  | @caseVar Γ _ _ A B _ _ _ _ value _ _ ihl ihr =>
    rw [Region.lsubst, invoke_lift]
    have left := rename_schedule_proof body ((Ren.wk Γ A).lift (instrTrg f))
    have right := rename_schedule_proof body ((Ren.wk Γ B).lift (instrTrg f))
    simpa only [callPaths, List.flatMap_append] using Schedule.caseVar value (ihl left single) (ihr right single)
  | @unpackVar Γ _ _ A B _ _ value _ ih =>
    rw [Region.lsubst, invoke_lift, invoke_lift]
    have left := rename_schedule_proof body ((Ren.wk Γ A).lift (instrTrg f))
    have moved := rename_schedule_proof left ((Ren.wk (A :: Γ) B).lift (instrTrg f))
    exact .unpackVar value (ih moved single)
  | @abortValue Γ _ A _ _ _ value _ ih =>
    rw [Region.lsubst, invoke_lift]
    exact .abortValue value (ih (rename_schedule_proof body ((Ren.wk Γ A).lift (instrTrg f))) single)

end Schedule

section Operands

variable {α : Type u} {Φ : Type v} [HasTy Φ (Ty α)] {ε : Type w} [HasEff Φ ε] {pe : ε}
  {L : LCtx (Ty α)} {A B : Ty α} {f : Φ} {q : Region Φ}
  {after : List (List Φ × Nat)} {n : Nat} {β : BoundCtx (Ty α) n}

theorem operand_schedule_proof (e : Operand Φ β (Ty.coprod A B))
    (l : Operand Φ (β.snoc A) (instrSrc f)) (r : Operand Φ (β.snoc B) (instrSrc f))
    (he : CallOperand (erase e.1) true) (hl : CallOperand (erase l.1) true)
    (hr : CallOperand (erase r.1) true) (body : Schedule (instrTrg f :: β.toList) q L after) :
    ∃ s before, CasePaths (operandCalls (erase e.1) true) (operandCalls (erase l.1) true)
        (operandCalls (erase r.1) true) 0 0 before ∧
      Schedule β.toList s L (callPaths f before after) ∧
      Eqv pe β.toList (.let₁ (.op f (.case (erase e.1) (erase l.1) (erase r.1))) q) s L := by
  obtain ⟨p, before, producer, paths, replay, _⟩ :=
    SumBind.operand_schedule (pe := pe) (rfl : At [instrSrc f] 0 (instrSrc f)) (rfl : At [instrSrc f] 0 (instrSrc f)) e l r he hl hr
  exact ⟨_, before, paths, splice_proof producer body rfl,
    call_replay_proof (erase_hasType e.2.toHasType) (erase_hasType l.2.toHasType) (erase_hasType r.2.toHasType)
      body.valueBranches.hasType producer.valueBranches (ofSums_proof replay)⟩

end Operands

end Silmaril.Isotope.LambdaSSA.Acyclic.Native.SumBind.Continuation

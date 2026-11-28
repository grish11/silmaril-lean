module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Calls.SumBind.Defs
import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Calls.ProductBind.Thms
import Silmaril.SSA.Isotope.Bridge.Acyclic.FiniteExit.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Normalization.Transport.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.BranchNormalization.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.Thms

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Native.SumBind

open Region (HasType ValueBranches)
open Region.Paper
open Region.Paper.WithComputedCallReturns
open Region.Paper.RetainedCase (boundCase boundCase_typed)
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
  {pe : ε} {Γ : VCtx τ} {L : LCtx τ} {A B : τ} {r s l l' k k' : Region Φ} {a b : Tm Φ}

theorem ofProducts_proof (h : ProductBind.Eqv pe Γ r s L) : Eqv pe Γ r s L :=
  WithProjectionReturnsAndUnitEta.WithBranchBinding.mapSeed Or.inl h

theorem bind_replay_proof (ha : Tm.HasType Γ a (coprod A B)) (hp : ValueBranches Γ r [coprod A B])
    (producer : Eqv pe Γ ((Region.br 0 a).bindBranchArguments) r [coprod A B])
    (left : Eqv pe (A :: Γ) l l' L) (right : Eqv pe (B :: Γ) k k' L)
    (hl : ValueBranches (A :: Γ) l' L) (hk : ValueBranches (B :: Γ) k' L) :
    Eqv pe Γ (.case a l k) (r.lsubst (fun _ => boundCase l' k')) L := by
  have bind := WithCaseBind.case_eq_let (Seed := Seed pe) Or.inr ha hl hk
  have plug := Extension.Eqv.lsubstPost (K := L) (σ := fun _ => boundCase l' k') producer
    (.let₁ ha (.br (ℓ := 0) rfl (.var rfl))) hp
    (fun _ _ hi => (List.mem_singleton.mp (List.mem_of_getElem? hi)).symm ▸ (boundCase_typed hl hk).hasType)
  rw [Region.lsubst_bindBranchArguments_br] at plug
  exact (Extension.Eqv.case ha left right).trans (bind.trans plug)

theorem constructor_left_proof (ha : Tm.BranchValue Γ a A)
    (hl : HasType (A :: Γ) l L) (hk : HasType (B :: Γ) k L) :
    Eqv pe Γ (.case (.inl a) l k) (l.substVars (Tm.singleSubst a)) L :=
  .paper (.cfgEta (.native ((Region.SubstitutionEquiv.base (.caseInl ha.hasType hl hk)).trans (.letValue ha hl))))

theorem constructor_right_proof (hb : Tm.BranchValue Γ b B)
    (hl : HasType (A :: Γ) l L) (hk : HasType (B :: Γ) k L) :
    Eqv pe Γ (.case (.inr b) l k) (k.substVars (Tm.singleSubst b)) L :=
  .paper (.cfgEta (.native ((Region.SubstitutionEquiv.base (.caseInr hb.hasType hl hk)).trans (.letValue hb hk))))

theorem Schedule.valueBranches_proof {paths : List (List Φ × Nat)}
    (h : Schedule Γ r L paths) : ValueBranches Γ r L := by
  induction h with
  | ret exit value => exact .br exit value
  | call value _ ih => exact .let₁ (.op value.hasType) ih
  | caseVar value _ _ ihl ihr => exact .case (.var value) ihl ihr
  | unpackVar value _ ih => exact .let₂ (.var value) ih
  | abortValue value _ ih => exact .let₁ (.abort value.hasType) ih

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
    (h : Eqv pe Γ r s L) (hr : HasType Γ r L) (hs : HasType Γ s L) :
    denoteRegion J M hr = denoteRegion J M hs := by
  apply Extension.Eqv.sound J M shared (WithCaseBind.joined_seedDenotes J M ?_) h hr hs
  intro _ _ _ _ seed tr ts
  have eq := ProductBind.sound J M shared (.extra tr ts seed) tr ts
  exact ⟨_, denoteRegion_spec J M tr, eq.symm ▸ denoteRegion_spec J M ts⟩

end Native

section Normalize

variable {α : Type u} {Φ : Type v} [HasTy Φ (Ty α)] {ε : Type w} [HasEff Φ ε] {pe : ε}
  {Γ : VCtx (Ty α)} {L : LCtx (Ty α)} {A B D E : Ty α}
  {p l r : Region Φ} {fs ls rs : List Φ}

private theorem boundCase_subst (a : Tm Φ) (left right : Region Φ) :
    (boundCase left right).substVars (Tm.singleSubst a) = .case a left right := by
  have arm (s : Region Φ) :
      (s.renameVars (lift Nat.succ)).substVars (Tm.liftSubst (Tm.singleSubst a)) = s := by
    rw [Region.substVars_renameVars]
    have drop : Tm.liftSubst (Tm.singleSubst a) ∘ lift Nat.succ = Tm.var := by
      funext i
      cases i <;> rfl
    rw [drop, Region.substVars_var]
  change Region.case a
    ((left.renameVars (lift Nat.succ)).substVars (Tm.liftSubst (Tm.singleSubst a)))
    ((right.renameVars (lift Nat.succ)).substVars (Tm.liftSubst (Tm.singleSubst a))) = _
  rw [arm, arm]

private theorem boundCase_lift (left right : Region Φ) :
    Region.liftLSubstVars (fun _ => boundCase left right) =
      fun _ => boundCase (left.renameVars (lift Nat.succ)) (right.renameVars (lift Nat.succ)) := by
  have arm (s : Region Φ) :
      (s.renameVars (lift Nat.succ)).renameVars (lift (lift Nat.succ)) =
        (s.renameVars (lift Nat.succ)).renameVars (lift Nat.succ) := by
    rw [Region.renameVars_comp, Region.renameVars_comp]
    congr 1
    funext i
    cases i <;> rfl
  funext i
  exact congrArg₂ (Region.case (.var 0)) (arm left) (arm right)

private theorem schedule_at {i : Nat} (exit : At L i D)
    (h : CallSchedule Γ p D fs) : Schedule Γ (p.renameLabels (fun _ => i)) L [(fs, i)] := by
  induction h with
  | ret value => exact .ret exit value
  | call value _ ih => exact .call value (ih exit)

omit [HasTy Φ (Ty α)] in
private theorem payload {a : Tm Φ} (ha : Tm.BranchValue Γ a A) :
    ∀ ⦃i T⦄, At (A :: Γ) i T → Tm.BranchValue Γ (Tm.singleSubst a i) T := by
  intro i T hi
  cases i with
  | zero => cases Option.some.inj hi; exact ha
  | succ => exact .var hi

private theorem CasePaths.prepend {paths : List (List Φ × Nat)} {f : Φ} {i j : Nat}
    (h : CasePaths fs ls rs i j paths) :
    CasePaths (f :: fs) ls rs i j (paths.map fun path => (f :: path.1, path.2)) := by
  rcases h with h | h | h <;> subst paths
  · exact .inl rfl
  · exact .inr (.inl rfl)
  · exact .inr (.inr rfl)

theorem splice_proof {i j : Nat} {S : Ty α} (exitL : At L i D) (exitR : At L j E)
    (producer : CallSchedule Γ p S fs) (left : CallSchedule (A :: Γ) l D ls)
    (right : CallSchedule (B :: Γ) r E rs) (shape : S = Ty.coprod A B) :
    ∃ s paths, Schedule Γ s L paths ∧ CasePaths fs ls rs i j paths ∧
      Eqv pe Γ (p.lsubst (fun _ => boundCase (l.renameLabels (fun _ => i)) (r.renameLabels (fun _ => j)))) s L := by
  induction producer generalizing l r with
  | ret value =>
    cases shape
    rw [Region.lsubst, boundCase_subst]
    have hl := (schedule_at exitL left).valueBranches_proof.hasType
    have hr := (schedule_at exitR right).valueBranches_proof.hasType
    cases value with
    | var hi =>
      exact ⟨_, _, .caseVar hi (schedule_at exitL left) (schedule_at exitR right),
        .inr (.inr rfl), .refl (.case (.var hi) hl hr)⟩
    | inl value =>
      have reduced := schedule_at exitL (left.subst (payload value))
      exact ⟨_, _, by simpa only [Region.substVars_renameLabels, List.nil_append] using reduced,
        .inl rfl, constructor_left_proof value hl hr⟩
    | inr value =>
      have reduced := schedule_at exitR (right.subst (payload value))
      exact ⟨_, _, by simpa only [Region.substVars_renameLabels, List.nil_append] using reduced,
        .inr (.inl rfl), constructor_right_proof value hl hr⟩
  | @call Γ f a p _ fs value cont ih =>
    rw [Region.lsubst, boundCase_lift, Region.renameVars_renameLabels, Region.renameVars_renameLabels]
    obtain ⟨s, paths, hs, routes, eq⟩ := ih
      (left.rename ((Ren.wk Γ (instrTrg f)).lift A)) (right.rename ((Ren.wk Γ (instrTrg f)).lift B)) shape
    exact ⟨_, _, .call value hs, routes.prepend, .let₁ (.op value.hasType) eq⟩

private theorem rename_guarded {n : Nat} {β : BoundCtx (Ty α) n} {T : Ty α} (c : Code Φ β T) (i : Nat) :
    (c.guardedSSA 0).renameLabels (fun _ => i) = c.guardedSSA i := by
  rw [Code.guardedSSA, ← Region.bindBranchArguments_renameLabels, Code.toSSA_renameLabels]
  rfl

theorem operand_schedule_proof {n : Nat} {β : BoundCtx (Ty α) n} {i j : Nat}
    (exitL : At L i D) (exitR : At L j E)
    (producer : Operand Φ β (Ty.coprod A B)) (left : Operand Φ (β.snoc A) D)
    (right : Operand Φ (β.snoc B) E)
    (hp : CallOperand (erase producer.1) true) (hl : CallOperand (erase left.1) true)
    (hr : CallOperand (erase right.1) true) :
    ∃ s paths, Schedule β.toList s L paths ∧
      CasePaths (operandCalls (erase producer.1) true) (operandCalls (erase left.1) true)
        (operandCalls (erase right.1) true) i j paths ∧
      Eqv pe β.toList
        (FiniteExit.case producer (.br exitL left) (.br exitR right)).toSSA.bindBranchArguments s L ∧
      Eqv pe β.toList
        (.case (erase producer.1) ((Code.ofLetCase left.2).guardedSSA i)
          ((Code.ofLetCase right.2).guardedSSA j)) s L := by
  obtain ⟨p, ps, ep, _⟩ := operand_pair_schedule pe producer hp
  obtain ⟨l, lq, el, reifiedL⟩ := operand_pair_schedule pe left hl
  obtain ⟨r, rq, er, reifiedR⟩ := operand_pair_schedule pe right hr
  have labelsL : Ren [D] L (fun _ => i) :=
    fun _ _ hi => (List.mem_singleton.mp (List.mem_of_getElem? hi)).symm ▸ exitL
  have labelsR : Ren [E] L (fun _ => j) :=
    fun _ _ hi => (List.mem_singleton.mp (List.mem_of_getElem? hi)).symm ▸ exitR
  have liftRewrite {Δ : VCtx (Ty α)} {K : LCtx (Ty α)} {a b : Region Φ}
      (h : OrderedPairs.Eqv pe Δ a b K) : Eqv pe Δ a b K :=
    ofProducts_proof (ProductBind.ofPairs h)
  have a := erase_hasType producer.2.toHasType
  have eqL := (liftRewrite el).renameLabels labelsL
  have eqR := (liftRewrite er).renameLabels labelsR
  have rl := (liftRewrite reifiedL).renameLabels labelsL
  have rr := (liftRewrite reifiedR).renameLabels labelsR
  rw [rename_guarded] at eqL eqR rl rr
  have leftTyped := (schedule_at exitL lq).valueBranches_proof
  have rightTyped := (schedule_at exitR rq).valueBranches_proof
  obtain ⟨s, paths, sp, route, finish⟩ := splice_proof (pe := pe) exitL exitR ps lq rq rfl
  have first := bind_replay_proof a ps.valueBranches (liftRewrite ep) eqL eqR leftTyped rightTyped
  have second := bind_replay_proof a ps.valueBranches (liftRewrite ep) rl rr leftTyped rightTyped
  exact ⟨s, paths, sp, route, first.trans finish, second.trans finish⟩

end Normalize

end Silmaril.Isotope.LambdaSSA.Acyclic.Native.SumBind

module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Calls.ProductBind.Defs
import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Calls.Thms
import Silmaril.SSA.Isotope.Bridge.Acyclic.FiniteExit.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Normalization.Transport.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.BranchNormalization.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.BinaryLetBind.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedCallReturns.OrderedPairs.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.Thms

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Native.ProductBind

open Region (HasType ValueBranches)
open Region.Paper
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
  {pe : ε} {Γ : VCtx τ} {L : LCtx τ} {A B : τ} {r k k' : Region Φ} {a : Tm Φ}

theorem ofPairs_proof (h : OrderedPairs.Eqv pe Γ r k L) : Eqv pe Γ r k L :=
  WithProjectionReturnsAndUnitEta.WithBranchBinding.mapSeed Or.inl h

private theorem unpack_typed (hk : HasType (B :: A :: Γ) k L) :
    HasType (product A B :: Γ) (unpack k) L :=
  .let₂ (.var (i := 0) rfl) (hk.renameVars (((Ren.wk Γ (product A B)).lift A).lift B))

theorem bind_replay_proof {seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop}
    (includeBind : ∀ {Δ K p q}, Region.BinaryLetBind.Step Δ p q K → seed Δ p q K)
    (ha : Tm.HasType Γ a (product A B)) (hr : ValueBranches Γ r [product A B])
    (producer : Extension.Eqv seed Γ ((Region.br 0 a).bindBranchArguments) r [product A B])
    (body : Extension.Eqv seed (B :: A :: Γ) k k' L) :
    Extension.Eqv seed Γ (.let₂ a k) (r.lsubst (fun _ => unpack k')) L := by
  let step := Region.BinaryLetBind.Step.bind ha body.typed.2
  have bind : Extension.Eqv seed Γ (.let₂ a k') (Region.BinaryLetBind.rebound a k') L :=
    .extra step.typed.1 step.typed.2 (includeBind step)
  have plug := Extension.Eqv.lsubstPost (K := L) (σ := fun _ => unpack k') producer
    (.let₁ ha (.br (ℓ := 0) rfl (.var rfl))) hr
    (fun _ _ hi => (List.mem_singleton.mp (List.mem_of_getElem? hi)).symm ▸ unpack_typed body.typed.2)
  rw [Region.lsubst_bindBranchArguments_br] at plug
  exact (Extension.Eqv.let₂ ha body).trans (bind.trans plug)

theorem Schedule.valueBranches_proof {fs : List Φ} (h : Schedule Γ r L fs) : ValueBranches Γ r L := by
  induction h with
  | ret exit value => exact .br exit value
  | call value _ ih => exact .let₁ (.op value.hasType) ih
  | unpackVar value _ ih => exact .let₂ (.var value) ih

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
    (h : Eqv pe Γ r k L) (hr : HasType Γ r L) (hk : HasType Γ k L) :
    denoteRegion J M hr = denoteRegion J M hk := by
  apply Extension.Eqv.sound J M shared _ h hr hk
  intro _ _ _ _ seed tr ts
  have eq := seed.elim
    (fun h => OrderedPairs.sound J M shared (.extra tr ts h) tr ts)
    (fun h => h.sound J M tr ts)
  exact ⟨_, denoteRegion_spec J M tr, eq.symm ▸ denoteRegion_spec J M ts⟩

end Native

section Normalize

variable {α : Type u} {Φ : Type v} [HasTy Φ (Ty α)] {ε : Type w} [HasEff Φ ε] {pe : ε}
  {Γ : VCtx (Ty α)} {L : LCtx (Ty α)} {A B D : Ty α}
  {r k : Region Φ} {fs gs : List Φ}

private theorem unpack_subst (a : Tm Φ) (body : Region Φ) :
    (unpack body).substVars (Tm.singleSubst a) = .let₂ a body := by
  change Region.let₂ a ((body.renameVars (lift (lift Nat.succ))).substVars
      (Tm.liftSubstN 2 (Tm.singleSubst a))) = _
  rw [Region.substVars_renameVars]
  have drop : Tm.liftSubstN 2 (Tm.singleSubst a) ∘ lift (lift Nat.succ) = Tm.var := by
    funext i
    match i with
    | 0 | 1 | _ + 2 => rfl
  rw [drop, Region.substVars_var]

private theorem unpack_lift (body : Region Φ) :
    Region.liftLSubstVars (fun _ => unpack body) =
      fun _ => unpack (body.renameVars (lift (lift Nat.succ))) := by
  funext l
  change Region.let₂ (.var 0)
      ((body.renameVars (lift (lift Nat.succ))).renameVars (lift (lift (lift Nat.succ)))) =
    Region.let₂ (.var 0)
      ((body.renameVars (lift (lift Nat.succ))).renameVars (lift (lift Nat.succ)))
  rw [Region.renameVars_comp, Region.renameVars_comp]
  congr 2
  funext i
  match i with
  | 0 | 1 | _ + 2 => rfl

private theorem schedule_at {i : Nat} (exit : At L i D)
    (p : CallSchedule Γ r D fs) : Schedule Γ (r.renameLabels (fun _ => i)) L fs := by
  induction p with
  | ret value => exact .ret exit value
  | call value _ ih => exact .call value (ih exit)

omit [HasTy Φ (Ty α)] in
private theorem fields {a b : Tm Φ}
    (ha : Tm.BranchValue Γ a A) (hb : Tm.BranchValue Γ b B) :
    ∀ ⦃i T⦄, At (B :: A :: Γ) i T → Tm.BranchValue Γ
      (Tm.consSubst b (Tm.singleSubst a) i) T := by
  intro i T atSlot
  match i with
  | 0 => cases Option.some.inj atSlot; exact hb
  | 1 => cases Option.some.inj atSlot; exact ha
  | j + 2 => exact .var atSlot

theorem splice_proof {i : Nat} {P : Ty α} (exit : At L i D) (p : CallSchedule Γ r P fs)
    (q : CallSchedule (B :: A :: Γ) k D gs) (shape : P = Ty.product A B) :
    ∃ s, Schedule Γ s L (fs ++ gs) ∧
      Eqv pe Γ (r.lsubst (fun _ => unpack (k.renameLabels (fun _ => i)))) s L := by
  induction p generalizing k with
  | ret value =>
    cases shape
    rw [Region.lsubst, unpack_subst]
    cases value with
    | var hi =>
      exact ⟨_, .unpackVar hi (schedule_at exit q), .refl (.let₂ (.var hi) (schedule_at exit q |>.valueBranches_proof.hasType))⟩
    | pair left right =>
      have reduced := schedule_at exit (q.subst (fields left right))
      have beta := Region.ProductBeta.Step.let₂Beta left right (schedule_at exit q |>.valueBranches_proof.hasType)
      exact ⟨_, by simpa only [Region.substVars_renameLabels, List.nil_append] using reduced, .paper (.productBeta beta)⟩
  | @call Γ f a r _ fs value cont ih =>
    rw [Region.lsubst, unpack_lift, Region.renameVars_renameLabels]
    obtain ⟨s, hs, eq⟩ := ih (q.rename (((Ren.wk Γ (instrTrg f)).lift A).lift B)) shape
    exact ⟨_, .call value hs, .let₁ (.op value.hasType) eq⟩

theorem operand_schedule_proof
    {n : Nat} {β : BoundCtx (Ty α) n} {i : Nat}
    (exit : At L i D) (producer : Operand Φ β (Ty.product A B))
    (body : Operand Φ ((β.snoc A).snoc B) D)
    (hp : CallOperand (erase producer.1) true) (hk : CallOperand (erase body.1) true) :
    ∃ s, Schedule β.toList s L
        (operandCalls (erase producer.1) true ++ operandCalls (erase body.1) true) ∧
      Eqv pe β.toList ((Code.let₂ producer (.br body)).guardedSSA i) s L ∧
      Eqv pe β.toList ((Code.ofLetCase (.let₂ producer.2 body.2)).guardedSSA i) s L := by
  obtain ⟨r, rp, eqp, _⟩ := operand_pair_schedule pe producer hp
  obtain ⟨k, kq, eqk, reified⟩ := operand_pair_schedule pe body hk
  have labels : Ren [D] L (fun _ => i) :=
    fun _ _ hi => (List.mem_singleton.mp (List.mem_of_getElem? hi)).symm ▸ exit
  have tail := (ofPairs_proof eqk).renameLabels labels
  have tailReified := (ofPairs_proof reified).renameLabels labels
  have move (c : Code Φ ((β.snoc A).snoc B) D) :
      (c.guardedSSA 0).renameLabels (fun _ => i) = c.guardedSSA i := by
    rw [Code.guardedSSA, ← Region.bindBranchArguments_renameLabels, Code.toSSA_renameLabels]
    rfl
  rw [move] at tail
  rw [move] at tailReified
  obtain ⟨s, scheduled, finish⟩ := splice_proof (pe := pe) exit rp kq rfl
  have a := erase_hasType producer.2.toHasType
  have first := bind_replay_proof (seed := Seed pe) Or.inr a rp.valueBranches (ofPairs_proof eqp) tail
  have second := bind_replay_proof (seed := Seed pe) Or.inr a rp.valueBranches (ofPairs_proof eqp) tailReified
  exact ⟨s, scheduled, first.trans finish, second.trans finish⟩

end Normalize

end Silmaril.Isotope.LambdaSSA.Acyclic.Native.ProductBind

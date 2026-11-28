module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Calls.SumBind.Recursive.Defs
import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Calls.SumBind.Continuation.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Family.Thms

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Native.SumBind.Recursive

open Region (HasType ValueBranches)
open Region.Paper.Extension
open Silmaril.DeBruijn (lift)

set_option backward.isDefEq.respectTransparency false

universe u v w

variable {α : Type u} {Φ : Type v} [HasTy Φ (Ty α)] {ε : Type w} [HasEff Φ ε] {pe : ε}
  {Γ Δ : VCtx (Ty α)} {L K : LCtx (Ty α)} {D : Ty α} {p q : Region Φ}
  {paths before after : List (List Φ × Nat)} {θ : Nat → Tm Φ}

omit [HasTy Φ (Ty α)] in
private theorem value_cons {A : Ty α} {a : Tm Φ} (value : Tm.BranchValue Δ a A)
    (h : ∀ ⦃i T⦄, At Γ i T → Tm.BranchValue Δ (θ i) T) :
    ∀ ⦃i T⦄, At (A :: Γ) i T → Tm.BranchValue Δ (Tm.consSubst a θ i) T := by
  intro i T hi
  cases i with
  | zero => cases Option.some.inj hi; exact value
  | succ => exact h hi

omit [HasTy Φ (Ty α)] in
private theorem value_lift (A : Ty α)
    (h : ∀ ⦃i T⦄, At Γ i T → Tm.BranchValue Δ (θ i) T) :
    ∀ ⦃i T⦄, At (A :: Γ) i T → Tm.BranchValue (A :: Δ) (Tm.liftSubst θ i) T := by
  intro i T hi
  cases i with
  | zero => cases Option.some.inj hi; exact .var rfl
  | succ i =>
    change Tm.BranchValue (A :: Δ) ((θ i).rename Nat.succ) T
    rw [Tm.rename_eq_subst]
    exact (h hi).subst (fun _ _ hj => .var (Ren.wk Δ A hj))

private theorem specialize_arm (p : Region Φ) (θ : Nat → Tm Φ) (a : Tm Φ) :
    (p.substVars (Tm.liftSubst θ)).substVars (Tm.singleSubst a) =
      p.substVars (Tm.consSubst a θ) := by
  rw [Region.substVars_comp]
  congr 1
  funext i
  cases i with
  | zero => rfl
  | succ i =>
    change ((θ i).rename Nat.succ).subst (Tm.singleSubst a) = θ i
    rw [Tm.subst_rename]
    exact Tm.subst_var _

private theorem specialize_fields (p : Region Φ) (θ : Nat → Tm Φ) (a b : Tm Φ) :
    (p.substVars (Tm.liftSubst (Tm.liftSubst θ))).substVars (Tm.consSubst b (Tm.singleSubst a)) =
      p.substVars (Tm.consSubst b (Tm.consSubst a θ)) := by
  rw [Region.substVars_comp]
  congr 1
  funext i
  match i with
  | 0 | 1 => rfl
  | j + 2 =>
    change (((θ j).rename Nat.succ).rename Nat.succ).subst (Tm.consSubst b (Tm.singleSubst a)) = θ j
    rw [Tm.subst_rename, Tm.subst_rename]
    exact Tm.subst_var _

private theorem specialize_schedule (h : Schedule Γ p L paths)
    (typed : ∀ ⦃i T⦄, At Γ i T → Tm.BranchValue Δ (θ i) T) :
    ∃ s routes, Schedule Δ s L routes ∧ List.Sublist routes paths ∧
      Continuation.Eqv pe Δ (p.substVars θ) s L := by
  induction h generalizing Δ θ with
  | ret exit value =>
    have out := value.subst (fun _ _ hi => typed hi)
    exact ⟨_, _, .ret exit out, .refl _, .refl (.br exit out.hasType)⟩
  | @call _ _ f _ _ _ value _ ih =>
    obtain ⟨s, routes, out, sub, replay⟩ := ih (value_lift (instrTrg f) typed)
    have arg := value.subst (fun _ _ hi => typed hi)
    exact ⟨_, _, .call arg out, sub.map _, .let₁ (.op arg.hasType) replay⟩
  | @caseVar Γ L slot A B l r left right hi hl hr ihl ihr =>
    have leftLift := value_lift A typed
    have rightLift := value_lift B typed
    have leftTyped := hl.valueBranches.hasType.substVars (fun _ _ h => (leftLift h).hasType)
    have rightTyped := hr.valueBranches.hasType.substVars (fun _ _ h => (rightLift h).hasType)
    have test := typed hi
    change ∃ s routes, Schedule Δ s L routes ∧ List.Sublist routes (left ++ right) ∧
      Continuation.Eqv pe Δ (.case (θ slot) (l.substVars (Tm.liftSubst θ)) (r.substVars (Tm.liftSubst θ))) s L
    generalize htest : θ slot = testTerm at test ⊢
    cases test with
    | var guard =>
      obtain ⟨l', ls, lp, lsub, lr⟩ := ihl leftLift
      obtain ⟨r', rs, rp, rsub, rr⟩ := ihr rightLift
      exact ⟨_, _, .caseVar guard lp rp, lsub.append rsub, .case (.var guard) lr rr⟩
    | inl value =>
      obtain ⟨s, routes, out, sub, replay⟩ := ihl (value_cons value typed)
      have beta := Continuation.ofSums (constructor_left (pe := pe) value leftTyped rightTyped)
      rw [specialize_arm] at beta
      exact ⟨s, routes, out, sub.trans (List.sublist_append_left ..), beta.trans replay⟩
    | inr value =>
      obtain ⟨s, routes, out, sub, replay⟩ := ihr (value_cons value typed)
      have beta := Continuation.ofSums (constructor_right (pe := pe) value leftTyped rightTyped)
      rw [specialize_arm] at beta
      exact ⟨s, routes, out, sub.trans (List.sublist_append_right ..), beta.trans replay⟩
  | @unpackVar Γ L slot A B r paths hi hr ih =>
    have lifted := value_lift B (value_lift A typed)
    have packet := typed hi
    change ∃ s routes, Schedule Δ s L routes ∧ List.Sublist routes paths ∧
      Continuation.Eqv pe Δ (.let₂ (θ slot) (r.substVars (Tm.liftSubst (Tm.liftSubst θ)))) s L
    generalize hpacket : θ slot = packetTerm at packet ⊢
    cases packet with
    | var value =>
      obtain ⟨s, routes, out, sub, replay⟩ := ih lifted
      exact ⟨_, routes, .unpackVar value out, sub, .let₂ (.var value) replay⟩
    | pair left right =>
      obtain ⟨s, routes, out, sub, replay⟩ := ih (value_cons right (value_cons left typed))
      have bodyTyped := hr.valueBranches.hasType.substVars (fun _ _ h => (lifted h).hasType)
      have beta := Continuation.ofSums (SumBind.ofProducts (ProductBind.constructor_beta (pe := pe) left right bodyTyped))
      rw [specialize_fields] at beta
      exact ⟨s, routes, out, sub, beta.trans replay⟩
  | @abortValue _ _ A _ _ _ value _ ih =>
    obtain ⟨s, _, out, _, replay⟩ := ih (value_lift A typed)
    have emptyValue := value.subst (fun _ _ hi => typed hi)
    exact ⟨_, [], .abortValue emptyValue out, .refl [], .let₁ (.abort emptyValue.hasType) replay⟩

-- Even an unreachable syntactic branch has a typed label to host the
-- guarded eliminator. No such label is added to the returning paths.
private theorem schedule_exit (h : Schedule Γ p L paths) : ∃ i A, At L i A := by
  induction h with
  | ret exit _ => exact ⟨_, _, exit⟩
  | call _ _ ih | unpackVar _ _ ih | abortValue _ _ ih => exact ih
  | caseVar _ _ _ ih _ => exact ih

theorem splice_schedule_proof (producer : Schedule Γ p K before) (body : Schedule (D :: Γ) q L after)
    (single : K = [D]) :
    ∃ s routes, Schedule Γ s L routes ∧ List.Sublist routes (appendPaths before after) ∧
      Continuation.Eqv pe Γ (p.lsubst (fun _ => q)) s L := by
  induction producer generalizing q with
  | ret exit value =>
    cases single
    have eq := List.mem_singleton.mp (List.mem_of_getElem? exit)
    cases eq
    have values := value_cons value (θ := Tm.var) (fun _ _ hi => .var hi)
    simpa only [Region.lsubst, appendPaths, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.nil_append, Prod.mk.eta, List.map_id', Tm.singleSubst] using specialize_schedule (pe := pe) body values
  | @call Γ _ f _ _ _ arg _ ih =>
    obtain ⟨s, routes, out, sub, replay⟩ :=
      ih (Continuation.rename_schedule body ((Ren.wk Γ (instrTrg f)).lift D)) single
    refine ⟨_, _, .call arg out, ?_, .let₁ (.op arg.hasType) replay⟩
    simpa only [appendPaths, List.flatMap_map, List.map_flatMap, List.map_map, Function.comp_def, List.cons_append]
      using sub.map (fun p => (f :: p.1, p.2))
  | @caseVar Γ _ _ A B _ _ _ _ value _ _ ihl ihr =>
    obtain ⟨l', ls, lp, lsub, lr⟩ := ihl (Continuation.rename_schedule body ((Ren.wk Γ A).lift D)) single
    obtain ⟨r', rs, rp, rsub, rr⟩ := ihr (Continuation.rename_schedule body ((Ren.wk Γ B).lift D)) single
    exact ⟨_, _, .caseVar value lp rp, by simpa only [appendPaths, List.flatMap_append] using lsub.append rsub,
      .case (.var value) lr rr⟩
  | @unpackVar Γ _ _ A B _ _ value _ ih =>
    have left := Continuation.rename_schedule body ((Ren.wk Γ A).lift D)
    obtain ⟨s, routes, out, sub, replay⟩ :=
      ih (Continuation.rename_schedule left ((Ren.wk (A :: Γ) B).lift D)) single
    exact ⟨_, _, .unpackVar value out, sub, .let₂ (.var value) replay⟩
  | @abortValue Γ _ _ _ _ _ value dead _ =>
    cases single
    obtain ⟨i, T, exit⟩ := schedule_exit body
    have stop : Schedule Γ (.let₁ (.abort _) (.br i (.var 0))) L [] :=
      .abortValue value (.ret exit (.var (i := 0) rfl))
    have pasted := (Schedule.abortValue value dead).valueBranches.lsubst (σ := fun _ => q)
      (fun _ _ hi => (List.mem_singleton.mp (List.mem_of_getElem? hi)).symm ▸ body.valueBranches)
    exact ⟨_, [], stop, .refl [], .paper (.cfgEta (.native (.initial value pasted.hasType stop.valueBranches.hasType)))⟩

theorem retarget_schedule_proof {i : Nat} (out : At L i D) (h : Schedule Γ p K paths)
    (single : K = [D]) :
    Schedule Γ (p.renameLabels (fun _ => i)) L (paths.map fun p => (p.1, i)) := by
  induction h with
  | ret exit value =>
    cases single
    have eq := List.mem_singleton.mp (List.mem_of_getElem? exit)
    cases eq
    exact .ret out value
  | @call _ _ f _ _ _ value _ ih =>
    simpa only [Region.renameLabels, List.map_map, Function.comp_def] using Schedule.call value (ih single)
  | caseVar value _ _ ihl ihr =>
    simpa only [Region.renameLabels, List.map_append] using Schedule.caseVar value (ihl single) (ihr single)
  | unpackVar value _ ih => exact .unpackVar value (ih single)
  | abortValue value _ ih => exact .abortValue value (ih single)

end Silmaril.Isotope.LambdaSSA.Acyclic.Native.SumBind.Recursive

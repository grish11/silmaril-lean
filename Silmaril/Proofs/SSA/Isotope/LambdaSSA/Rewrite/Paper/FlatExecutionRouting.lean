module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.FlatDispatcher.Execution.Defs

/-! # Finite evaluation of the entry and block routers -/

public section

universe u v w x

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.FlatExecution

open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.FiniteCFG
open Silmaril.Isotope.LambdaSSA.Region
open Silmaril.DeBruijn (lift)
open SyntacticCategory (iterationBody iterationDispatch)
open Semantics (extend Env)

variable {α : Type u} {Φ : Type v} {σ : Type w}
  {instr : Φ → Value α → σ → Value α → σ → Prop}

local notation "Eval" => Semantics.Region.Eval

private theorem eval_lifted {k : Nat → Region Φ} {i label : Nat} {env : Env α}
    {ignored payload out : Value α} {s t : σ} :
    Eval instr (extend (extend env ignored) payload) (liftLSubstVars k i) s label out t ↔
      Eval instr (extend env payload) (k i) s label out t :=
  Semantics.Region.Eval.renameVars_iff (Semantics.extend_rename (fun _ => rfl) payload)

@[expose] def feedbackLabel (blocks i : Nat) : Nat :=
  if i < blocks then 0 else 1

@[expose] def feedbackPayload (blocks i : Nat) (v : Value α) : Value α :=
  packedExitValue (if i < blocks then i else i - blocks) v

theorem route_comp_dispatch (count i : Nat) :
    compLSubst (routeExit (Φ := Φ) count) (fun _ => iterationDispatch) i =
      .case (if i < count then .inr (packedExitArg i (.var 0))
             else .inl (packedExitArg (i - count) (.var 0)))
        (.br 1 (.var 0)) (.br 0 (.var 0)) := by
  unfold compLSubst routeExit
  split <;> rfl

private theorem eval_route_comp_dispatch {env : Env α} {payload out : Value α}
    {count i label : Nat} {s t : σ} :
    Eval instr (extend env payload)
        (compLSubst (routeExit count) (fun _ => iterationDispatch) i) s label out t ↔
      label = feedbackLabel count i ∧ out = feedbackPayload count i payload ∧ t = s := by
  let tag : Tm Φ := if i < count then .inr (packedExitArg i (.var 0))
    else .inl (packedExitArg (i - count) (.var 0))
  have ht {v : Value α} {m : σ} :
      Semantics.Tm.Eval instr (extend env payload) tag s v m ↔
        v = routeValue count i payload ∧ m = s := by
    have h : routeExit (Φ := Φ) count i = .br 0 tag := by unfold routeExit tag; split <;> rfl
    constructor
    · intro ht
      have hv : Eval instr (extend env payload) (routeExit count i) s 0 v m :=
        h.symm ▸ Semantics.Region.Eval.br ht
      exact (routeExit_eval_iff.mp hv).2
    · intro ht
      have hv := (routeExit_eval_iff (env := env) (instr := instr) (count := count) (i := i)).mpr
        ⟨rfl, ht⟩
      rw [h] at hv
      cases hv with
      | br hv => exact hv
  rw [route_comp_dispatch]
  change Eval instr (extend env payload) (.case tag (.br 1 (.var 0)) (.br 0 (.var 0))) s label out t ↔ _
  by_cases h : i < count
  · simp only [feedbackLabel, feedbackPayload, ite_eq_left h]
    constructor
    · intro hv
      cases hv with
      | case_inl htag _ =>
        have hbad := (ht.mp htag).1
        simp [routeValue, h] at hbad
      | case_inr htag hbr =>
        have ⟨hv, hs⟩ := ht.mp htag
        simp [routeValue, h] at hv
        cases hv
        cases hs
        cases hbr with
        | br harg => cases harg; exact ⟨rfl, rfl, rfl⟩
    · rintro ⟨rfl, rfl, rfl⟩
      exact .case_inr (ht.mpr ⟨by simp [routeValue, h], rfl⟩) (.br .var)
  · simp only [feedbackLabel, feedbackPayload, ite_eq_right h]
    constructor
    · intro hv
      cases hv with
      | case_inr htag _ =>
        have hbad := (ht.mp htag).1
        simp [routeValue, h] at hbad
      | case_inl htag hbr =>
        have ⟨hv, hs⟩ := ht.mp htag
        simp [routeValue, h] at hv
        cases hv
        cases hs
        cases hbr with
        | br harg => cases harg; exact ⟨rfl, rfl, rfl⟩
    · rintro ⟨rfl, rfl, rfl⟩
      exact .case_inl (ht.mpr ⟨by simp [routeValue, h], rfl⟩) (.br .var)

theorem routedFlat_body_eval {labels n : Nat} (count : Nat) (r : Flat Φ labels n)
    {env : Env α} {s t : σ} {label : Nat} {out : Value α} :
    Eval instr env (iterationBody (routedFlat count r)) s label out t ↔
      ∃ i v, Eval instr env r.erase s i v t ∧
        label = feedbackLabel count i ∧ out = feedbackPayload count i v := by
  rw [iterationBody, routedFlat, lsubst_comp, flat_bindBranchArguments_lsubst_eval_iff]
  constructor
  · rintro ⟨i, v, m, h, hk⟩
    obtain ⟨hl, hv, rfl⟩ := eval_route_comp_dispatch.mp hk
    exact ⟨i, v, h, hl, hv⟩
  · rintro ⟨i, v, h, hl, hv⟩
    exact ⟨i, v, t, h, eval_route_comp_dispatch.mpr ⟨hl, hv, rfl⟩⟩

/- The selected continuation receives the decoded payload above the environment
in which the decoder ran. The additional case binders are absent from it. -/
private theorem unpackExits_apply_eval {τ : Type x} [TypeFormers τ] (L : LCtx τ)
    {i : Nat} (hi : i < L.length) (k : Nat → Region Φ)
    {env : Env α} {v out : Value α} {s t : σ} {label : Nat} :
    Eval instr (extend env (packedExitValue i v)) ((unpackExits L).lsubst k) s label out t ↔
      Eval instr (extend (extend env (packedExitValue i v)) v) (k i) s label out t := by
  induction L generalizing i k env with
  | nil => simp at hi
  | cons A L ih =>
    cases i with
    | zero =>
      simp only [unpackExits, packedExitValue, Region.lsubst] at *
      change Eval instr (extend env (.inl v))
        (.case (.var 0) (compLSubst labelId k 0) _) s label out t ↔ _
      rw [compLSubst_id_left]
      constructor
      · intro h
        cases h with
        | case_inl ht hb => cases ht; exact hb
        | case_inr ht _ => cases ht
      · intro h
        exact .case_inl .var h
    | succ i =>
      have htail : i < L.length := Nat.lt_of_succ_lt_succ hi
      rw [unpackExits, packedExitValue, Region.lsubst, lsubst_renameLabels]
      constructor
      · intro h
        cases h with
        | case_inl ht _ => cases ht
        | case_inr ht hb =>
          cases ht
          exact eval_lifted.mp ((ih htail (liftLSubstVars k ∘ Nat.succ)).mp hb)
      · intro h
        exact .case_inr .var ((ih htail (liftLSubstVars k ∘ Nat.succ)).mpr (eval_lifted.mpr h))

theorem unpackExits_comp_eval {τ : Type x} [TypeFormers τ] (L : LCtx τ)
    {i : Nat} (hi : i < L.length) (k : Nat → Region Φ)
    {env : Env α} {v out : Value α} {s t : σ} {label : Nat} :
    Eval instr (extend env (packedExitValue i v))
        (compLSubst (fun _ => unpackExits L) k 0) s label out t ↔
      Eval instr (extend env v) (k i) s label out t :=
  (unpackExits_apply_eval L hi (liftLSubstVars k)).trans eval_lifted

section Dispatcher

variable {τ : Type x} [TypeFormers τ] [HasTy Φ τ]
  {blocks exits : Nat} {R : Fin blocks → τ} {E : Fin exits → τ}
  {n : Nat} {β : BoundCtx τ n} {g : FiniteCFG Φ blocks exits n}

/-- The continuations applied after decoding the packed block index. -/
def packedBlockContinuations (hg : FiniteCFG.HasType β R E g) : Nat → Region Φ :=
  compLSubst (compLSubst (blockFamily hg).val (routeFamily (List.ofFn R) (List.ofFn E) β.toList).val)
    (fun _ => iterationDispatch)

theorem iterationBody_packedDispatcher (hg : FiniteCFG.HasType β R E g) :
    iterationBody (packedDispatcherRegion hg) =
      compLSubst (fun _ => unpackExits (List.ofFn R)) (packedBlockContinuations hg) 0 := by
  let body := compLSubst (blockFamily hg).val (routeFamily (List.ofFn R) (List.ofFn E) β.toList).val
  let ret : Nat → Region Φ := fun _ => iterationDispatch
  have shift : liftLSubstVars ret = ret := rfl
  have assoc : compLSubst (liftLSubstVars body) ret = liftLSubstVars (compLSubst body ret) :=
    (congrArg (compLSubst (liftLSubstVars body)) shift).symm.trans (compLSubst_liftVars body ret)
  change ((unpackExits (List.ofFn R)).lsubst (liftLSubstVars body)).lsubst ret = _
  rw [lsubst_comp, assoc]
  rfl

theorem packedBlockContinuations_at (hg : FiniteCFG.HasType β R E g) {i : Nat} (hi : i < blocks) :
    packedBlockContinuations hg i = iterationBody (routedFlat blocks (g.block ⟨i, hi⟩)) := by
  have shift : liftLSubstVars (fun _ => iterationDispatch : Nat → Region Φ) =
      fun _ => iterationDispatch := rfl
  simp only [packedBlockContinuations, iterationBody, compLSubst, routeFamily, List.length_ofFn,
    blockFamily, ContinuationFamily.ofTyped, dite_eq_left hi, liftLSubstVars_routeExit, shift, routedFlat]

end Dispatcher

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.FlatExecution

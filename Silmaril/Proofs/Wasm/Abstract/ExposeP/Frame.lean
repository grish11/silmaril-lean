module

public import Silmaril.Proofs.Wasm.Abstract.ExposeP.Answer

/-!
Proofs for `Silmaril.Wasm.Abstract.ExposeP.Thms`, the frame: `CallXP.bodyCallXP C` is exactly the
finished answered paths of the exposed frame `frameXP` (`bodyCallXP_path`, `path_bodyCallXP`).
A pending tail call of the body is made as a call event only when the frame is left
(`frameK`), and answered as `FrameP.tail` reads its answer (`frameAns`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.ExposeP

open Silmaril.Wasm Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Abstract
  Silmaril.Wasm.Abstract.Body Silmaril.Wasm.Abstract.BodyTrace Silmaril.Wasm.Binaryen
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract.StoreBody Silmaril.Wasm.Abstract.StoreCall
  Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.CallXP Silmaril.Wasm.Abstract.ExposeP
  Silmaril.Elgot.ITree Silmaril.Proofs.Wasm.Abstract.StoreBody
  Silmaril.Proofs.Wasm.Abstract.BodyTrace Silmaril.Proofs.Wasm.Abstract.StoreCall
  Silmaril.Proofs.Wasm.Abstract.CallX

variable {H : Type}

/-! ## Frame results -/

theorem endF_ok {s : Store H} {fl : Flow} (h : fl ≠ .trap) :
    endF (s, fl) = .val (.ok (⟨fl⟩, ⟨s⟩)) := by
  cases fl <;> first | exact absurd rfl h | rfl

theorem endF_ok_inv {s : Store H} {fl : Flow} {a : ULift.{1} Flow} {t : St H}
    (h : endF (s, fl) = .val (.ok (a, t))) : fl ≠ .trap ∧ a = ⟨fl⟩ ∧ t = ⟨s⟩ := by
  cases fl <;> simp_all [endF]

theorem endF_err_inv {s : Store H} {fl : Flow} (h : endF (s, fl) = .val (.error ⟨⟩)) :
    fl = .trap := by
  cases fl <;> simp_all [endF]

/-! ## Leaving the frame -/

theorem run_frameK_tail {f : Frame} {fa n : Nat} {args : List Val} (s : Store H) :
    run' (frameK ⟨(f, .tail fa args n)⟩ : M (CallSig H) H (ULift.{1} Flow)) ⟨s⟩ =
      vis (⟨(fa, args, s), rfl⟩ : SigEv (CallSig H) (Store H × Flow))
        (fun ans => run' (frameAns n ans) ⟨s⟩) := by
  show run' (getState >>= fun s : St H =>
    callImport (E := CallSig H) (fa, args, s.down) >>= fun ans => frameAns n ans.down) ⟨s⟩ = _
  rw [run_getState_bind]
  have ht : run' (callImport (E := CallSig H) (S := St H) (T := PUnit.{2})
        (fa, args, s) >>= fun ans => frameAns n ans.down) ⟨s⟩ =
      vis (⟨(fa, args, s), rfl⟩ : SigEv (CallSig H) (Store H × Flow))
        (fun ans => run' (frameAns n ans) ⟨s⟩) := by
    rw [StoreBody.run_bind]
    refine (vis_bind _ _ _).trans ?_
    congr 1
    funext ans
    exact pure_bind _ _
  exact ht

theorem path_frameAns {n : Nat} {s₂ : Store H} {fl : Flow}
    (hfl : (∃ vs, fl.retVals = some vs) ∨ fl.Abrupt) (s : St H) :
    Path (run' (frameAns n (s₂, fl)) s) [] (endF (s₂, tailFlow n fl)) := by
  rcases hfl with ⟨vs, hvs⟩ | hab
  · cases fl with
    | normal ws =>
      simp only [Flow.retVals, Option.some.injEq] at hvs; subst hvs
      exact .ret (run_set_pure _ _ _)
    | ret ws =>
      simp only [Flow.retVals, Option.some.injEq] at hvs; subst hvs
      exact .ret (run_set_pure _ _ _)
    | brk k ws =>
      cases k with
      | zero =>
        simp only [Flow.retVals, Option.some.injEq] at hvs; subst hvs
        exact .ret (run_set_pure _ _ _)
      | succ k => simp [Flow.retVals] at hvs
    | trap => simp [Flow.retVals] at hvs
    | throw t => simp [Flow.retVals] at hvs
  · cases fl with
    | trap => exact .ret (run_trapS s)
    | throw t => exact .ret (run_set_pure _ _ _)
    | _ => exact absurd hab id

theorem path_frameAns_inv {n : Nat} {ans : Store H × Flow} {s : St H}
    {cs : List (Call (CallSig H))} {e : PathEnd (Except PUnit.{2} (ULift.{1} Flow × St H))}
    (h : Path (run' (frameAns n ans) s) cs e) (he : e ≠ .div) :
    cs = [] ∧ ((∃ vs, ans.2.retVals = some vs) ∨ ans.2.Abrupt) ∧
      e = endF (ans.1, tailFlow n ans.2) := by
  obtain ⟨s₂, fl⟩ := ans
  cases fl with
  | trap =>
    obtain ⟨rfl, rfl⟩ := path_ret_inv (run_trapS s) h
    exact ⟨rfl, .inr trivial, rfl⟩
  | throw t =>
    obtain ⟨rfl, rfl⟩ := path_ret_inv (run_set_pure _ _ _) h
    exact ⟨rfl, .inr trivial, rfl⟩
  | normal ws =>
    obtain ⟨rfl, rfl⟩ := path_ret_inv (run_set_pure _ _ _) h
    exact ⟨rfl, .inl ⟨ws, rfl⟩, rfl⟩
  | ret ws =>
    obtain ⟨rfl, rfl⟩ := path_ret_inv (run_set_pure _ _ _) h
    exact ⟨rfl, .inl ⟨ws, rfl⟩, rfl⟩
  | brk k ws =>
    cases k with
    | zero =>
      obtain ⟨rfl, rfl⟩ := path_ret_inv (run_set_pure _ _ _) h
      exact ⟨rfl, .inl ⟨ws, rfl⟩, rfl⟩
    | succ k => exact absurd (path_stuck_inv h) he

/-! ## Frame-level exactness -/

section
variable {C : CallRel H}

/-- **Every `bodyCallXP C` outcome is a path of the exposed frame**, with every call event
answered by `C`: the body's events, then the pending tail call's, if any. -/
theorem bodyCallXP_path {s : Store H} {a : Nat} {args : List Val} {out : Store H × Flow}
    (h : bodyCallXP C s a args out) :
    ∃ cs, Answered C cs ∧
      Path (run' (frameXP a args : M (CallSig H) H (ULift.{1} Flow)) ⟨s⟩) cs (endF out) := by
  obtain ⟨fi, fn, ps, rs, f₂, s₁, o, hfi, hcode, hty, hev, hfr⟩ := h
  obtain ⟨cs, hA, hp⟩ := evalOXP_path hev
  have hrun : run' (frameXP a args : M (CallSig H) H (ULift.{1} Flow)) ⟨s⟩ =
      run' (denListXP (liftInstrs fn.body) (Frame.forCall fi.module args fn.locals) [] >>=
        frameK) ⟨s⟩ := by
    rw [frameXP, run_getState_bind]
    simp only [hfi, hcode, hty]
  rw [hrun]
  cases hfr with
  | @flow _ fl =>
    cases fl
    case trap => exact ⟨cs, hA, path_bind_err hp⟩
    all_goals exact ⟨cs, hA, path_bind_pure hp rfl⟩
  | @tail _ s₂ fa n args' fl hcall hfl =>
    refine ⟨cs ++ [⟨(fa, args', s₁), (s₂, fl)⟩], answered_append hA (answered_single hcall), ?_⟩
    refine path_bind_ok hp ?_
    rw [run_frameK_tail]
    exact .vis rfl (path_frameAns hfl _)

/-- **The converse.** Every finished answered path of the exposed frame is a `bodyCallXP C`
outcome, ending as the path does. -/
theorem path_bodyCallXP {s : Store H} {a : Nat} {args : List Val}
    {cs : List (Call (CallSig H))} {e : PathEnd (Except PUnit.{2} (ULift.{1} Flow × St H))}
    (hA : Answered C cs)
    (h : Path (run' (frameXP a args : M (CallSig H) H (ULift.{1} Flow)) ⟨s⟩) cs e)
    (he : e ≠ .div) : ∃ out, bodyCallXP C s a args out ∧ endF out = e := by
  rw [frameXP, run_getState_bind] at h
  cases hfi : s.funcs[a]? with
  | none =>
    simp only [hfi] at h
    exact absurd (path_stuck_inv h) he
  | some fi =>
    simp only [hfi] at h
    cases hc : fi.code with
    | host hh =>
      simp only [hc] at h
      exact absurd (path_stuck_inv h) he
    | wasm fn =>
      cases hty : Validation.DefType.funcType? fi.type with
      | none =>
        simp only [hc, hty] at h
        exact absurd (path_stuck_inv h) he
      | some q =>
        obtain ⟨ps, rs⟩ := q
        simp only [hc, hty] at h
        rcases path_run_bind_inv h he with ⟨c₁, c₂, r, s₁, rfl, h₁, h₂⟩ | ⟨h₁, rfl⟩
        · obtain ⟨⟨s₁', f₂, o⟩, hev, hend⟩ :=
            list_ansXP _ s _ [] c₁ _ (answered_left hA) h₁ (by simp)
          obtain ⟨hnt, rfl, rfl⟩ := endRP_ok_inv hend
          cases o with
          | flow fl =>
            have h₂' : Path (run' (pure ⟨fl⟩ : M (CallSig H) H (ULift.{1} Flow)) ⟨s₁'⟩) c₂ e :=
              h₂
            obtain ⟨-, rfl⟩ := path_pure_inv h₂'
            exact ⟨(s₁', fl), ⟨fi, fn, ps, rs, f₂, s₁', .flow fl, hfi, hc, hty, hev, .flow⟩,
              endF_ok (fun h => hnt (congrArg POut.flow h))⟩
          | tail fa args' n =>
            rw [run_frameK_tail] at h₂
            obtain ⟨ans, cs', rfl, hp⟩ := Silmaril.Wasm.Abstract.BodyTrace.path_vis_inv h₂
            obtain ⟨rfl, hfl, rfl⟩ := path_frameAns_inv hp he
            have hC : C s₁' fa args' ans := (answered_right hA) _ (List.mem_cons_self ..)
            exact ⟨_, ⟨fi, fn, ps, rs, f₂, s₁', _, hfi, hc, hty, hev, .tail hC hfl⟩, rfl⟩
        · obtain ⟨⟨s₁', f₂, o⟩, hev, hend⟩ := list_ansXP _ s _ [] cs _ hA h₁ (by simp)
          obtain rfl := endRP_err_inv hend
          exact ⟨(s₁', .trap), ⟨fi, fn, ps, rs, f₂, s₁', _, hfi, hc, hty, hev, .flow⟩, rfl⟩

theorem bodyCallXP_iff {s : Store H} {a : Nat} {args : List Val} {s' : Store H} {fl : Flow}
    (hfl : fl ≠ .trap) :
    bodyCallXP C s a args (s', fl) ↔
      ∃ cs, Answered C cs ∧
        Path (run' (frameXP a args : M (CallSig H) H (ULift.{1} Flow)) ⟨s⟩) cs
          (.val (.ok (⟨fl⟩, ⟨s'⟩))) := by
  constructor
  · intro h
    obtain ⟨cs, hA, hp⟩ := bodyCallXP_path h
    exact ⟨cs, hA, endF_ok hfl ▸ hp⟩
  · rintro ⟨cs, hA, hp⟩
    obtain ⟨⟨s₁, fl₁⟩, hb, he⟩ := path_bodyCallXP hA hp (by simp)
    obtain ⟨-, h1, h2⟩ := endF_ok_inv he
    cases h1
    cases h2
    exact hb

theorem bodyCallXP_trap_iff {s : Store H} {a : Nat} {args : List Val} :
    (∃ s', bodyCallXP C s a args (s', .trap)) ↔
      ∃ cs, Answered C cs ∧
        Path (run' (frameXP a args : M (CallSig H) H (ULift.{1} Flow)) ⟨s⟩) cs
          (.val (.error ⟨⟩)) := by
  constructor
  · rintro ⟨s', h⟩
    exact bodyCallXP_path h
  · rintro ⟨cs, hA, hp⟩
    obtain ⟨⟨s₁, fl₁⟩, hb, he⟩ := path_bodyCallXP hA hp (by simp)
    obtain rfl := endF_err_inv he
    exact ⟨s₁, hb⟩

end

end Silmaril.Proofs.Wasm.Abstract.ExposeP

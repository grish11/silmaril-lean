module

public import Silmaril.Proofs.Wasm.Abstract.FunctorP.Basic

/-!
Proofs for `Silmaril.Wasm.Abstract.FunctorP.Thms`, the converse: every finished path of the
exposed body `ExposeP.denListXP` whose call events are answered by `C` is a logged run
(`EvalLXP`) with exactly that log (`list_ansL`). Construct by construct, as
`ExposeP.list_ansXP`, the log kept.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.FunctorP

open Silmaril.Wasm Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Abstract
  Silmaril.Wasm.Abstract.Body Silmaril.Wasm.Abstract.BodyTrace Silmaril.Wasm.Binaryen
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract.StoreBody Silmaril.Wasm.Abstract.StoreCall
  Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.CallXP Silmaril.Wasm.Abstract.ExposeE
  Silmaril.Wasm.Abstract.ExposeP Silmaril.Wasm.Abstract.FunctorP
  Silmaril.Elgot.ITree Silmaril.Proofs.Wasm.Abstract.StoreBody
  Silmaril.Proofs.Wasm.Abstract.BodyTrace Silmaril.Proofs.Wasm.Abstract.StoreCall
  Silmaril.Proofs.Wasm.Abstract.CallX Silmaril.Proofs.Wasm.Abstract.ExposeE
  Silmaril.Proofs.Wasm.Abstract.ExposeP
open Silmaril.Wasm.Abstract.CallXT (typeArity tailAnn)

variable {H : Type}

/-! ## Lifted answers -/

/-- How a lifted flow computation's path ends, from its flow computation's end. -/
def LiftEnd (e' : PathEnd (Except PUnit.{2} (Res × St H)))
    (v : Except PUnit.{2} (ResP × St H)) : Prop :=
  (∃ f₂ fl s₂, e' = .val (.ok (⟨(f₂, fl)⟩, ⟨s₂⟩)) ∧ v = .ok (⟨(f₂, .flow fl)⟩, ⟨s₂⟩)) ∨
    (e' = .val (.error ⟨⟩) ∧ v = .error ⟨⟩)

theorem LiftEnd.ne_div {e' : PathEnd (Except PUnit.{2} (Res × St H))}
    {v : Except PUnit.{2} (ResP × St H)} (h : LiftEnd e' v) : e' ≠ .div := by
  rcases h with ⟨_, _, _, rfl, -⟩ | ⟨rfl, -⟩ <;> simp

theorem liftP_inv {x : M (CallSig H) H Res} {s : St H} {cs : List (Call (CallSig H))}
    {v : Except PUnit.{2} (ResP × St H)} (h : Path (run' (liftP x) s) cs (.val v)) :
    ∃ e', Path (run' x s) cs e' ∧ LiftEnd e' v := by
  rcases path_run_bind_inv h (by simp) with ⟨c₁, c₂, a, s', rfl, h₁, h₂⟩ | ⟨h₁, hv⟩
  · obtain ⟨rfl, hv⟩ := path_pure_inv h₂
    cases hv
    obtain ⟨⟨f₂, fl⟩⟩ := a
    exact ⟨_, by simpa using h₁, .inl ⟨f₂, fl, s'.down, rfl, rfl⟩⟩
  · cases hv
    exact ⟨_, h₁, .inr ⟨rfl, rfl⟩⟩

theorem ansOut_vals {f : Frame} {stk : List Val} {ps rs : List Validation.CValType}
    {s₂ : Store H} {fl : Flow} {vs : List Val} (h : fl.retVals = some vs) :
    ansOut f stk ps rs (s₂, fl) =
      some (s₂, f, .flow (.normal (vs.take rs.length ++ stk.drop ps.length))) := by
  cases fl with
  | brk k ws => cases k <;> simp_all [ansOut, Flow.retVals]
  | _ => simp_all [ansOut, Flow.retVals]

theorem ansOut_of_callAns {f : Frame} {stk : List Val} {ps rs : List Validation.CValType}
    {ans : Store H × Flow} {s : St H} {cs : List (Call (CallSig H))}
    {e' : PathEnd (Except PUnit.{2} (Res × St H))} {v : Except PUnit.{2} (ResP × St H)}
    (hp : Path (run' (callAns f stk ps rs ans) s) cs e') (hv : LiftEnd e' v) :
    cs = [] ∧ ∃ r, ansOut f stk ps rs ans = some r ∧ endRP r = .val v := by
  obtain ⟨rfl, hcase⟩ := path_callAns_inv hp hv.ne_div
  refine ⟨rfl, ?_⟩
  obtain ⟨s₂, fl⟩ := ans
  rcases hcase with ⟨htr, rfl⟩ | ⟨t, hth, rfl⟩ | ⟨vs, hvs, rfl⟩
  · simp only at htr; subst htr
    rcases hv with ⟨_, _, _, h, -⟩ | ⟨-, rfl⟩
    · cases h
    · exact ⟨_, rfl, rfl⟩
  · simp only at hth; subst hth
    rcases hv with ⟨f₂, fl₂, s₃, h, rfl⟩ | ⟨h, -⟩
    · simp only [PathEnd.val.injEq, Except.ok.injEq, Prod.mk.injEq, ULift.up.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      exact ⟨_, rfl, rfl⟩
    · cases h
  · simp only at hvs
    rcases hv with ⟨f₂, fl₂, s₃, h, rfl⟩ | ⟨h, -⟩
    · simp only [PathEnd.val.injEq, Except.ok.injEq, Prod.mk.injEq, ULift.up.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      exact ⟨_, ansOut_vals hvs, rfl⟩
    · cases h

section
variable {C : CallRel H}

/-- An operator's finished answered path is a logged head. -/
theorem headL_ans {s₁ : Store H} {f₁ : Frame} {stk₁ : List Val} {i : Instr}
    {cs : List (Call (CallSig H))} {v : Except PUnit.{2} (ResP × St H)} (hA : Answered C cs)
    (h : Path (run' (opCXP i f₁ stk₁ : M (CallSig H) H ResP) ⟨s₁⟩) cs (.val v)) :
    ∃ r, HeadL C s₁ f₁ stk₁ i cs r ∧ endRP r = .val v := by
  cases hi : callEvInstr i with
  | false =>
    obtain rfl := (quiet_opCXP hi f₁ stk₁ s₁).path_nil h
    rw [← run_denListXP_op] at h
    obtain ⟨r, hev, hr⟩ := list_ansXP (C := C) _ s₁ f₁ stk₁ _ _ hA h (by simp)
    exact ⟨r, .quiet hi hev, hr⟩
  | true =>
    obtain ⟨x, rfl⟩ | ⟨x, y, rfl⟩ | ⟨y, rfl⟩ :
        (∃ x, i = .call x) ∨ (∃ x y, i = .callIndirect x y) ∨ (∃ y, i = .callRef y) := by
      cases i <;> simp_all [callEvInstr]
    · change Path (run' (liftP (callEv x f₁ stk₁)) ⟨s₁⟩) cs (.val v) at h
      obtain ⟨e', hp, hv⟩ := liftP_inv h
      obtain ⟨a, fi, ps, rs, ans, cs', hfi, hty, rfl, hp'⟩ := path_callEv_inv hp hv.ne_div
      obtain ⟨rfl, r, hr, hend⟩ := ansOut_of_callAns hp' hv
      exact ⟨r, .call hfi hty (hA _ (List.mem_cons_self ..)) hr, hend⟩
    · change Path (run' (liftP (indEvT x y f₁ stk₁)) ⟨s₁⟩) cs (.val v) at h
      obtain ⟨e', hp, hv⟩ := liftP_inv h
      rcases path_indEvT_inv hp hv.ne_div with ⟨fa, stk', hres, ht, hp'⟩ | ⟨stk', hres, rfl, rfl⟩
      · obtain ⟨fi, ps, rs, ans, cs', hfi, hty, rfl, hp''⟩ := path_callAt_inv hp' hv.ne_div
        obtain ⟨rfl, r, hr, hend⟩ := ansOut_of_callAns hp'' hv
        exact ⟨r, .ind hres hfi hty (ht fi ps rs hfi hty) (hA _ (List.mem_cons_self ..)) hr, hend⟩
      · rcases hv with ⟨_, _, _, h', -⟩ | ⟨-, rfl⟩
        · cases h'
        · exact ⟨_, .indNone hres, rfl⟩
    · change Path (run' (liftP (refEvT y f₁ stk₁)) ⟨s₁⟩) cs (.val v) at h
      obtain ⟨e', hp, hv⟩ := liftP_inv h
      rcases path_refEvT_inv hp hv.ne_div with ⟨fa, stk', hstk, ht, hp'⟩ | ⟨stk', hstk, rfl, rfl⟩
      · obtain ⟨fi, ps, rs, ans, cs', hfi, hty, rfl, hp''⟩ := path_callAt_inv hp' hv.ne_div
        obtain ⟨rfl, r, hr, hend⟩ := ansOut_of_callAns hp'' hv
        exact ⟨r, .ref hstk hfi hty (ht fi ps rs hfi hty) (hA _ (List.mem_cons_self ..)) hr, hend⟩
      · rcases hv with ⟨_, _, _, h', -⟩ | ⟨-, rfl⟩
        · cases h'
        · exact ⟨_, .refNull hstk, rfl⟩

/-- Finished answered paths of `es` are logged runs with that log. -/
def LAnsL (C : CallRel H) (es : List BExpr) : Prop :=
  ∀ s f stk cs e, Answered C cs →
    Path (run' (denListXP es f stk : M (CallSig H) H ResP) ⟨s⟩) cs e → e ≠ .div →
    ∃ r, EvalLXP C s f stk es cs r ∧ endRP r = e

/-- The same for a tree, as a one-tree sequence. -/
def TAnsL (C : CallRel H) (t : BExpr) : Prop :=
  ∀ s f stk cs e, Answered C cs →
    Path (run' (denXP t f stk : M (CallSig H) H ResP) ⟨s⟩) cs e → e ≠ .div →
    ∃ r, EvalLXP C s f stk [t] cs r ∧ endRP r = e

theorem POut.normal_eq {o : POut} (h : o.IsNormal) : ∃ stk, o = .flow (.normal stk) := by
  rcases o with fl | _
  · cases fl <;> first | exact ⟨_, rfl⟩ | exact absurd h id
  · exact absurd h id

theorem op_ansL {i : Instr} {args : List BExpr} (hargs : LAnsL C args) : TAnsL C (.op i args) := by
  intro s f stk cs e hA h he
  rw [denXP_op] at h
  rcases path_run_bind_inv h he with ⟨c₁, c₂, a, t, rfl, h₁, h₂⟩ | ⟨h₁, rfl⟩
  · obtain ⟨⟨s₀, f₀, o⟩, hev, hend⟩ := hargs s f stk c₁ _ (answered_left hA) h₁ (by simp)
    obtain ⟨hnt, rfl, rfl⟩ := endRP_ok_inv hend
    by_cases hn : o.IsNormal
    · obtain ⟨stk₁, rfl⟩ := POut.normal_eq hn
      obtain ⟨v, rfl⟩ : ∃ v, e = .val v := by
        rcases e with v | _
        · exact ⟨v, rfl⟩
        · exact absurd rfl he
      obtain ⟨r, hh, hr⟩ := headL_ans (answered_right hA) h₂
      exact ⟨r, .head hev hh, hr⟩
    · rw [thenKP_pass_eq hn] at h₂
      obtain ⟨rfl, rfl⟩ := path_pure_inv h₂
      rw [List.append_nil]
      exact ⟨_, .argsStop hev hn, hend⟩
  · obtain ⟨⟨s₀, f₀, o⟩, hev, hend⟩ := hargs s f stk cs _ hA h₁ (by simp)
    obtain rfl := endRP_err_inv hend
    exact ⟨_, .argsStop hev (notNormal_flowP Flow.notNormal_trap), rfl⟩

/-- A block body's path through its exits. -/
theorem arm_ansL {L : List BExpr} (hL : LAnsL C L) {np nr : Nat} {stk : List Val}
    {s : Store H} {f : Frame} {stk' : List Val} {cs : List (Call (CallSig H))}
    {e : PathEnd (Except PUnit.{2} (ResP × St H))} (hA : Answered C cs)
    (h : Path (run' (denListXP L f stk' >>= blockKP np nr stk : M (CallSig H) H ResP) ⟨s⟩) cs e)
    (he : e ≠ .div) :
    ∃ s₁ f₁ o, EvalLXP C s f stk' L cs (s₁, f₁, o) ∧ endRP (s₁, f₁, blockOutP np nr stk o) = e := by
  rcases path_run_bind_inv h he with ⟨c₁, c₂, a, t, rfl, h₁, h₂⟩ | ⟨h₁, rfl⟩
  · obtain ⟨⟨s₁, f₁, o⟩, hev, hend⟩ := hL s f stk' c₁ _ (answered_left hA) h₁ (by simp)
    obtain ⟨hnt, rfl, rfl⟩ := endRP_ok_inv hend
    rw [blockKP_eq] at h₂
    obtain ⟨rfl, rfl⟩ := path_pure_inv h₂
    rw [List.append_nil]
    refine ⟨s₁, f₁, o, hev, ?_⟩
    rw [blockOutP_eq]
    exact endRP_ok (fun h => hnt (blockFlowP_trap.1 h))
  · obtain ⟨⟨s₁, f₁, o⟩, hev, hend⟩ := hL s f stk' cs _ hA h₁ (by simp)
    obtain rfl := endRP_err_inv hend
    exact ⟨s₁, f₁, .flow .trap, hev, rfl⟩

theorem block_ansL {bt : BlockType} {body : List BExpr} (hbody : LAnsL C body) :
    TAnsL C (.block bt body) := by
  intro s f stk cs e hA h he
  rw [denXP_block] at h
  cases har : arity f bt with
  | none => simp only [har] at h; exact absurd (path_stuck_inv h) he
  | some p =>
    obtain ⟨np, nr⟩ := p
    simp only [har] at h
    obtain ⟨s₁, f₁, o, hev, hend⟩ := arm_ansL hbody hA h he
    exact ⟨_, .block har hev, hend⟩

theorem if_ansL {bt : BlockType} {c t el : List BExpr} (hc : LAnsL C c) (ht : LAnsL C t)
    (hel : LAnsL C el) : TAnsL C (.if_ bt c t el) := by
  intro s f stk cs e hA h he
  rw [denXP_if] at h
  rcases path_run_bind_inv h he with ⟨c₁, c₂, a, t', rfl, h₁, h₂⟩ | ⟨h₁, rfl⟩
  · obtain ⟨⟨s₁, f₁, o⟩, hev, hend⟩ := hc s f stk c₁ _ (answered_left hA) h₁ (by simp)
    obtain ⟨hnt, rfl, rfl⟩ := endRP_ok_inv hend
    by_cases hn : o.IsNormal
    · obtain ⟨stk₁, rfl⟩ := POut.normal_eq hn
      rcases stk₁ with _ | ⟨cv, stk₁⟩
      · exact absurd (path_stuck_inv h₂) he
      cases hb : truthy cv with
      | none => simp only [hb] at h₂; exact absurd (path_stuck_inv h₂) he
      | some b =>
        cases har : arity f₁ bt with
        | none => simp only [hb, har] at h₂; exact absurd (path_stuck_inv h₂) he
        | some p =>
          obtain ⟨np, nr⟩ := p
          simp only [hb, har] at h₂
          have hL : LAnsL C (if b then t else el) := by cases b <;> assumption
          have h₂' : Path (run' (denListXP (if b then t else el) f₁ (stk₁.take np) >>=
              blockKP np nr stk₁ : M (CallSig H) H ResP) ⟨s₁⟩) c₂ e := by
            cases b <;> exact h₂
          obtain ⟨s₂, f₂, o₂, hev₂, hend₂⟩ := arm_ansL hL (answered_right hA) h₂' he
          exact ⟨_, .ifArm hev hb har hev₂, hend₂⟩
    · have h₂' : Path (run' (pure ⟨(f₁, o)⟩ : M (CallSig H) H ResP) ⟨s₁⟩) c₂ e := by
        rcases o with fl | _
        · cases fl <;> first | exact absurd trivial hn | exact h₂
        · exact h₂
      obtain ⟨rfl, rfl⟩ := path_pure_inv h₂'
      rw [List.append_nil]
      exact ⟨_, .ifStop hev hn, hend⟩
  · obtain ⟨⟨s₁, f₁, o⟩, hev, hend⟩ := hc s f stk cs _ hA h₁ (by simp)
    obtain rfl := endRP_err_inv hend
    exact ⟨_, .ifStop hev (notNormal_flowP Flow.notNormal_trap), rfl⟩

theorem try_ansL {bt : BlockType} {cls : List Catch} {body : List BExpr}
    (hbody : LAnsL C body) : TAnsL C (.tryTable bt cls body) := by
  intro s f stk cs e hA h he
  rw [denXP_try] at h
  cases har : arity f bt with
  | none => simp only [har] at h; exact absurd (path_stuck_inv h) he
  | some p =>
    obtain ⟨np, nr⟩ := p
    simp only [har] at h
    rcases path_run_bind_inv h he with ⟨c₁, c₂, a, t, rfl, h₁, h₂⟩ | ⟨h₁, rfl⟩
    · obtain ⟨⟨s₁, f₁, o⟩, hev, hend⟩ :=
        hbody s f (stk.take np) c₁ _ (answered_left hA) h₁ (by simp)
      obtain ⟨hnt, rfl, rfl⟩ := endRP_ok_inv hend
      by_cases hth : ∃ a, o = .flow (.throw a)
      · obtain ⟨a, rfl⟩ := hth
        rw [run_tryKP_throw] at h₂
        cases hr : resolveCatch s₁ f₁ a cls with
        | none => simp only [hr] at h₂; exact absurd (path_stuck_inv h₂) he
        | some o =>
          have hc := resolveCatch_spec hr
          cases o with
          | some p =>
            obtain ⟨us, l⟩ := p
            simp only [hr] at h₂
            obtain ⟨rfl, rfl⟩ := path_pure_inv h₂
            rw [List.append_nil]
            exact ⟨_, .tryT har hev (.inr ⟨a, rfl, .inl ⟨us, l, hc, rfl⟩⟩), rfl⟩
          | none =>
            simp only [hr] at h₂
            obtain ⟨rfl, rfl⟩ := path_pure_inv h₂
            rw [List.append_nil]
            exact ⟨_, .tryT har hev (.inr ⟨a, rfl, .inr ⟨hc, rfl⟩⟩), rfl⟩
      · have hnt' : o.NotThrow := by
          rcases o with fl | _
          · cases fl <;> first | trivial | exact hth ⟨_, rfl⟩
          · trivial
        rw [tryKP_ne hnt', blockKP_eq] at h₂
        obtain ⟨rfl, rfl⟩ := path_pure_inv h₂
        rw [List.append_nil]
        refine ⟨_, .tryT har hev (.inl ⟨hnt', rfl⟩), ?_⟩
        rw [blockOutP_eq]
        exact endRP_ok (fun h => hnt (blockFlowP_trap.1 h))
    · obtain ⟨⟨s₁, f₁, o⟩, hev, hend⟩ := hbody s f (stk.take np) cs _ hA h₁ (by simp)
      obtain rfl := endRP_err_inv hend
      exact ⟨_, .tryT har hev (.inl ⟨trivial, rfl⟩), rfl⟩

/-- One loop iteration's path, inverted: the body runs to a logged outcome. -/
theorem loopIter_ansL {bt : BlockType} {body : List BExpr} (hbody : LAnsL C body)
    {p : ULift.{1} (Frame × List Val) × St H} {cs : List (Call (CallSig H))}
    {r' : PathEnd (Except PUnit.{2} ((ResP ⊕ ULift.{1} (Frame × List Val)) × St H))}
    (hA : Answered C cs) (h : Path (run' (loopBodyXP bt body p.1) p.2) cs r')
    (hr : r' ≠ .div) :
    ∃ np nr s₁ f₁ o, arity p.1.down.1 bt = some (np, nr) ∧
      EvalLXP C p.2.down p.1.down.1 (p.1.down.2.take np) body cs (s₁, f₁, o) ∧
      ((o = .flow .trap ∧ r' = .val (.error ⟨⟩)) ∨
       (o ≠ .flow .trap ∧ r' = .val (.ok (loopOutP np nr p.1.down.2 f₁ o, ⟨s₁⟩)))) := by
  obtain ⟨⟨f, stk⟩, ⟨s⟩⟩ := p
  simp only [loopBodyXP] at h
  cases har : arity f bt with
  | none => simp only [har] at h; exact absurd (path_stuck_inv h) hr
  | some q =>
    obtain ⟨np, nr⟩ := q
    simp only [har] at h
    rcases path_run_bind_inv h hr with ⟨c₁, c₂, a, t, rfl, h₁, h₂⟩ | ⟨h₁, hv⟩
    · obtain ⟨⟨s₁, f₁, o⟩, hev, hend⟩ := hbody s f (stk.take np) c₁ _ (answered_left hA) h₁
        (by simp)
      obtain ⟨hnt, rfl, rfl⟩ := endRP_ok_inv hend
      rw [loopKP_eq] at h₂
      obtain ⟨rfl, rfl⟩ := path_pure_inv h₂
      rw [List.append_nil]
      exact ⟨np, nr, s₁, f₁, o, rfl, hev, .inr ⟨hnt, rfl⟩⟩
    · obtain ⟨⟨s₁, f₁, o⟩, hev, hend⟩ := hbody s f (stk.take np) cs _ hA h₁ (by simp)
      obtain rfl := endRP_err_inv hend
      exact ⟨np, nr, s₁, f₁, .flow .trap, rfl, hev, .inl ⟨rfl, hv⟩⟩

theorem loop_ansL {bt : BlockType} {body : List BExpr} (hbody : LAnsL C body) :
    TAnsL C (.loop bt body) := by
  intro s f stk cs e hA h he
  let G := loopTree (loopBodyXP (H := H) bt body)
  have key : ∀ (p : ULift.{1} (Frame × List Val) × St H) cs
      (r : PathEnd (Except PUnit.{2} (ResP × St H))),
      IterPath G p cs r → Answered C cs → r ≠ .div →
      ∃ r', EvalLXP C p.2.down p.1.down.1 p.1.down.2 [.loop bt body] cs r' ∧ endRP r' = r := by
    intro p cs r hit
    induction hit with
    | @exit p cs y hp =>
      intro hA _
      obtain ⟨r', hp', hm⟩ := path_map_inv hp
      obtain ⟨np, nr, s₁, f₁, o, har, hev, ⟨rfl, hr'⟩ | ⟨hnt, hr'⟩⟩ :=
        loopIter_ansL hbody hA hp' (by rintro rfl; cases hm)
      · subst hr'
        cases hm
        exact ⟨_, .loopExit har hev (by simp), rfl⟩
      · subst hr'
        have hb : ∀ vs, o ≠ .flow (.brk 0 vs) := by
          rintro vs rfl; cases hm
        rw [loopOutP_of_ne hb] at hm
        cases hm
        refine ⟨_, .loopExit har hev hb, ?_⟩
        exact endRP_ok (fun h => hnt (blockOutP_trap.1 h))
    | div _ => intro _ h; exact absurd rfl h
    | @step p cs₁ p' cs₂ r hp _ ih =>
      intro hA hr
      obtain ⟨r', hp', hm⟩ := path_map_inv hp
      have hr'' := loopEnd_inr hm.symm
      obtain ⟨np, nr, s₁, f₁, o, har, hev, ⟨-, hr'⟩ | ⟨hnt, hr'⟩⟩ :=
        loopIter_ansL hbody (answered_left hA) hp' (by rw [hr'']; simp)
      · rw [hr''] at hr'; cases hr'
      · rw [hr''] at hr'
        simp only [PathEnd.val.injEq, Except.ok.injEq, Prod.mk.injEq] at hr'
        obtain ⟨hlo, hs⟩ := hr'
        obtain ⟨vs, rfl, hc⟩ := loopOutP_inr hlo.symm
        obtain ⟨r₁, hk, hr₁⟩ := ih (answered_right hA) hr
        rw [hc, hs] at hk
        exact ⟨r₁, .loopBack har hev hk, hr₁⟩
    | spin _ _ _ => intro _ h; exact absurd rfl h
  rw [denXP_loop] at h
  change Path ((((Silmaril.Elgot.iter (loopBodyXP bt body) ⟨(f, stk)⟩ :
    M (CallSig H) H _).run ⟨s⟩).run)) cs e at h
  rw [Silmaril.Wasm.Abstract.BodyTrace.run_iter] at h
  exact key _ _ _ (path_iter_iff.1 h) hA he

theorem cons_ansL {e : BExpr} {es : List BExpr} (he : TAnsL C e) (hes : LAnsL C es) :
    LAnsL C (e :: es) := by
  intro s f stk cs ee hA h hee
  rw [denListXP_cons] at h
  rcases path_run_bind_inv h hee with ⟨c₁, c₂, a, t, rfl, h₁, h₂⟩ | ⟨h₁, rfl⟩
  · obtain ⟨⟨s₀, f₀, o⟩, hev, hend⟩ := he s f stk c₁ _ (answered_left hA) h₁ (by simp)
    obtain ⟨hnt, rfl, rfl⟩ := endRP_ok_inv hend
    by_cases hn : o.IsNormal
    · obtain ⟨stk₁, rfl⟩ := POut.normal_eq hn
      obtain ⟨r, hk, hr⟩ := hes s₀ f₀ stk₁ c₂ ee (answered_right hA) h₂ hee
      exact ⟨r, .cons hev hk, hr⟩
    · rw [thenKP_pass_eq hn] at h₂
      obtain ⟨rfl, rfl⟩ := path_pure_inv h₂
      rw [List.append_nil]
      exact ⟨_, .stop hev hn, hend⟩
  · obtain ⟨⟨s₀, f₀, o⟩, hev, hend⟩ := he s f stk cs _ hA h₁ (by simp)
    obtain rfl := endRP_err_inv hend
    exact ⟨_, .stop hev (notNormal_flowP Flow.notNormal_trap), rfl⟩

mutual

theorem tree_ansL : ∀ (t : BExpr), TAnsL C t
  | .op _ args => op_ansL (list_ansL args)
  | .block _ body => block_ansL (list_ansL body)
  | .loop _ body => loop_ansL (list_ansL body)
  | .if_ _ c t el => if_ansL (list_ansL c) (list_ansL t) (list_ansL el)
  | .tryTable _ _ body => try_ansL (list_ansL body)

theorem list_ansL : ∀ (es : List BExpr), LAnsL C es
  | [] => fun s f stk cs e _ h _ => by
    obtain ⟨rfl, rfl⟩ := path_pure_inv h
    exact ⟨(s, f, .flow (.normal stk)), .nil, rfl⟩
  | e :: es => cons_ansL (tree_ansL e) (list_ansL es)

end

end

end Silmaril.Proofs.Wasm.Abstract.FunctorP

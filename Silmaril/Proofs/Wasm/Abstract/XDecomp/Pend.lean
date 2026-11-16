module

public import Silmaril.Proofs.Wasm.Abstract.XDecomp.Expose
public import Silmaril.Proofs.Wasm.Abstract.CallX.Answer

/-!
Proofs for `Silmaril.Wasm.Abstract.XDecomp.Thms`: the converse of `reachX_pend`.
A pending call event of the exposed body `CallX.denListX`, after call events
answered by `closedCallX`, is a descent `ReachX` (`list_pendX`). The structural
cases are `StoreCall`'s; the operator head adds the indirect, reference and
tail call events, inverted through their resolutions (`pend_indEv_inv`,
`pend_refEv_inv`, `pend_tailEv_inv`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.XDecomp

open Silmaril.Wasm Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Abstract
  Silmaril.Wasm.Abstract.Body Silmaril.Wasm.Abstract.BodyTrace Silmaril.Wasm.Binaryen
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract.StoreBody Silmaril.Wasm.Abstract.StoreCall
  Silmaril.Elgot.ITree Silmaril.Proofs.Wasm.Abstract.StoreBody Silmaril.Proofs.Wasm.Abstract.BodyTrace
  Silmaril.Proofs.Wasm.Abstract.StoreCall
open Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.XRecursion Silmaril.Wasm.Abstract.XDecomp
open Silmaril.Proofs.Wasm.Abstract.CallX

variable {H : Type}

/-! ## Pending call events of the extended forms, inverted -/

theorem not_pend_tailAns {f : Frame} {rs : List Validation.CValType} {ans : Store H × Flow}
    {s : St H} {cs : List (Call (CallSig H))} {m : (CallSig H).Op} :
    ¬ Pend (run' (tailAns f rs ans) s) cs m := by
  obtain ⟨s₂, fl⟩ := ans
  intro h
  cases fl with
  | trap => rw [show run' (tailAns f rs (s₂, .trap)) s = _ from run_trapS s] at h; exact not_pend_ret h
  | throw t => rw [show run' (tailAns f rs (s₂, .throw t)) s = _ from run_set_pure _ _ _] at h; exact not_pend_ret h
  | normal ws => rw [show run' (tailAns f rs (s₂, .normal ws)) s = _ from run_set_pure _ _ _] at h; exact not_pend_ret h
  | ret ws => rw [show run' (tailAns f rs (s₂, .ret ws)) s = _ from run_set_pure _ _ _] at h; exact not_pend_ret h
  | brk k ws =>
    cases k with
    | zero => rw [show run' (tailAns f rs (s₂, .brk 0 ws)) s = _ from run_set_pure _ _ _] at h; exact not_pend_ret h
    | succ k => exact not_pend_diverge h

theorem pend_callAt_inv {fa : Nat} {f : Frame} {stk : List Val} {s : Store H}
    {cs : List (Call (CallSig H))} {m : (CallSig H).Op} (h : Pend (run' (callAt fa f stk) ⟨s⟩) cs m) :
    ∃ fi ps rs, s.funcs[fa]? = some fi ∧ Validation.DefType.funcType? fi.type = some (ps, rs) ∧
      cs = [] ∧ m = (fa, (stk.take ps.length).reverse, s) := by
  cases hfi : s.funcs[fa]? with
  | none =>
    rw [callAt, run_getState_bind] at h
    simp only [hfi] at h
    exact absurd h not_pendR_stuck
  | some fi =>
    cases hty : Validation.DefType.funcType? fi.type with
    | none =>
      rw [callAt, run_getState_bind] at h
      simp only [hfi, hty] at h
      exact absurd h not_pendR_stuck
    | some p =>
      obtain ⟨ps, rs⟩ := p
      rw [run_callAt_vis hfi hty] at h
      rcases pend_vis_inv h with ⟨rfl, rfl⟩ | ⟨n, cs', rfl, hp⟩
      · exact ⟨fi, ps, rs, rfl, hty, rfl, rfl⟩
      · exact absurd hp not_pend_callAns

theorem pend_tailAt_inv {fa : Nat} {f : Frame} {stk : List Val} {s : Store H}
    {cs : List (Call (CallSig H))} {m : (CallSig H).Op} (h : Pend (run' (tailAt fa f stk) ⟨s⟩) cs m) :
    ∃ fi ps rs, s.funcs[fa]? = some fi ∧ Validation.DefType.funcType? fi.type = some (ps, rs) ∧
      cs = [] ∧ m = (fa, (stk.take ps.length).reverse, s) := by
  cases hfi : s.funcs[fa]? with
  | none =>
    rw [tailAt, run_getState_bind] at h
    simp only [hfi] at h
    exact absurd h not_pendR_stuck
  | some fi =>
    cases hty : Validation.DefType.funcType? fi.type with
    | none =>
      rw [tailAt, run_getState_bind] at h
      simp only [hfi, hty] at h
      exact absurd h not_pendR_stuck
    | some p =>
      obtain ⟨ps, rs⟩ := p
      rw [run_tailAt_vis hfi hty] at h
      rcases pend_vis_inv h with ⟨rfl, rfl⟩ | ⟨n, cs', rfl, hp⟩
      · exact ⟨fi, ps, rs, rfl, hty, rfl, rfl⟩
      · exact absurd hp not_pend_tailAns

theorem pend_indEv_inv {x : TableIdx} {y : TypeIdx} {f : Frame} {stk : List Val} {s : Store H}
    {cs : List (Call (CallSig H))} {m : (CallSig H).Op} (h : Pend (run' (indEv x y f stk) ⟨s⟩) cs m) :
    ∃ fa stk₁, IndResS s f x y stk (some fa, stk₁) ∧ Pend (run' (callAt fa f stk₁) ⟨s⟩) cs m := by
  rw [indEv, run_getState_bind] at h
  cases hr : resolveInd s f x y stk with
  | none => simp only [hr] at h; exact absurd h not_pendR_stuck
  | some p =>
    obtain ⟨o, stk₁⟩ := p
    have hs := Silmaril.Proofs.Wasm.Abstract.CallX.resolveInd_spec hr
    cases o with
    | some fa => simp only [hr] at h; exact ⟨fa, stk₁, hs, h⟩
    | none =>
      simp only [hr] at h
      rw [run_trapS] at h
      exact absurd h not_pend_ret

theorem pend_refEv_inv {f : Frame} {stk : List Val} {s : Store H}
    {cs : List (Call (CallSig H))} {m : (CallSig H).Op} (h : Pend (run' (refEv f stk) ⟨s⟩) cs m) :
    ∃ fa stk₁, stk = .ref (.func fa) :: stk₁ ∧ Pend (run' (callAt fa f stk₁) ⟨s⟩) cs m := by
  unfold refEv at h
  split at h
  · exact ⟨_, _, rfl, h⟩
  · rw [run_trapS] at h; exact absurd h not_pend_ret
  · exact absurd h not_pendR_stuck

theorem pend_tailEv_inv {i : Instr} {f : Frame} {stk : List Val} {s : Store H}
    {cs : List (Call (CallSig H))} {m : (CallSig H).Op} (h : Pend (run' (tailEv i f stk) ⟨s⟩) cs m) :
    ∃ fa stk₁, TailRes s f i stk (some (fa, stk₁)) ∧ Pend (run' (tailAt fa f stk₁) ⟨s⟩) cs m := by
  rw [tailEv, run_getState_bind] at h
  cases hr : resolveTail s f i stk with
  | none => simp only [hr] at h; exact absurd h not_pendR_stuck
  | some o =>
    have hs := Silmaril.Proofs.Wasm.Abstract.CallX.resolveTail_spec hr
    cases o with
    | some p =>
      obtain ⟨fa, stk₁⟩ := p
      simp only [hr] at h
      exact ⟨fa, stk₁, hs, h⟩
    | none =>
      simp only [hr] at h
      rw [run_trapS] at h
      exact absurd h not_pend_ret

/-! ## Pending calls are descents -/

/-- Pending calls of the exposed body of `es` after `closedCallX` answers are descents. -/
def PReX (es : List BExpr) : Prop :=
  ∀ (s : Store H) (f : Frame) (stk : List Val) (cs : List (Call (CallSig H))) (m : (CallSig H).Op),
    Answered closedCallX cs →
    Pend (run' (denListX es f stk : M (CallSig H) H Res) ⟨s⟩) cs m →
    ReachX s f stk es (opOf m)

theorem lans_closedX (es : List BExpr) : LAnsX (closedCallX : CallRel H) es := list_ansX es

/-- A finished head followed by a pending call in the continuation. -/
theorem cont_pendX {es : List BExpr} (hes : PReX (H := H) es) {x : M (CallSig H) H Res} {s : St H}
    {cs : List (Call (CallSig H))} {m : (CallSig H).Op} {Q : Store H × Frame × Flow → Prop}
    (hA : Answered closedCallX cs) (h : Pend (run' (x >>= thenK (denListX es)) s) cs m)
    (hx : ∀ cs₁ v, Answered closedCallX cs₁ → Path (run' x s) cs₁ (.val v) →
      ∃ r₀, Q r₀ ∧ endR r₀ = .val v) :
    Pend (run' x s) cs m ∨
      ∃ s₁ f₁ stk₁, Q (s₁, f₁, .normal stk₁) ∧ ReachX s₁ f₁ stk₁ es (opOf m) := by
  rcases pendR_bind_inv h with h₁ | ⟨cs₁, cs₂, a, t, rfl, h₁, h₂⟩
  · exact .inl h₁
  · obtain ⟨⟨s₁, f₁, fl⟩, hQ, hend⟩ := hx cs₁ _ (answered_left hA) h₁
    obtain ⟨-, rfl, rfl⟩ := endR_ok_inv hend
    by_cases hn : fl.IsNormal
    · obtain ⟨stk₁, rfl⟩ : ∃ stk₁, fl = .normal stk₁ := by
        cases fl <;> first | exact ⟨_, rfl⟩ | exact absurd hn id
      exact .inr ⟨s₁, f₁, stk₁, hQ, hes s₁ f₁ stk₁ cs₂ m (answered_right hA) h₂⟩
    · rw [thenK_pass_eq hn] at h₂
      exact absurd h₂ not_pendR_pure

/-- A pending call event at an operator after its arguments returned. -/
theorem head_pendX {i : Instr} {s₁ : Store H} {f₁ : Frame} {stk₁ : List Val}
    {cs : List (Call (CallSig H))} {m : (CallSig H).Op} {s : Store H} {f : Frame} {stk : List Val}
    {args es : List BExpr} (hev : EvalOX closedCallX s f stk args (s₁, f₁, .normal stk₁))
    (h : Pend (run' (opCX i f₁ stk₁ : M (CallSig H) H Res) ⟨s₁⟩) cs m) :
    ReachX s f stk (.op i args :: es) (opOf m) := by
  by_cases hc : ∃ x, i = .call x
  · obtain ⟨x, rfl⟩ := hc
    obtain ⟨a, fi, ps, rs, hfi, hty, -, rfl⟩ := pend_callEv_inv h
    exact .here hev hfi hty
  have hi : ∀ x, i ≠ .call x := fun x hx => hc ⟨x, hx⟩
  cases hx : isXCall i with
  | false =>
    rw [opCX_flat hi hx] at h
    exact absurd h not_pendR_flatK
  | true =>
    obtain ⟨x, y, rfl⟩ | ⟨y, rfl⟩ | htail :
        (∃ x y, i = .callIndirect x y) ∨ (∃ y, i = .callRef y) ∨ isXTail i := by
      cases i <;> simp_all [isXCall, isXTail]
    · obtain ⟨fa, stk', ⟨ad, j, rfl, hres⟩, hp⟩ := pend_indEv_inv h
      obtain ⟨fi, ps, rs, hfi, hty, -, rfl⟩ := pend_callAt_inv hp
      exact .hereInd hev hres hfi hty
    · obtain ⟨fa, stk', rfl, hp⟩ := pend_refEv_inv h
      obtain ⟨fi, ps, rs, hfi, hty, -, rfl⟩ := pend_callAt_inv hp
      exact .hereRef hev hfi hty
    · rw [opCX_tail htail] at h
      obtain ⟨fa, stk', hres, hp⟩ := pend_tailEv_inv h
      obtain ⟨fi, ps, rs, hfi, hty, -, rfl⟩ := pend_tailAt_inv hp
      obtain rfl := tailRes_drop hres
      exact .hereTail hev hres hfi hty

theorem body_of_closedCallX {s₁ s₂ : Store H} {fa : Nat} {args : List Val} {fl : Flow}
    {fi : FuncInst H} (hC : closedCallX s₁ fa args (s₂, fl))
    (hfi : s₁.funcs[fa]? = some fi) :
    ∃ fn f₃, fi.code = .wasm fn ∧ EvalOX closedCallX s₁ (Frame.forCall fi.module args fn.locals) []
      (liftInstrs fn.body) (s₂, f₃, fl) := by
  rw [closedCallX_fixpoint] at hC
  obtain ⟨fi', fn, ps', rs', f₃, hfi', hcode, hty', hbody⟩ := hC
  rw [hfi] at hfi'
  obtain rfl := Option.some.inj hfi'
  exact ⟨fn, f₃, hcode, hbody⟩

theorem op_pendX {i : Instr} {args es : List BExpr} (hargs : PReX (H := H) args)
    (hes : PReX (H := H) es) {s : Store H} {f : Frame} {stk : List Val}
    {cs : List (Call (CallSig H))} {m : (CallSig H).Op} (hA : Answered closedCallX cs)
    (h : Pend (run' (denX (.op i args) f stk >>= thenK (denListX es)) ⟨s⟩) cs m) :
    ReachX s f stk (.op i args :: es) (opOf m) := by
  rw [denX_op] at h
  rcases cont_pendX hes hA h (opHeadX_ans (lans_closedX args)) with h₁ |
    ⟨s₂, f₂, stk₂, hQ, hk⟩
  · rcases pendR_bind_inv h₁ with h₂ | ⟨c₁, c₂, a, t, rfl, h₂, h₃⟩
    · exact .args (hargs s f stk cs m hA h₂)
    · obtain ⟨⟨s₁, f₁, fl⟩, hev, hend⟩ := lans_closedX args s f stk c₁ _ (answered_left hA) h₂
        (by simp)
      obtain ⟨-, rfl, rfl⟩ := endR_ok_inv hend
      by_cases hn : fl.IsNormal
      · obtain ⟨stk₁, rfl⟩ : ∃ stk₁, fl = .normal stk₁ := by
          cases fl <;> first | exact ⟨_, rfl⟩ | exact absurd hn id
        exact head_pendX hev h₃
      · rw [thenK_pass_eq hn] at h₃
        exact absurd h₃ not_pendR_pure
  · rcases hQ with ⟨hn, -⟩ | ⟨s₁, f₁, stk₁, hev, hhead⟩
    · exact absurd trivial hn
    generalize hr : (s₂, f₂, Flow.normal stk₂) = r at hhead
    cases hhead with
    | flat hi hflat => subst hr; exact .opK hi hev hflat hk
    | callRet hfi hty hC hvs =>
      simp only [Prod.mk.injEq, Flow.normal.injEq] at hr
      obtain ⟨rfl, rfl, rfl⟩ := hr
      obtain ⟨fn, f₃, hcode, hbody⟩ := body_of_closedCallX hC (funcs_of_func? hfi)
      exact .callK hev hfi hcode hty hbody hvs hk
    | callTrap => simp at hr
    | callThrow => simp at hr
    | indRet hres hfi hty hC hvs =>
      simp only [Prod.mk.injEq, Flow.normal.injEq] at hr
      obtain ⟨rfl, rfl, rfl⟩ := hr
      obtain ⟨ad, j, rfl, hres⟩ := hres
      obtain ⟨fn, f₃, hcode, hbody⟩ := body_of_closedCallX hC hfi
      exact .callIndK hev hres hfi hcode hty hbody hvs hk
    | indStop _ _ _ _ hfl =>
      simp only [Prod.mk.injEq] at hr
      obtain ⟨-, -, rfl⟩ := hr
      exact absurd hfl id
    | indRes => simp at hr
    | refRet hstk hfi hty hC hvs =>
      simp only [Prod.mk.injEq, Flow.normal.injEq] at hr
      obtain ⟨rfl, rfl, rfl⟩ := hr
      subst hstk
      obtain ⟨fn, f₃, hcode, hbody⟩ := body_of_closedCallX hC hfi
      exact .callRefK hev hfi hcode hty hbody hvs hk
    | refStop _ _ _ _ hfl =>
      simp only [Prod.mk.injEq] at hr
      obtain ⟨-, -, rfl⟩ := hr
      exact absurd hfl id
    | refNull => simp at hr
    | tail =>
      simp only [Prod.mk.injEq] at hr
      obtain ⟨-, -, hfl⟩ := hr
      exact absurd (by rw [← hfl]; trivial) (tailFlow_notNormal _ _)
    | tailRes => simp at hr

theorem block_pendX {bt : BlockType} {body es : List BExpr} (hbody : PReX (H := H) body) (hes : PReX (H := H) es)
    {s : Store H} {f : Frame} {stk : List Val} {cs : List (Call (CallSig H))}
    {m : (CallSig H).Op} (hA : Answered closedCallX cs)
    (h : Pend (run' (denX (.block bt body) f stk >>= thenK (denListX es)) ⟨s⟩) cs m) :
    ReachX s f stk (.block bt body :: es) (opOf m) := by
  rw [denX_block] at h
  cases har : arity f bt with
  | none =>
    simp only [har] at h
    rcases pendR_bind_inv h with h₁ | ⟨_, _, _, _, _, h₁, _⟩
    · exact absurd h₁ not_pendR_stuck
    · exact absurd (path_stuck_inv h₁) (by simp)
  | some p =>
    obtain ⟨np, nr⟩ := p
    simp only [har] at h
    rcases cont_pendX (Q := BlockHeadX closedCallX s f stk bt body) hes hA h
      (fun cs₁ v hA₁ h₁ => by
        obtain ⟨s₁, f₁, fl, hev, hend⟩ := blockArm_ansX (lans_closedX body) cs₁ v hA₁ h₁
        exact ⟨_, ⟨np, nr, s₁, f₁, fl, har, hev, rfl⟩, hend⟩) with h₁ |
      ⟨s₂, f₂, stk₂, ⟨np', nr', s₁, f₁, fl, har', hev, hr₀⟩, hk⟩
    · rcases pendR_bind_inv h₁ with h₂ | ⟨c₁, c₂, a, t, rfl, -, h₃⟩
      · exact .block har (hbody s f _ cs m hA h₂)
      · obtain ⟨⟨f', fl'⟩⟩ := a
        rw [blockK_eq] at h₃
        exact absurd h₃ not_pendR_pure
    · rw [har] at har'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj har')
      simp only [Prod.mk.injEq] at hr₀
      obtain ⟨rfl, rfl, hfl⟩ := hr₀
      cases fl with
      | normal vs =>
        simp only [blockFlow, Flow.normal.injEq] at hfl
        subst hfl
        exact .blockK har hev rfl hk
      | brk k vs =>
        cases k with
        | zero =>
          simp only [blockFlow, Flow.normal.injEq] at hfl
          subst hfl
          exact .blockK har hev rfl hk
        | succ k => simp [blockFlow] at hfl
      | _ => simp [blockFlow] at hfl

theorem if_pendX {bt : BlockType} {c t el es : List BExpr} (hc : PReX (H := H) c)
    (ht : PReX (H := H) t) (hel : PReX (H := H) el) (hes : PReX (H := H) es)
    {s : Store H} {f : Frame} {stk : List Val} {cs : List (Call (CallSig H))}
    {m : (CallSig H).Op} (hA : Answered closedCallX cs)
    (h : Pend (run' (denX (.if_ bt c t el) f stk >>= thenK (denListX es)) ⟨s⟩) cs m) :
    ReachX s f stk (.if_ bt c t el :: es) (opOf m) := by
  rw [denX_if] at h
  rcases cont_pendX (Q := IfHeadX closedCallX s f stk bt c t el) hes hA h
    (ifHead_ansX (lans_closedX c) (lans_closedX t) (lans_closedX el)) with h₁ |
    ⟨s₂, f₂, stk₂, hQ, hk⟩
  · rcases pendR_bind_inv h₁ with h₂ | ⟨c₁, c₂, a, t', rfl, h₂, h₃⟩
    · exact .cond (hc s f stk cs m hA h₂)
    · obtain ⟨⟨s₁, f₁, fl⟩, hev, hend⟩ := lans_closedX c s f stk c₁ _ (answered_left hA) h₂
        (by simp)
      obtain ⟨-, rfl, rfl⟩ := endR_ok_inv hend
      by_cases hn : fl.IsNormal
      · obtain ⟨stk₁, rfl⟩ : ∃ stk₁, fl = .normal stk₁ := by
          cases fl <;> first | exact ⟨_, rfl⟩ | exact absurd hn id
        rcases stk₁ with _ | ⟨cv, stk₁⟩
        · exact absurd h₃ not_pendR_stuck
        cases hb : truthy cv with
        | none => simp only [hb] at h₃; exact absurd h₃ not_pendR_stuck
        | some b =>
          cases har : arity f₁ bt with
          | none => simp only [hb, har] at h₃; exact absurd h₃ not_pendR_stuck
          | some p =>
            obtain ⟨np, nr⟩ := p
            simp only [hb, har] at h₃
            rcases pendR_bind_inv h₃ with h₄ | ⟨_, c₄, a', _, _, -, h₄⟩
            · refine .arm hev hb har ?_
              cases b
              · exact hel _ _ _ _ m (answered_right hA) h₄
              · exact ht _ _ _ _ m (answered_right hA) h₄
            · obtain ⟨⟨f', fl'⟩⟩ := a'
              rw [blockK_eq] at h₄
              exact absurd h₄ not_pendR_pure
      · have h₃' : Pend (run' (pure ⟨(f₁, fl)⟩ : M (CallSig H) H Res) ⟨s₁⟩) c₂ m := by
          cases fl <;> first | exact absurd trivial hn | exact h₃
        exact absurd h₃' not_pendR_pure
  · rcases hQ with ⟨hn, -⟩ | ⟨s₁, f₁, cv, stk₁, b, np, nr, s₃, f₃, fl, hev, hb, har, hev₂, hr₀⟩
    · exact absurd trivial hn
    · simp only [Prod.mk.injEq] at hr₀
      obtain ⟨rfl, rfl, hfl⟩ := hr₀
      cases fl with
      | normal vs =>
        simp only [blockFlow, Flow.normal.injEq] at hfl
        subst hfl
        exact .ifK hev hb har hev₂ rfl hk
      | brk k vs =>
        cases k with
        | zero =>
          simp only [blockFlow, Flow.normal.injEq] at hfl
          subst hfl
          exact .ifK hev hb har hev₂ rfl hk
        | succ k => simp [blockFlow] at hfl
      | _ => simp [blockFlow] at hfl

theorem loop_pendX {bt : BlockType} {body es : List BExpr} (hbody : PReX (H := H) body)
    (hes : PReX (H := H) es) {s : Store H} {f : Frame} {stk : List Val}
    {cs : List (Call (CallSig H))} {m : (CallSig H).Op} (hA : Answered closedCallX cs)
    (h : Pend (run' (denX (.loop bt body) f stk >>= thenK (denListX es)) ⟨s⟩) cs m) :
    ReachX s f stk (.loop bt body :: es) (opOf m) := by
  let G := loopTree (loopBodyX (H := H) bt body)
  have hloop : ∀ f stk s, run' (denX (.loop bt body) f stk : M (CallSig H) H Res) ⟨s⟩ =
      iterT G (⟨(f, stk)⟩, ⟨s⟩) := by
    intro f stk s
    rw [denX_loop]
    exact Silmaril.Wasm.Abstract.BodyTrace.run_iter _ _ _
  -- pending calls inside the loop
  have kin : ∀ (p : ULift.{1} (Frame × List Val) × St H) cs m, IterPend G p cs m →
      Answered closedCallX cs → ReachX p.2.down p.1.down.1 p.1.down.2 (.loop bt body :: es) (opOf m) := by
    intro p cs m hp
    induction hp with
    | @inside p cs m hp =>
      intro hA
      rcases pend_bind_inv hp with h₁ | ⟨_, _, _, _, _, h₂⟩
      · obtain ⟨⟨f, stk⟩, ⟨s⟩⟩ := p
        have h₁' : Pend (run' (loopBodyX bt body ⟨(f, stk)⟩ : M (CallSig H) H _) ⟨s⟩) cs m := h₁
        simp only [loopBodyX] at h₁'
        cases har : arity f bt with
        | none => simp only [har] at h₁'; exact absurd h₁' not_pendR_stuck
        | some q =>
          obtain ⟨np, nr⟩ := q
          simp only [har] at h₁'
          rcases pendR_bind_inv h₁' with h₂ | ⟨_, _, a, _, _, _, h₃⟩
          · exact .loop har (hbody s f _ cs m hA h₂)
          · obtain ⟨⟨f', fl'⟩⟩ := a
            rw [loopK_eq] at h₃
            exact absurd h₃ not_pendR_pure
      · exact absurd h₂ not_pend_ret
    | @step p cs₁ p' cs₂ m hp _ ih =>
      intro hA
      obtain ⟨r', hp', hm⟩ := path_map_inv hp
      have hr'' := loopEnd_inr hm.symm
      obtain ⟨np, nr, s₁, f₁, fl, har, hev, ⟨-, hr'⟩ | ⟨hnt, hr'⟩⟩ :=
        loopIter_ansX (lans_closedX body) (answered_left hA) hp' (by rw [hr'']; simp)
      · rw [hr''] at hr'; cases hr'
      · rw [hr''] at hr'
        simp only [PathEnd.val.injEq, Except.ok.injEq, Prod.mk.injEq] at hr'
        obtain ⟨hlo, hs⟩ := hr'
        obtain ⟨vs, rfl, hc⟩ := loopOut_inr hlo.symm
        have := ih (answered_right hA)
        rw [hc, hs] at this
        exact .loopBack har hev this
  -- pending calls in the continuation after the loop
  let kk : Except PUnit.{2} (Res × St H) → Tree (SigEv (CallSig H)) (Except PUnit.{2} (Res × St H)) :=
    fun r => match r with
      | .ok (a, s') => run' (thenK (denListX es) a) s'
      | .error e => pure (.error e)
  have kout : ∀ (p : ULift.{1} (Frame × List Val) × St H) cs₁ (r : PathEnd (Except PUnit.{2} (Res × St H))),
      IterPath G p cs₁ r → ∀ v, r = .val v → ∀ cs₂ m, Answered closedCallX (cs₁ ++ cs₂) →
      Pend (kk v) cs₂ m → ReachX p.2.down p.1.down.1 p.1.down.2 (.loop bt body :: es) (opOf m) := by
    intro p cs₁ r hit
    induction hit with
    | @exit p cs y hp =>
      intro v hv cs₂ m hA h₂
      cases hv
      obtain ⟨r', hp', hm⟩ := path_map_inv hp
      rcases loopEnd_inl hm.symm with ⟨e, rfl, rfl⟩ | ⟨b, s', rfl, rfl⟩
      · exact absurd h₂ not_pend_ret
      · obtain ⟨np, nr, s₁, f₁, fl, har, hev, ⟨-, hr'⟩ | ⟨hnt, hr'⟩⟩ :=
          loopIter_ansX (lans_closedX body) (answered_left hA) hp' (by simp)
        · cases hr'
        · simp only [PathEnd.val.injEq, Except.ok.injEq, Prod.mk.injEq] at hr'
          obtain ⟨hlo, rfl⟩ := hr'
          rcases loopOut_inl hlo.symm with ⟨vs, rfl, rfl⟩ | ⟨k, vs, rfl, rfl⟩ | ⟨hesc, rfl⟩
          · exact .loopK har hev (hes s₁ f₁ _ cs₂ m (answered_right hA) h₂)
          · have h₂' : Pend (run' (pure ⟨(f₁, .brk k vs)⟩ : M (CallSig H) H Res) ⟨s₁⟩) cs₂ m := h₂
            exact absurd h₂' not_pendR_pure
          · rw [show kk (.ok (⟨(f₁, fl)⟩, ⟨s₁⟩)) = run' (pure ⟨(f₁, fl)⟩ : M (CallSig H) H Res) ⟨s₁⟩
              from congrArg (fun x => run' x ⟨s₁⟩)
                (thenK_pass_eq (Flow.not_normal_of_escapes hesc))] at h₂
            exact absurd h₂ not_pendR_pure
    | div _ => intro v hv; cases hv
    | @step p cs₁ p' cs₂' r hp _ ih =>
      intro v hv cs₂ m hA h₂
      obtain ⟨r', hp', hm⟩ := path_map_inv hp
      have hr'' := loopEnd_inr hm.symm
      obtain ⟨np, nr, s₁, f₁, fl, har, hev, ⟨-, hr'⟩ | ⟨hnt, hr'⟩⟩ :=
        loopIter_ansX (lans_closedX body) (answered_left (answered_left (by rw [List.append_assoc] at hA ⊢; exact hA)))
          hp' (by rw [hr'']; simp)
      · rw [hr''] at hr'; cases hr'
      · rw [hr''] at hr'
        simp only [PathEnd.val.injEq, Except.ok.injEq, Prod.mk.injEq] at hr'
        obtain ⟨hlo, hs⟩ := hr'
        obtain ⟨vs, rfl, hc⟩ := loopOut_inr hlo.symm
        have := ih v hv cs₂ m (by rw [List.append_assoc] at hA; exact answered_right hA) h₂
        rw [hc, hs] at this
        exact .loopBack har hev this
    | spin _ _ _ => intro v hv; cases hv
  rcases pendR_bind_inv h with h₁ | ⟨cs₁, cs₂, a, s₁, rfl, h₁, h₂⟩
  · rw [hloop] at h₁
    exact kin _ cs m (pend_iterPend h₁) hA
  · rw [hloop] at h₁
    exact kout _ cs₁ _ (path_iter_iff.1 h₁) (.ok (a, s₁)) rfl cs₂ m hA h₂

mutual

theorem tree_pendX : ∀ (e : BExpr) (es : List BExpr), PReX (H := H) es →
    ∀ (s : Store H) (f : Frame) (stk : List Val) (cs : List (Call (CallSig H)))
      (m : (CallSig H).Op), Answered closedCallX cs →
    Pend (run' (denX e f stk >>= thenK (denListX es)) ⟨s⟩) cs m →
    ReachX s f stk (e :: es) (opOf m)
  | .op i args, es, hes, _, _, _, _, _, hA, h => op_pendX (list_pendX args) hes hA h
  | .block bt body, es, hes, _, _, _, _, _, hA, h => block_pendX (list_pendX body) hes hA h
  | .loop bt body, es, hes, _, _, _, _, _, hA, h => loop_pendX (list_pendX body) hes hA h
  | .if_ bt c t el, es, hes, _, _, _, _, _, hA, h =>
    if_pendX (list_pendX c) (list_pendX t) (list_pendX el) hes hA h
  | .tryTable .., _, _, _, _, _, _, _, _, h => by
    rw [denX.eq_def] at h
    rcases pendR_bind_inv h with h₁ | ⟨_, _, _, _, _, h₁, _⟩
    · exact absurd h₁ not_pendR_stuck
    · exact absurd (path_stuck_inv h₁) (by simp)

theorem list_pendX : ∀ (es : List BExpr), PReX (H := H) es
  | [] => fun _ _ _ _ _ _ h => absurd h not_pendR_pure
  | e :: es => fun s f stk cs m hA h => by
    rw [denListX_cons] at h
    exact tree_pendX e es (list_pendX es) s f stk cs m hA h

end

end Silmaril.Proofs.Wasm.Abstract.XDecomp

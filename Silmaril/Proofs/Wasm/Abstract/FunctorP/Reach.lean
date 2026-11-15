module

public import Silmaril.Proofs.Wasm.Abstract.FunctorP.Back

/-!
Proofs for `Silmaril.Wasm.Abstract.FunctorP.Thms`: logged pending observations (`ReachXP`) are
exactly the pending calls of the exposed body after answered events (`reachXP_pend`,
`list_reachL`), and the frame-level versions (`frameLXP_path`, `path_frameLXP`,
`frameReachXP_pend`, `pend_frameReachXP`).
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

/-! ## Operator events -/

theorem pend_liftP {x : M (CallSig H) H Res} {s : St H} {cs : List (Call (CallSig H))}
    {m : (CallSig H).Op} : Pend (run' (liftP x) s) cs m ↔ Pend (run' x s) cs m := by
  constructor
  · intro h
    rcases pendR_bind_inv h with h₁ | ⟨_, _, _, _, _, _, h₂⟩
    · exact h₁
    · exact absurd h₂ not_pendR_pure
  · exact pendR_bind_left

theorem pend_callAtT {y : TypeIdx} {fa : Nat} {f : Frame} {stk : List Val} {s : Store H}
    {fi : FuncInst H} {ps rs : List Validation.CValType} (hfi : s.funcs[fa]? = some fi)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hy : typeArity f.module y = some (ps.length, rs.length)) :
    Pend (run' (callAtT y fa f stk) ⟨s⟩) [] (fa, (stk.take ps.length).reverse, s) := by
  rw [callAtT, run_getState_bind]
  rw [ite_eq_left (calleeTyped_of hfi hty hy)]
  rw [run_callAt_vis hfi hty]
  exact .here rfl

theorem headEv_pend {s : Store H} {f : Frame} {stk : List Val} {i : Instr}
    {y : Nat × List Val × Store H} (h : HeadEv s f stk i y) :
    Pend (run' (opCXP i f stk : M (CallSig H) H ResP) ⟨s⟩) [] y := by
  cases h with
  | call hfi hty =>
    exact pend_liftP.2 (pend_callEv hfi hty)
  | ind hres hfi hty hy =>
    refine pend_liftP (x := indEvT _ _ f stk).2 ?_
    rw [indEvT, run_getState_bind, resolveInd_eq hres]
    exact pend_callAtT hfi hty hy
  | ref hstk hfi hty hy =>
    subst hstk
    exact pend_liftP (x := refEvT _ f _).2 (pend_callAtT hfi hty hy)

theorem pend_callAtT_inv {y : TypeIdx} {fa : Nat} {f : Frame} {stk : List Val} {s : Store H}
    {cs : List (Call (CallSig H))} {m : (CallSig H).Op}
    (h : Pend (run' (callAtT y fa f stk) ⟨s⟩) cs m) :
    ∃ fi ps rs, s.funcs[fa]? = some fi ∧ Validation.DefType.funcType? fi.type = some (ps, rs) ∧
      typeArity f.module y = some (ps.length, rs.length) ∧
      cs = [] ∧ m = (fa, (stk.take ps.length).reverse, s) := by
  rw [callAtT, run_getState_bind] at h
  by_cases ht : calleeTyped s f y fa
  · simp only [ht, ↓reduceIte] at h
    obtain ⟨fi, ps, rs, hfi, hty, rfl, rfl⟩ :=
      Silmaril.Proofs.Wasm.Abstract.XDecomp.pend_callAt_inv h
    exact ⟨fi, ps, rs, hfi, hty, ht fi ps rs hfi hty, rfl, rfl⟩
  · simp only [ht, ↓reduceIte] at h
    exact absurd h not_pendR_stuck

/-- The only pending call of an operator is its own call event. -/
theorem pend_opCXP_inv {s : Store H} {f : Frame} {stk : List Val} {i : Instr}
    {cs : List (Call (CallSig H))} {m : (CallSig H).Op}
    (h : Pend (run' (opCXP i f stk : M (CallSig H) H ResP) ⟨s⟩) cs m) :
    cs = [] ∧ HeadEv s f stk i m := by
  cases hi : callEvInstr i with
  | false => exact absurd h (quiet_opCXP hi f stk s).not_pend
  | true =>
    obtain ⟨x, rfl⟩ | ⟨x, y, rfl⟩ | ⟨y, rfl⟩ :
        (∃ x, i = .call x) ∨ (∃ x y, i = .callIndirect x y) ∨ (∃ y, i = .callRef y) := by
      cases i <;> simp_all [callEvInstr]
    · have h' := pend_liftP (x := callEv x f stk).1 h
      obtain ⟨a, fi, ps, rs, hfi, hty, rfl, rfl⟩ := pend_callEv_inv h'
      exact ⟨rfl, .call hfi hty⟩
    · have h' := pend_liftP (x := indEvT x y f stk).1 h
      rw [indEvT, run_getState_bind] at h'
      cases hr : resolveInd s f x y stk with
      | none => simp only [hr] at h'; exact absurd h' not_pendR_stuck
      | some p =>
        obtain ⟨o, stk'⟩ := p
        have hs := resolveInd_spec hr
        cases o with
        | some fa =>
          simp only [hr] at h'
          obtain ⟨fi, ps, rs, hfi, hty, hy, rfl, rfl⟩ := pend_callAtT_inv h'
          exact ⟨rfl, .ind hs hfi hty hy⟩
        | none =>
          simp only [hr] at h'
          rw [run_trapS] at h'
          exact absurd h' not_pend_ret
    · have h' := pend_liftP (x := refEvT y f stk).1 h
      unfold refEvT at h'
      split at h'
      · obtain ⟨fi, ps, rs, hfi, hty, hy, rfl, rfl⟩ := pend_callAtT_inv h'
        exact ⟨rfl, .ref rfl hfi hty hy⟩
      · rw [run_trapS] at h'; exact absurd h' not_pend_ret
      · exact absurd h' not_pendR_stuck

/-! ## Forward -/

section
variable {C : CallRel H}

/-- **Logged pending observations are pending calls** of the exposed body, after the log. -/
theorem reachXP_pend {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {cs : List (Call (CallSig H))} {y : Nat × List Val × Store H}
    (h : ReachXP C s f stk es cs y) :
    Answered C cs ∧ Pend (run' (denListXP es f stk : M (CallSig H) H ResP) ⟨s⟩) cs y := by
  induction h with
  | head _ ih =>
    obtain ⟨hA, hp⟩ := ih
    rw [run_denListXP_single] at hp
    exact ⟨hA, by rw [denListXP_cons]; exact pendR_bind_left hp⟩
  | cons h₁ _ ih =>
    obtain ⟨hA₁, hp₁⟩ := evalLXP_path h₁
    obtain ⟨hA₂, hp₂⟩ := ih
    rw [run_denListXP_single] at hp₁
    exact ⟨answered_append hA₁ hA₂, by rw [denListXP_cons]; exact pendR_bind_ok hp₁ hp₂⟩
  | args _ ih =>
    obtain ⟨hA, hp⟩ := ih
    refine ⟨hA, ?_⟩
    rw [run_denListXP_single, denXP_op]
    exact pendR_bind_left hp
  | @call s s₁ f f₁ stk stk₁ i args cs y h hy =>
    obtain ⟨hA, hp⟩ := evalLXP_path h
    refine ⟨hA, ?_⟩
    rw [run_denListXP_single, denXP_op]
    simpa using pendR_bind_ok (k := thenKP (opCXP i)) hp (headEv_pend hy)
  | block har _ ih =>
    obtain ⟨hA, hp⟩ := ih
    refine ⟨hA, ?_⟩
    rw [run_denListXP_single, denXP_block]
    simp only [har]
    exact pendR_bind_left hp
  | @loop s f stk bt body np nr cs y har _ ih =>
    obtain ⟨hA, hp⟩ := ih
    refine ⟨hA, ?_⟩
    rw [run_denListXP_single, denXP_loop_unfold]
    refine pendR_bind_left ?_
    simp only [loopBodyXP, har]
    exact pendR_bind_left hp
  | @loopBack s s₁ f f₁ stk vs bt body np nr cs₁ cs₂ y har h _ ih =>
    obtain ⟨hA₁, hp₁⟩ := evalLXP_path h
    obtain ⟨hA₂, hp₂⟩ := ih
    refine ⟨answered_append hA₁ hA₂, ?_⟩
    rw [run_denListXP_single] at hp₂ ⊢
    rw [denXP_loop_unfold]
    have h1 : Path (run' (loopBodyXP bt body ⟨(f, stk)⟩) ⟨s⟩) cs₁
        (.val (.ok (.inr ⟨(f₁, vs.take np ++ stk.drop np)⟩, ⟨s₁⟩))) := by
      simp only [loopBodyXP, har]; exact path_bind_pure hp₁ rfl
    exact pendR_bind_ok h1 hp₂
  | cond _ ih =>
    obtain ⟨hA, hp⟩ := ih
    refine ⟨hA, ?_⟩
    rw [run_denListXP_single, denXP_if]
    exact pendR_bind_left hp
  | @arm s s₁ f f₁ stk stk₁ cv b bt c t el np nr cs₁ cs₂ y h hb har _ ih =>
    obtain ⟨hA₁, hp₁⟩ := evalLXP_path h
    obtain ⟨hA₂, hp₂⟩ := ih
    refine ⟨answered_append hA₁ hA₂, ?_⟩
    rw [run_denListXP_single, denXP_if]
    refine pendR_bind_ok hp₁ ?_
    simp only [hb, har]
    refine pendR_bind_left ?_
    cases b <;> exact hp₂
  | tryT har _ ih =>
    obtain ⟨hA, hp⟩ := ih
    refine ⟨hA, ?_⟩
    rw [run_denListXP_single, denXP_try]
    simp only [har]
    exact pendR_bind_left hp

/-! ## Converse -/

/-- Pending calls of `es` after answered events are logged pending observations. -/
def PReL (C : CallRel H) (es : List BExpr) : Prop :=
  ∀ (s : Store H) (f : Frame) (stk : List Val) (cs : List (Call (CallSig H))) (m : (CallSig H).Op),
    Answered C cs → Pend (run' (denListXP es f stk : M (CallSig H) H ResP) ⟨s⟩) cs m →
    ReachXP C s f stk es cs m

/-- The same for a tree. -/
def TReL (C : CallRel H) (t : BExpr) : Prop :=
  ∀ (s : Store H) (f : Frame) (stk : List Val) (cs : List (Call (CallSig H))) (m : (CallSig H).Op),
    Answered C cs → Pend (run' (denXP t f stk : M (CallSig H) H ResP) ⟨s⟩) cs m →
    ReachXP C s f stk [t] cs m

theorem not_pend_blockKP {np nr : Nat} {stk : List Val} {a : ResP} {s : St H}
    {cs : List (Call (CallSig H))} {m : (CallSig H).Op} :
    ¬ Pend (run' (blockKP np nr stk a : M (CallSig H) H ResP) s) cs m := by
  obtain ⟨⟨f, o⟩⟩ := a
  rw [blockKP_eq]
  exact not_pendR_pure

theorem not_pend_tryKP {np nr : Nat} {stk : List Val} {cls : List Catch} {a : ResP} {s : St H}
    {cs : List (Call (CallSig H))} {m : (CallSig H).Op} :
    ¬ Pend (run' (tryKP np nr stk cls a : M (CallSig H) H ResP) s) cs m := by
  obtain ⟨⟨f, o⟩⟩ := a
  obtain ⟨s⟩ := s
  by_cases hth : ∃ a, o = .flow (.throw a)
  · obtain ⟨a, rfl⟩ := hth
    rw [run_tryKP_throw]
    split
    · exact not_pendR_pure
    · exact not_pendR_pure
    · exact not_pendR_stuck
  · have hnt' : o.NotThrow := by
      rcases o with fl | _
      · cases fl <;> first | trivial | exact hth ⟨_, rfl⟩
      · trivial
    rw [tryKP_ne hnt']
    exact not_pend_blockKP

theorem op_reachL {i : Instr} {args : List BExpr} (hargs : PReL C args) :
    TReL C (.op i args) := by
  intro s f stk cs m hA h
  rw [denXP_op] at h
  rcases pendR_bind_inv h with h₁ | ⟨c₁, c₂, a, t, rfl, h₁, h₂⟩
  · exact .args (hargs s f stk cs m hA h₁)
  · obtain ⟨⟨s₀, f₀, o⟩, hev, hend⟩ :=
      list_ansL args s f stk c₁ _ (answered_left hA) h₁ (by simp)
    obtain ⟨-, rfl, rfl⟩ := endRP_ok_inv hend
    by_cases hn : o.IsNormal
    · obtain ⟨stk₁, rfl⟩ := POut.normal_eq hn
      obtain ⟨rfl, hy⟩ := pend_opCXP_inv h₂
      rw [List.append_nil]
      exact .call hev hy
    · rw [thenKP_pass_eq hn] at h₂
      exact absurd h₂ not_pendR_pure

theorem block_reachL {bt : BlockType} {body : List BExpr} (hbody : PReL C body) :
    TReL C (.block bt body) := by
  intro s f stk cs m hA h
  rw [denXP_block] at h
  cases har : arity f bt with
  | none => simp only [har] at h; exact absurd h not_pendR_stuck
  | some p =>
    obtain ⟨np, nr⟩ := p
    simp only [har] at h
    rcases pendR_bind_inv h with h₁ | ⟨_, _, _, _, _, _, h₂⟩
    · exact .block har (hbody s f _ cs m hA h₁)
    · exact absurd h₂ not_pend_blockKP

theorem try_reachL {bt : BlockType} {cls : List Catch} {body : List BExpr}
    (hbody : PReL C body) : TReL C (.tryTable bt cls body) := by
  intro s f stk cs m hA h
  rw [denXP_try] at h
  cases har : arity f bt with
  | none => simp only [har] at h; exact absurd h not_pendR_stuck
  | some p =>
    obtain ⟨np, nr⟩ := p
    simp only [har] at h
    rcases pendR_bind_inv h with h₁ | ⟨_, _, _, _, _, _, h₂⟩
    · exact .tryT har (hbody s f _ cs m hA h₁)
    · exact absurd h₂ not_pend_tryKP

theorem if_reachL {bt : BlockType} {c t el : List BExpr} (hc : PReL C c) (ht : PReL C t)
    (hel : PReL C el) : TReL C (.if_ bt c t el) := by
  intro s f stk cs m hA h
  rw [denXP_if] at h
  rcases pendR_bind_inv h with h₁ | ⟨c₁, c₂, a, t', rfl, h₁, h₂⟩
  · exact .cond (hc s f stk cs m hA h₁)
  · obtain ⟨⟨s₁, f₁, o⟩, hev, hend⟩ := list_ansL c s f stk c₁ _ (answered_left hA) h₁ (by simp)
    obtain ⟨-, rfl, rfl⟩ := endRP_ok_inv hend
    by_cases hn : o.IsNormal
    · obtain ⟨stk₁, rfl⟩ := POut.normal_eq hn
      rcases stk₁ with _ | ⟨cv, stk₁⟩
      · exact absurd h₂ not_pendR_stuck
      cases hb : truthy cv with
      | none => simp only [hb] at h₂; exact absurd h₂ not_pendR_stuck
      | some b =>
        cases har : arity f₁ bt with
        | none => simp only [hb, har] at h₂; exact absurd h₂ not_pendR_stuck
        | some p =>
          obtain ⟨np, nr⟩ := p
          simp only [hb, har] at h₂
          rcases pendR_bind_inv h₂ with h₃ | ⟨_, _, _, _, _, _, h₃⟩
          · refine .arm hev hb har ?_
            cases b
            · exact hel _ _ _ _ m (answered_right hA) h₃
            · exact ht _ _ _ _ m (answered_right hA) h₃
          · exact absurd h₃ not_pend_blockKP
    · have h₂' : Pend (run' (pure ⟨(f₁, o)⟩ : M (CallSig H) H ResP) ⟨s₁⟩) c₂ m := by
        rcases o with fl | _
        · cases fl <;> first | exact absurd trivial hn | exact h₂
        · exact h₂
      exact absurd h₂' not_pendR_pure

theorem loop_reachL {bt : BlockType} {body : List BExpr} (hbody : PReL C body) :
    TReL C (.loop bt body) := by
  intro s f stk cs m hA h
  let G := loopTree (loopBodyXP (H := H) bt body)
  have kin : ∀ (p : ULift.{1} (Frame × List Val) × St H) cs m, IterPend G p cs m →
      Answered C cs → ReachXP C p.2.down p.1.down.1 p.1.down.2 [.loop bt body] cs m := by
    intro p cs m hp
    induction hp with
    | @inside p cs m hp =>
      intro hA
      rcases pend_bind_inv hp with h₁ | ⟨_, _, _, _, _, h₂⟩
      · obtain ⟨⟨f, stk⟩, ⟨s⟩⟩ := p
        have h₁' : Pend (run' (loopBodyXP bt body ⟨(f, stk)⟩ : M (CallSig H) H _) ⟨s⟩) cs m := h₁
        simp only [loopBodyXP] at h₁'
        cases har : arity f bt with
        | none => simp only [har] at h₁'; exact absurd h₁' not_pendR_stuck
        | some q =>
          obtain ⟨np, nr⟩ := q
          simp only [har] at h₁'
          rcases pendR_bind_inv h₁' with h₂ | ⟨_, _, a, _, _, _, h₃⟩
          · exact .loop har (hbody s f _ cs m hA h₂)
          · obtain ⟨⟨f', fl'⟩⟩ := a
            rw [loopKP_eq] at h₃
            exact absurd h₃ not_pendR_pure
      · exact absurd h₂ not_pend_ret
    | @step p cs₁ p' cs₂ m hp _ ih =>
      intro hA
      obtain ⟨r', hp', hm⟩ := path_map_inv hp
      have hr'' := loopEnd_inr hm.symm
      obtain ⟨np, nr, s₁, f₁, o, har, hev, ⟨-, hr'⟩ | ⟨hnt, hr'⟩⟩ :=
        loopIter_ansL (list_ansL body) (answered_left hA) hp' (by rw [hr'']; simp)
      · rw [hr''] at hr'; cases hr'
      · rw [hr''] at hr'
        simp only [PathEnd.val.injEq, Except.ok.injEq, Prod.mk.injEq] at hr'
        obtain ⟨hlo, hs⟩ := hr'
        obtain ⟨vs, rfl, hc⟩ := loopOutP_inr hlo.symm
        have := ih (answered_right hA)
        rw [hc, hs] at this
        exact .loopBack har hev this
  rw [denXP_loop] at h
  change Pend ((((Silmaril.Elgot.iter (loopBodyXP bt body) ⟨(f, stk)⟩ :
    M (CallSig H) H _).run ⟨s⟩).run)) cs m at h
  rw [Silmaril.Wasm.Abstract.BodyTrace.run_iter] at h
  exact kin _ cs m (pend_iterPend h) hA

theorem cons_reachL {e : BExpr} {es : List BExpr} (he : TReL C e) (hes : PReL C es) :
    PReL C (e :: es) := by
  intro s f stk cs m hA h
  rw [denListXP_cons] at h
  rcases pendR_bind_inv h with h₁ | ⟨c₁, c₂, a, t, rfl, h₁, h₂⟩
  · exact .head (he s f stk cs m hA h₁)
  · obtain ⟨⟨s₀, f₀, o⟩, hev, hend⟩ := tree_ansL e s f stk c₁ _ (answered_left hA) h₁ (by simp)
    obtain ⟨-, rfl, rfl⟩ := endRP_ok_inv hend
    by_cases hn : o.IsNormal
    · obtain ⟨stk₁, rfl⟩ := POut.normal_eq hn
      exact .cons hev (hes s₀ f₀ stk₁ c₂ m (answered_right hA) h₂)
    · rw [thenKP_pass_eq hn] at h₂
      exact absurd h₂ not_pendR_pure

mutual

theorem tree_reachL : ∀ (t : BExpr), TReL C t
  | .op _ args => op_reachL (list_reachL args)
  | .block _ body => block_reachL (list_reachL body)
  | .loop _ body => loop_reachL (list_reachL body)
  | .if_ _ c t el => if_reachL (list_reachL c) (list_reachL t) (list_reachL el)
  | .tryTable _ _ body => try_reachL (list_reachL body)

theorem list_reachL : ∀ (es : List BExpr), PReL C es
  | [] => fun _ _ _ _ _ _ h => absurd h not_pendR_pure
  | e :: es => cons_reachL (tree_reachL e) (list_reachL es)

end

/-! ## The frame -/

theorem frameOut_path {n : Nat} {ans : Store H × Flow} {out : Store H × Flow}
    (hr : frameOut n ans = some out) (s : St H) :
    Path (run' (frameAns n ans) s) [] (endF out) := by
  obtain ⟨s₂, fl⟩ := ans
  cases fl with
  | trap => cases hr; exact .ret (run_trapS s)
  | throw t => cases hr; exact .ret (run_set_pure _ _ _)
  | normal ws => cases hr; exact .ret (run_set_pure _ _ _)
  | ret ws => cases hr; exact .ret (run_set_pure _ _ _)
  | brk k ws =>
    cases k with
    | zero => cases hr; exact .ret (run_set_pure _ _ _)
    | succ k => simp [frameOut, Flow.retVals] at hr

theorem frameOut_of {n : Nat} {ans : Store H × Flow}
    (hfl : (∃ vs, ans.2.retVals = some vs) ∨ ans.2.Abrupt) :
    frameOut n ans = some (ans.1, tailFlow n ans.2) := by
  obtain ⟨s₂, fl⟩ := ans
  cases fl with
  | brk k ws =>
    cases k with
    | zero => rfl
    | succ k => simp [Flow.retVals, Flow.Abrupt] at hfl
  | _ => rfl

theorem not_pend_frameAns {n : Nat} {ans : Store H × Flow} {s : St H}
    {cs : List (Call (CallSig H))} {m : (CallSig H).Op} :
    ¬ Pend (run' (frameAns n ans) s) cs m := by
  obtain ⟨s₂, fl⟩ := ans
  intro h
  cases fl with
  | trap => rw [show run' (frameAns n (s₂, .trap)) s = _ from run_trapS s] at h; exact not_pend_ret h
  | throw t => rw [show run' (frameAns n (s₂, .throw t)) s = _ from run_set_pure _ _ _] at h; exact not_pend_ret h
  | normal ws => rw [show run' (frameAns n (s₂, .normal ws)) s = _ from run_set_pure _ _ _] at h; exact not_pend_ret h
  | ret ws => rw [show run' (frameAns n (s₂, .ret ws)) s = _ from run_set_pure _ _ _] at h; exact not_pend_ret h
  | brk k ws =>
    cases k with
    | zero => rw [show run' (frameAns n (s₂, .brk 0 ws)) s = _ from run_set_pure _ _ _] at h; exact not_pend_ret h
    | succ k => exact not_pend_diverge h

theorem run_frameXP {s : Store H} {a : Nat} {args : List Val} {fi : FuncInst H} {fn : Func}
    {ps rs : List Validation.CValType} (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) :
    run' (frameXP a args : M (CallSig H) H (ULift.{1} Flow)) ⟨s⟩ =
      run' (denListXP (liftInstrs fn.body) (Frame.forCall fi.module args fn.locals) [] >>=
        frameK) ⟨s⟩ := by
  rw [frameXP, run_getState_bind]
  simp only [hfi, hcode, hty]

/-- **A logged frame is a path of the exposed frame** with exactly its log. -/
theorem frameLXP_path {s : Store H} {a : Nat} {args : List Val} {cs : List (Call (CallSig H))}
    {out : Store H × Flow} (h : FrameLXP C s a args cs out) :
    Answered C cs ∧
      Path (run' (frameXP a args : M (CallSig H) H (ULift.{1} Flow)) ⟨s⟩) cs (endF out) := by
  obtain ⟨fi, fn, ps, rs, s₁, f₂, o, cs₁, cs₂, hfi, hcode, hty, hev, hk, rfl⟩ := h
  obtain ⟨hA, hp⟩ := evalLXP_path hev
  rw [run_frameXP hfi hcode hty]
  cases hk with
  | @flow fl =>
    rw [List.append_nil]
    cases fl
    case trap => exact ⟨hA, path_bind_err hp⟩
    all_goals exact ⟨hA, path_bind_pure hp rfl⟩
  | @tail fa n args' ans out hC hr =>
    refine ⟨answered_append hA (answered_single hC), ?_⟩
    refine path_bind_ok hp ?_
    rw [run_frameK_tail]
    exact .vis rfl (frameOut_path hr _)

/-- **The converse.** -/
theorem path_frameLXP {s : Store H} {a : Nat} {args : List Val}
    {cs : List (Call (CallSig H))} {e : PathEnd (Except PUnit.{2} (ULift.{1} Flow × St H))}
    (hA : Answered C cs)
    (h : Path (run' (frameXP a args : M (CallSig H) H (ULift.{1} Flow)) ⟨s⟩) cs e)
    (he : e ≠ .div) : ∃ out, FrameLXP C s a args cs out ∧ endF out = e := by
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
            list_ansL _ s _ [] c₁ _ (answered_left hA) h₁ (by simp)
          obtain ⟨hnt, rfl, rfl⟩ := endRP_ok_inv hend
          cases o with
          | flow fl =>
            have h₂' : Path (run' (pure ⟨fl⟩ : M (CallSig H) H (ULift.{1} Flow)) ⟨s₁'⟩) c₂ e :=
              h₂
            obtain ⟨rfl, rfl⟩ := path_pure_inv h₂'
            exact ⟨(s₁', fl), ⟨fi, fn, ps, rs, s₁', f₂, .flow fl, c₁, [], hfi, hc, hty, hev,
              .flow, rfl⟩, endF_ok (fun h => hnt (congrArg POut.flow h))⟩
          | tail fa args' n =>
            rw [run_frameK_tail] at h₂
            obtain ⟨ans, cs', rfl, hp⟩ := Silmaril.Wasm.Abstract.BodyTrace.path_vis_inv h₂
            obtain ⟨rfl, hfl, rfl⟩ := path_frameAns_inv hp he
            have hC : C s₁' fa args' ans := (answered_right hA) _ (List.mem_cons_self ..)
            exact ⟨_, ⟨fi, fn, ps, rs, s₁', f₂, _, c₁, _, hfi, hc, hty, hev,
              .tail hC (frameOut_of hfl), rfl⟩, rfl⟩
        · obtain ⟨⟨s₁', f₂, o⟩, hev, hend⟩ := list_ansL _ s _ [] cs _ hA h₁ (by simp)
          obtain rfl := endRP_err_inv hend
          exact ⟨(s₁', .trap), ⟨fi, fn, ps, rs, s₁', f₂, _, cs, [], hfi, hc, hty, hev, .flow,
            (List.append_nil _).symm⟩, rfl⟩

theorem frameReachXP_pend {s : Store H} {a : Nat} {args : List Val}
    {cs : List (Call (CallSig H))} {y : Nat × List Val × Store H}
    (h : FrameReachXP C s a args cs y) :
    Answered C cs ∧
      Pend (run' (frameXP a args : M (CallSig H) H (ULift.{1} Flow)) ⟨s⟩) cs y := by
  obtain ⟨fi, fn, ps, rs, hfi, hcode, hty, hr | ⟨s₁, f₂, fa, n, args', hev, rfl⟩⟩ := h
  · obtain ⟨hA, hp⟩ := reachXP_pend hr
    rw [run_frameXP hfi hcode hty]
    exact ⟨hA, pendR_bind_left hp⟩
  · obtain ⟨hA, hp⟩ := evalLXP_path hev
    rw [run_frameXP hfi hcode hty]
    refine ⟨hA, ?_⟩
    have := pendR_bind_ok (k := frameK) (cs₂ := []) (m := (fa, args', s₁)) hp
      (by rw [run_frameK_tail]; exact .here rfl)
    simpa using this

theorem pend_frameReachXP {s : Store H} {a : Nat} {args : List Val}
    {cs : List (Call (CallSig H))} {m : (CallSig H).Op} (hA : Answered C cs)
    (h : Pend (run' (frameXP a args : M (CallSig H) H (ULift.{1} Flow)) ⟨s⟩) cs m) :
    FrameReachXP C s a args cs m := by
  rw [frameXP, run_getState_bind] at h
  cases hfi : s.funcs[a]? with
  | none => simp only [hfi] at h; exact absurd h not_pendR_stuck
  | some fi =>
    simp only [hfi] at h
    cases hc : fi.code with
    | host hh => simp only [hc] at h; exact absurd h not_pendR_stuck
    | wasm fn =>
      cases hty : Validation.DefType.funcType? fi.type with
      | none => simp only [hc, hty] at h; exact absurd h not_pendR_stuck
      | some q =>
        obtain ⟨ps, rs⟩ := q
        simp only [hc, hty] at h
        refine ⟨fi, fn, ps, rs, hfi, hc, hty, ?_⟩
        rcases pendR_bind_inv h with h₁ | ⟨c₁, c₂, r, s₁, rfl, h₁, h₂⟩
        · exact .inl (list_reachL _ s _ [] cs m hA h₁)
        · obtain ⟨⟨s₁', f₂, o⟩, hev, hend⟩ :=
            list_ansL _ s _ [] c₁ _ (answered_left hA) h₁ (by simp)
          obtain ⟨-, rfl, rfl⟩ := endRP_ok_inv hend
          cases o with
          | flow fl =>
            have h₂' : Pend (run' (pure ⟨fl⟩ : M (CallSig H) H (ULift.{1} Flow)) ⟨s₁'⟩) c₂ m :=
              h₂
            exact absurd h₂' not_pendR_pure
          | tail fa args' n =>
            rw [run_frameK_tail] at h₂
            rcases pend_vis_inv h₂ with ⟨rfl, rfl⟩ | ⟨_, _, _, hp⟩
            · rw [List.append_nil]
              exact .inr ⟨s₁', f₂, fa, n, args', hev, rfl⟩
            · exact absurd hp not_pend_frameAns

end

end Silmaril.Proofs.Wasm.Abstract.FunctorP

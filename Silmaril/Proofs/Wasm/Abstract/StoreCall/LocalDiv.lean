module

public import Silmaril.Proofs.Wasm.Abstract.StoreCall.Descent
public import Silmaril.Proofs.Wasm.Abstract.BodyTrace.Inf
public import Silmaril.Proofs.Wasm.Abstract.StoreBody.Invoke

/-!
Proofs for `Silmaril.Wasm.Abstract.StoreCall.Thms`: local divergence. An
infinite run of the exposed body whose call events are all answered by
`closedCall` (infinitely many *returning* internal calls) is local divergence
`Interp.LocalDiv` of the problem (`localDiv_of_prod`), by coinduction on
`LocalDiv`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.StoreCall

open Silmaril.Wasm Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Abstract
  Silmaril.Wasm.Abstract.Body Silmaril.Wasm.Abstract.BodyTrace Silmaril.Wasm.Binaryen
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract.StoreBody Silmaril.Wasm.Abstract.StoreCall
  Silmaril.Elgot.ITree Silmaril.Proofs.Wasm.Abstract.StoreBody Silmaril.Proofs.Wasm.Abstract.BodyTrace

variable {H : Type}

/-- Every call event of the stream is answered by `closedCall`. -/
def AnsS (ω : Stream' (Call (CallSig H))) : Prop :=
  ∀ n, closedCall (ω n).1.2.2 (ω n).1.1 (ω n).1.2.1 (ω n).2

theorem ansS_append : ∀ {cs : List (Call (CallSig H))} {ω : Stream' (Call (CallSig H))},
    AnsS (cs ++ₛ ω) → Answered closedCall cs ∧ AnsS ω
  | [], _, h => ⟨answered_nil, h⟩
  | c :: cs, ω, h => by
    have ht : AnsS (cs ++ₛ ω) := fun n => h (n + 1)
    obtain ⟨h1, h2⟩ := ansS_append ht
    refine ⟨fun c' hc' => ?_, h2⟩
    rcases List.mem_cons.1 hc' with rfl | hc'
    · exact h 0
    · exact h1 c' hc'

theorem infPath_vis_inv {R : Type} {e : SigEv (CallSig H) R}
    {k : R → Tree (SigEv (CallSig H)) (Except PUnit.{2} (Res × St H))}
    {ω : Stream' (Call (CallSig H))} (h : InfPath (vis e k) ω) :
    ∃ r, ω 0 = ⟨e.1, cast e.2.symm r⟩ ∧ InfPath (k r) (fun n => ω (n + 1)) := by
  obtain ⟨τ, h0, hτ⟩ := h
  obtain ⟨R', e', k', r, h1, h2, h3⟩ := hτ 0
  rw [h0] at h1
  obtain ⟨rfl, he, hk⟩ := vis_heq h1
  obtain rfl := eq_of_heq he
  obtain rfl := eq_of_heq hk
  exact ⟨r, h2, ⟨fun n => τ (n + 1), h3, fun n => hτ (n + 1)⟩⟩

section
variable {E : Sig.{0}}

theorem infR_bind_inv {X Y : Type 1} {x : M E H X} {k : X → M E H Y} {s : St H}
    {ω : Stream' (Call E)} (h : InfPath (run' (x >>= k) s) ω) :
    InfPath (run' x s) ω ∨ ∃ cs a s₁ ω', Path (run' x s) cs (.val (.ok (a, s₁))) ∧
      InfPath (run' (k a) s₁) ω' ∧ ω = cs ++ₛ ω' := by
  rw [StoreBody.run_bind] at h
  rcases Silmaril.Wasm.Abstract.BodyTrace.infPath_bind_iff.1 h with h₁ | ⟨cs, v, ω', h₁, h₂, rfl⟩
  · exact .inl h₁
  · rcases v with e | ⟨a, s₁⟩
    · exact absurd h₂ not_infPath_ret
    · exact .inr ⟨cs, a, s₁, ω', h₁, h₂, rfl⟩

theorem infR_bind_left {X Y : Type 1} {x : M E H X} {k : X → M E H Y} {s : St H}
    {ω : Stream' (Call E)} (h : InfPath (run' x s) ω) : InfPath (run' (x >>= k) s) ω := by
  rw [StoreBody.run_bind]; exact Silmaril.Wasm.Abstract.BodyTrace.infPath_bind_iff.2 (.inl h)

theorem infR_bind_ok {X Y : Type 1} {x : M E H X} {k : X → M E H Y} {s : St H}
    {cs : List (Call E)} {a : X} {s₁ : St H} {ω' : Stream' (Call E)}
    (h₁ : Path (run' x s) cs (.val (.ok (a, s₁)))) (h₂ : InfPath (run' (k a) s₁) ω') :
    InfPath (run' (x >>= k) s) (cs ++ₛ ω') := by
  rw [StoreBody.run_bind]; exact Silmaril.Wasm.Abstract.BodyTrace.infPath_bind_iff.2 (.inr ⟨cs, _, ω', h₁, h₂, rfl⟩)

theorem not_infR_pure {X : Type 1} {a : X} {s : St H} {ω : Stream' (Call E)} :
    ¬ InfPath (run' (pure a : M E H X) s) ω := not_infPath_ret

theorem not_infR_stuck {X : Type 1} {s : St H} {ω : Stream' (Call E)} :
    ¬ InfPath (run' (stuck : M E H X) s) ω := not_infPath_diverge

theorem not_infR_flatK {i : Instr} {f : Frame} {stk : List Val} {s : Store H}
    {ω : Stream' (Call E)} : ¬ InfPath (run' (flatK i f stk : M E H Res) ⟨s⟩) ω := by
  rw [show run' (flatK i f stk : M E H Res) ⟨s⟩ = evalTree (evalFlat s f stk i) from
    run_flatK i f stk s]
  rcases evalFlat s f stk i with _ | ⟨s', f', fl⟩
  · exact not_infPath_diverge
  · cases fl <;> exact not_infPath_ret

end

theorem not_infR_callAns {f : Frame} {stk : List Val} {ps rs : List Validation.CValType}
    {ans : Store H × Flow} {s : St H} {ω : Stream' (Call (CallSig H))} :
    ¬ InfPath (run' (callAns f stk ps rs ans) s) ω := by
  obtain ⟨s₂, fl⟩ := ans
  intro h
  cases fl with
  | trap => rw [show run' (callAns f stk ps rs (s₂, .trap)) s = _ from run_trapS s] at h; exact not_infPath_ret h
  | throw t => rw [show run' (callAns f stk ps rs (s₂, .throw t)) s = _ from run_set_pure _ _ _] at h; exact not_infPath_ret h
  | normal ws => rw [show run' (callAns f stk ps rs (s₂, .normal ws)) s = _ from run_set_pure _ _ _] at h; exact not_infPath_ret h
  | ret ws => rw [show run' (callAns f stk ps rs (s₂, .ret ws)) s = _ from run_set_pure _ _ _] at h; exact not_infPath_ret h
  | brk k ws =>
    cases k with
    | zero => rw [show run' (callAns f stk ps rs (s₂, .brk 0 ws)) s = _ from run_set_pure _ _ _] at h; exact not_infPath_ret h
    | succ k => exact not_infPath_diverge h

theorem not_infR_callEv {x : FuncIdx} {f : Frame} {stk : List Val} {s : Store H}
    {ω : Stream' (Call (CallSig H))} :
    ¬ InfPath (run' (callEv x f stk : M (CallSig H) H Res) ⟨s⟩) ω := by
  intro h
  by_cases hex : ∃ a fi ps rs, s.func? f x = some (a, fi) ∧
      Validation.DefType.funcType? fi.type = some (ps, rs)
  · obtain ⟨a, fi, ps, rs, hfi, hty⟩ := hex
    rw [run_callEv_vis hfi hty] at h
    obtain ⟨r, -, h'⟩ := infPath_vis_inv h
    exact not_infR_callAns h'
  · rw [run_callEv_none (fun a fi ps rs h1 h2 => hex ⟨a, fi, ps, rs, h1, h2⟩)] at h
    exact not_infPath_diverge h

theorem ansS_of_append : ∀ {cs : List (Call (CallSig H))} {ω : Stream' (Call (CallSig H))},
    Answered closedCall cs → AnsS ω → AnsS (cs ++ₛ ω)
  | [], _, _, h => h
  | c :: cs, ω, hc, h => by
    intro n
    cases n with
    | zero => exact hc c (List.mem_cons_self ..)
    | succ n => exact ansS_of_append (cs := cs) (fun c' h' => hc c' (List.mem_cons_of_mem _ h')) h n

/-! ## Productive local divergence -/

/-- The exposed body of the problem has an infinite run answered by `closedCall`. -/
def ProdE (s : Store H) (f : Frame) (stk : List Val) (es : List BExpr) : Prop :=
  ∃ ω, AnsS ω ∧ InfPath (run' (denListC callEv es f stk : M (CallSig H) H Res) ⟨s⟩) ω

theorem cont_inf {es : List BExpr} {x : M (CallSig H) H Res} {s : St H}
    {ω : Stream' (Call (CallSig H))} {Q : Store H × Frame × Flow → Prop} (hA : AnsS ω)
    (h : InfPath (run' (x >>= thenK (denListC callEv es)) s) ω)
    (hx : ∀ cs₁ v, Answered closedCall cs₁ → Path (run' x s) cs₁ (.val v) →
      ∃ r₀, Q r₀ ∧ endR r₀ = .val v) :
    InfPath (run' x s) ω ∨ ∃ s₁ f₁ stk₁, Q (s₁, f₁, .normal stk₁) ∧ ProdE s₁ f₁ stk₁ es := by
  rcases infR_bind_inv h with h₁ | ⟨cs, a, t, ω', h₁, h₂, rfl⟩
  · exact .inl h₁
  · obtain ⟨hcs, hω'⟩ := ansS_append hA
    obtain ⟨⟨s₁, f₁, fl⟩, hQ, hend⟩ := hx cs _ hcs h₁
    obtain ⟨-, rfl, rfl⟩ := endR_ok_inv hend
    by_cases hn : fl.IsNormal
    · obtain ⟨stk₁, rfl⟩ : ∃ stk₁, fl = .normal stk₁ := by
        cases fl <;> first | exact ⟨_, rfl⟩ | exact absurd hn id
      exact .inr ⟨s₁, f₁, stk₁, hQ, ω', hω', h₂⟩
    · rw [thenK_pass_eq hn] at h₂
      exact absurd h₂ not_infR_pure

theorem op_step {i : Instr} {args es : List BExpr} {s : Store H} {f : Frame} {stk : List Val}
    {ω : Stream' (Call (CallSig H))} (hA : AnsS ω)
    (h : InfPath (run' (denC callEv (.op i args) f stk >>= thenK (denListC callEv es)) ⟨s⟩) ω) :
    Interp.DivStep ProdE ⊥ s f stk (.op i args :: es) := by
  rw [denC_op] at h
  rcases cont_inf hA h (opHead_ans (lans_closed args)) with h₁ | ⟨s₂, f₂, stk₂, hQ, hk⟩
  · rcases infR_bind_inv h₁ with h₂ | ⟨c₁, a, t, ω', h₂, h₃, rfl⟩
    · exact .args ⟨ω, hA, h₂⟩
    · obtain ⟨hc₁, -⟩ := ansS_append hA
      obtain ⟨⟨s₁, f₁, fl⟩, hev, hend⟩ := lans_closed args s f stk c₁ _ hc₁ h₂ (by simp)
      obtain ⟨-, rfl, rfl⟩ := endR_ok_inv hend
      by_cases hn : fl.IsNormal
      · obtain ⟨stk₁, rfl⟩ : ∃ stk₁, fl = .normal stk₁ := by
          cases fl <;> first | exact ⟨_, rfl⟩ | exact absurd hn id
        have h₃' : InfPath (run' (opC callEv i f₁ stk₁ : M (CallSig H) H Res) ⟨s₁⟩) ω' := h₃
        cases hci : callIdx? i with
        | none => simp only [opC, hci] at h₃'; exact absurd h₃' not_infR_flatK
        | some x => simp only [opC, hci] at h₃'; exact absurd h₃' not_infR_callEv
      · rw [thenK_pass_eq hn] at h₃
        exact absurd h₃ not_infR_pure
  · rcases hQ with ⟨hn, -⟩ | ⟨s₁, f₁, stk₁, hev, ⟨hi, hflat⟩ | ⟨x, a, fi, ps, rs, rfl, hfi, hty, hc⟩⟩
    · exact absurd trivial hn
    · exact .opK hi (eval_of_evalO hev) hflat hk
    · rcases hc with ⟨fl, vs, hC, hvs, hr₀⟩ | ⟨-, hr₀⟩ | ⟨t, -, hr₀⟩
      · simp only [Prod.mk.injEq, Flow.normal.injEq] at hr₀
        obtain ⟨-, rfl, rfl⟩ := hr₀
        rw [closedCall_eq] at hC
        obtain ⟨fi', fn, ps', rs', f₃, hfi', hcode, hty', hbody⟩ := hC
        rw [funcs_of_func? hfi] at hfi'
        obtain rfl := Option.some.inj hfi'
        rw [hty] at hty'
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hty')
        exact .callRet (eval_of_evalO hev) hfi hcode hty hbody hvs hk
      · simp at hr₀
      · simp at hr₀

theorem block_step {bt : BlockType} {body es : List BExpr} {s : Store H} {f : Frame}
    {stk : List Val} {ω : Stream' (Call (CallSig H))} (hA : AnsS ω)
    (h : InfPath (run' (denC callEv (.block bt body) f stk >>= thenK (denListC callEv es)) ⟨s⟩) ω) :
    Interp.DivStep ProdE ⊥ s f stk (.block bt body :: es) := by
  rw [denC_block] at h
  cases har : arity f bt with
  | none =>
    simp only [har] at h
    rcases infR_bind_inv h with h₁ | ⟨_, _, _, _, h₁, _, _⟩
    · exact absurd h₁ not_infR_stuck
    · exact absurd (path_stuck_inv h₁) (by simp)
  | some p =>
    obtain ⟨np, nr⟩ := p
    simp only [har] at h
    rcases cont_inf (Q := BlockHead closedCall s f stk bt body) hA h
      (fun cs₁ v hA₁ h₁ => by
        obtain ⟨s₁, f₁, fl, hev, hend⟩ := blockArm_ans (lans_closed body) cs₁ v hA₁ h₁
        exact ⟨_, ⟨np, nr, s₁, f₁, fl, har, hev, rfl⟩, hend⟩) with h₁ |
      ⟨s₂, f₂, stk₂, ⟨np', nr', s₁, f₁, fl, har', hev, hr₀⟩, hk⟩
    · rcases infR_bind_inv h₁ with h₂ | ⟨c₁, a, t, ω', -, h₃, -⟩
      · exact .block har ⟨ω, hA, h₂⟩
      · obtain ⟨⟨f', fl'⟩⟩ := a
        rw [blockK_eq] at h₃
        exact absurd h₃ not_infR_pure
    · rw [har] at har'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj har')
      simp only [Prod.mk.injEq] at hr₀
      obtain ⟨rfl, rfl, hfl⟩ := hr₀
      cases fl with
      | normal vs =>
        simp only [blockFlow, Flow.normal.injEq] at hfl
        subst hfl
        exact .blockK har (eval_of_evalO hev) rfl hk
      | brk k vs =>
        cases k with
        | zero =>
          simp only [blockFlow, Flow.normal.injEq] at hfl
          subst hfl
          exact .blockK har (eval_of_evalO hev) rfl hk
        | succ k => simp [blockFlow] at hfl
      | _ => simp [blockFlow] at hfl

theorem if_step {bt : BlockType} {c t el es : List BExpr} {s : Store H} {f : Frame}
    {stk : List Val} {ω : Stream' (Call (CallSig H))} (hA : AnsS ω)
    (h : InfPath (run' (denC callEv (.if_ bt c t el) f stk >>= thenK (denListC callEv es)) ⟨s⟩) ω) :
    Interp.DivStep ProdE ⊥ s f stk (.if_ bt c t el :: es) := by
  rw [denC_if] at h
  rcases cont_inf (Q := IfHead closedCall s f stk bt c t el) hA h
    (ifHead_ans (lans_closed c) (lans_closed t) (lans_closed el)) with h₁ |
    ⟨s₂, f₂, stk₂, hQ, hk⟩
  · rcases infR_bind_inv h₁ with h₂ | ⟨c₁, a, t', ω', h₂, h₃, rfl⟩
    · exact .cond ⟨ω, hA, h₂⟩
    · obtain ⟨hc₁, hω'⟩ := ansS_append hA
      obtain ⟨⟨s₁, f₁, fl⟩, hev, hend⟩ := lans_closed c s f stk c₁ _ hc₁ h₂ (by simp)
      obtain ⟨-, rfl, rfl⟩ := endR_ok_inv hend
      by_cases hn : fl.IsNormal
      · obtain ⟨stk₁, rfl⟩ : ∃ stk₁, fl = .normal stk₁ := by
          cases fl <;> first | exact ⟨_, rfl⟩ | exact absurd hn id
        rcases stk₁ with _ | ⟨cv, stk₁⟩
        · exact absurd h₃ not_infR_stuck
        cases hb : truthy cv with
        | none => simp only [hb] at h₃; exact absurd h₃ not_infR_stuck
        | some b =>
          cases har : arity f₁ bt with
          | none => simp only [hb, har] at h₃; exact absurd h₃ not_infR_stuck
          | some p =>
            obtain ⟨np, nr⟩ := p
            simp only [hb, har] at h₃
            rcases infR_bind_inv h₃ with h₄ | ⟨_, a', _, _, -, h₄, -⟩
            · refine .arm (eval_of_evalO hev) hb har ⟨ω', hω', ?_⟩
              cases b <;> exact h₄
            · obtain ⟨⟨f', fl'⟩⟩ := a'
              rw [blockK_eq] at h₄
              exact absurd h₄ not_infR_pure
      · have h₃' : InfPath (run' (pure ⟨(f₁, fl)⟩ : M (CallSig H) H Res) ⟨s₁⟩) ω' := by
          cases fl <;> first | exact absurd trivial hn | exact h₃
        exact absurd h₃' not_infR_pure
  · rcases hQ with ⟨hn, -⟩ | ⟨s₁, f₁, cv, stk₁, b, np, nr, s₃, f₃, fl, hev, hb, har, hev₂, hr₀⟩
    · exact absurd trivial hn
    · simp only [Prod.mk.injEq] at hr₀
      obtain ⟨rfl, rfl, hfl⟩ := hr₀
      cases fl with
      | normal vs =>
        simp only [blockFlow, Flow.normal.injEq] at hfl
        subst hfl
        exact .ifK (eval_of_evalO hev) hb har (eval_of_evalO hev₂) rfl hk
      | brk k vs =>
        cases k with
        | zero =>
          simp only [blockFlow, Flow.normal.injEq] at hfl
          subst hfl
          exact .ifK (eval_of_evalO hev) hb har (eval_of_evalO hev₂) rfl hk
        | succ k => simp [blockFlow] at hfl
      | _ => simp [blockFlow] at hfl

theorem loop_step {bt : BlockType} {body es : List BExpr} {s : Store H} {f : Frame}
    {stk : List Val} {ω : Stream' (Call (CallSig H))} (hA : AnsS ω)
    (h : InfPath (run' (denC callEv (.loop bt body) f stk >>= thenK (denListC callEv es)) ⟨s⟩) ω) :
    Interp.DivStep ProdE ⊥ s f stk (.loop bt body :: es) := by
  let G := loopTree (loopBodyC (callEv (H := H)) bt body)
  have hloop : ∀ f stk s, run' (denC callEv (.loop bt body) f stk : M (CallSig H) H Res) ⟨s⟩ =
      iterT G (⟨(f, stk)⟩, ⟨s⟩) := by
    intro f stk s
    rw [denC_loop]
    exact Silmaril.Wasm.Abstract.BodyTrace.run_iter _ _ _
  rcases infR_bind_inv h with h₁ | ⟨cs, a, s₁, ω', h₁, h₂, rfl⟩
  · rw [hloop, iter_unfold] at h₁
    rcases Silmaril.Wasm.Abstract.BodyTrace.infPath_bind_iff.1 h₁ with h₂ | ⟨cs, v, ω', h₂, h₃, rfl⟩
    · -- infinite inside the first iteration
      have h₂' : InfPath (run' (loopBodyC callEv bt body ⟨(f, stk)⟩ : M (CallSig H) H _) ⟨s⟩ >>=
          fun r => pure (loopEnd r)) ω := h₂
      rcases Silmaril.Wasm.Abstract.BodyTrace.infPath_bind_iff.1 h₂' with h₃ | ⟨_, _, _, _, h₄, _⟩
      · simp only [loopBodyC] at h₃
        cases har : arity f bt with
        | none => simp only [har] at h₃; exact absurd h₃ not_infR_stuck
        | some q =>
          obtain ⟨np, nr⟩ := q
          simp only [har] at h₃
          rcases infR_bind_inv h₃ with h₄ | ⟨_, a, _, _, _, h₅, _⟩
          · exact .loop har ⟨ω, hA, h₄⟩
          · obtain ⟨⟨f', fl'⟩⟩ := a
            rw [loopK_eq] at h₅
            exact absurd h₅ not_infR_pure
      · exact absurd h₄ not_infPath_ret
    · -- the first iteration finishes
      obtain ⟨hcs, hω'⟩ := ansS_append hA
      rcases v with y | p'
      · exact absurd h₃ not_infPath_ret
      · obtain ⟨r', hp', hm⟩ := path_map_inv h₂
        have hr'' := loopEnd_inr hm.symm
        obtain ⟨np, nr, s₂, f₂, fl, har, hev, ⟨-, hr'⟩ | ⟨hnt, hr'⟩⟩ :=
          loopIter_ans (lans_closed body) hcs hp' (by rw [hr'']; simp)
        · rw [hr''] at hr'; cases hr'
        · rw [hr''] at hr'
          simp only [PathEnd.val.injEq, Except.ok.injEq, Prod.mk.injEq] at hr'
          obtain ⟨hlo, hs⟩ := hr'
          obtain ⟨vs, rfl, hc⟩ := loopOut_inr hlo.symm
          refine .loopBack har (eval_of_evalO hev) ⟨ω', hω', ?_⟩
          rw [denListC_cons]
          refine infR_bind_left ?_
          have h₃' : InfPath (iterT G p') ω' := h₃
          obtain ⟨⟨⟨f', stk'⟩⟩, ⟨s'⟩⟩ := p'
          simp only [ULift.up.injEq, Prod.mk.injEq] at hc
          obtain ⟨rfl, rfl⟩ := hc
          cases hs
          rw [hloop]
          exact h₃'
  · -- the loop finishes, the continuation runs forever
    obtain ⟨hcs, hω'⟩ := ansS_append hA
    rw [hloop] at h₁
    have hit := path_iter_iff.1 h₁
    cases hit with
    | exit hp =>
      obtain ⟨r', hp', hm⟩ := path_map_inv hp
      rcases loopEnd_inl hm.symm with ⟨e, rfl, he⟩ | ⟨b, s', rfl, hb'⟩
      · cases he
      · obtain ⟨np, nr, s₂, f₂, fl, har, hev, ⟨-, hr'⟩ | ⟨hnt, hr'⟩⟩ :=
          loopIter_ans (lans_closed body) hcs hp' (by simp)
        · cases hr'
        · simp only [Except.ok.injEq, Prod.mk.injEq] at hb'
          obtain ⟨rfl, rfl⟩ := hb'
          simp only [PathEnd.val.injEq, Except.ok.injEq, Prod.mk.injEq] at hr'
          obtain ⟨hlo, hs⟩ := hr'
          cases hs
          rcases loopOut_inl hlo.symm with ⟨vs, rfl, rfl⟩ | ⟨k, vs, rfl, rfl⟩ | ⟨hesc, rfl⟩
          · exact .loopK har (eval_of_evalO hev) ⟨ω', hω', h₂⟩
          · exact absurd (h₂ : InfPath (run' (pure ⟨(f₂, .brk k vs)⟩ : M (CallSig H) H Res) _) ω')
              not_infR_pure
          · rw [thenK_pass_eq (Flow.not_normal_of_escapes hesc)] at h₂
            exact absurd h₂ not_infR_pure
    | step hp hrest =>
      rename_i cs₁ p' cs₂
      obtain ⟨r', hp', hm⟩ := path_map_inv hp
      have hr'' := loopEnd_inr hm.symm
      obtain ⟨np, nr, s₂, f₂, fl, har, hev, ⟨-, hr'⟩ | ⟨hnt, hr'⟩⟩ :=
        loopIter_ans (lans_closed body) (answered_left hcs) hp' (by rw [hr'']; simp)
      · rw [hr''] at hr'; cases hr'
      · rw [hr''] at hr'
        simp only [PathEnd.val.injEq, Except.ok.injEq, Prod.mk.injEq] at hr'
        obtain ⟨hlo, hs⟩ := hr'
        obtain ⟨vs, rfl, hc⟩ := loopOut_inr hlo.symm
        refine .loopBack har (eval_of_evalO hev)
          ⟨cs₂ ++ₛ ω', ansS_of_append (answered_right hcs) hω', ?_⟩
        rw [denListC_cons]
        have hp₂ := iterPath_path hrest
        obtain ⟨⟨⟨f', stk'⟩⟩, ⟨s'⟩⟩ := p'
        simp only [ULift.up.injEq, Prod.mk.injEq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        cases hs
        rw [← hloop] at hp₂
        exact infR_bind_ok hp₂ h₂

/-- **Productive local divergence.** An infinite run of the exposed body whose
call events are all answered by `closedCall` is local divergence. -/
theorem localDiv_of_prod {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    (h : ProdE s f stk es) : Interp.LocalDiv s f stk es := by
  refine Interp.localDiv_of_coind (X := ProdE) ?_ s f stk es h
  rintro s f stk es ⟨ω, hA, h⟩
  cases es with
  | nil => exact absurd h not_infR_pure
  | cons e es =>
    rw [denListC_cons] at h
    cases e with
    | op i args => exact op_step hA h
    | block bt body => exact block_step hA h
    | loop bt body => exact loop_step hA h
    | if_ bt c t el => exact if_step hA h
    | tryTable bt cs body =>
      rw [denC.eq_def] at h
      rcases infR_bind_inv h with h₁ | ⟨_, _, _, _, h₁, _, _⟩
      · exact absurd h₁ not_infR_stuck
      · exact absurd (path_stuck_inv h₁) (by simp)

/-! ## Reached calls of local divergence return -/

theorem evalDet {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {r₁ r₂ : Store H × Frame × Flow} (h₁ : Eval s f stk es r₁) (h₂ : Eval s f stk es r₂) :
    r₁ = r₂ := Interp.eval_det' h₁ h₂

theorem notEval_of_localDiv {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {r : Store H × Frame × Flow} (hL : Interp.LocalDiv s f stk es) (h : Eval s f stk es r) : False :=
  Interp.not_evalDiv_of_eval h (Interp.localDiv_evalDiv _ _ _ _ hL)

/-- A call reached by a terminating run returns (or traps or throws) in `closedCall`. -/
theorem reach_eval_call {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {y : (wasmOShape H).self.Op} (hR : Reach s f stk es y) :
    ∀ {r}, Eval s f stk es r → ∃ out, closedCall y.2.2 y.1 y.2.1 out := by
  induction hR with
  | @here s s₁ f f₁ stk stk₁ x args es a fi ps rs hargs hfi hty =>
    intro r h
    cases h with
    | argsAbort h' hfl => cases evalDet hargs h'; exact absurd trivial hfl
    | callOk h' hfi' hcode hty' hbody hvs hk =>
      cases evalDet hargs h'
      rw [hfi] at hfi'; cases hfi'
      rw [hty] at hty'; cases hty'
      exact ⟨_, closedCall_of_eval hfi hcode hty hbody⟩
    | callTrap h' hfi' hcode hty' hbody =>
      cases evalDet hargs h'
      rw [hfi] at hfi'; cases hfi'
      rw [hty] at hty'; cases hty'
      exact ⟨_, closedCall_of_eval hfi hcode hty hbody⟩
    | callThrow h' hfi' hcode hty' hbody =>
      cases evalDet hargs h'
      rw [hfi] at hfi'; cases hfi'
      rw [hty] at hty'; cases hty'
      exact ⟨_, closedCall_of_eval hfi hcode hty hbody⟩
    | opOk hi => exact absurd rfl (hi x)
    | opStop hi => exact absurd rfl (hi x)
  | args _ ih =>
    intro r h
    cases h with
    | argsAbort h' => exact ih h'
    | callOk h' => exact ih h'
    | callTrap h' => exact ih h'
    | callThrow h' => exact ih h'
    | opOk _ h' => exact ih h'
    | opStop _ h' => exact ih h'
  | @callK s s₁ s₂ f f₁ f₂ stk stk₁ vs x args es a fi fn ps rs fl y hargs hfi hcode hty hbody hvs _ ih =>
    intro r h
    cases h with
    | argsAbort h' hfl => cases evalDet hargs h'; exact absurd trivial hfl
    | callOk h' hfi' hcode' hty' hbody' hvs' hk =>
      cases evalDet hargs h'
      rw [hfi] at hfi'; cases hfi'
      rw [hcode] at hcode'; cases hcode'
      rw [hty] at hty'; cases hty'
      cases evalDet hbody hbody'
      rw [hvs] at hvs'; cases hvs'
      exact ih hk
    | callTrap h' hfi' hcode' hty' hbody' =>
      cases evalDet hargs h'
      rw [hfi] at hfi'; cases hfi'
      rw [hcode] at hcode'; cases hcode'
      rw [hty] at hty'; cases hty'
      cases evalDet hbody hbody'
      simp [Flow.retVals] at hvs
    | callThrow h' hfi' hcode' hty' hbody' =>
      cases evalDet hargs h'
      rw [hfi] at hfi'; cases hfi'
      rw [hcode] at hcode'; cases hcode'
      rw [hty] at hty'; cases hty'
      cases evalDet hbody hbody'
      simp [Flow.retVals] at hvs
    | opOk hi => exact absurd rfl (hi x)
    | opStop hi => exact absurd rfl (hi x)
  | @opK s s₁ s₂ f f₁ f₂ stk stk₁ stk₂ i args es y hi hargs hflat _ ih =>
    intro r h
    cases h with
    | argsAbort h' hfl => cases evalDet hargs h'; exact absurd trivial hfl
    | callOk => exact absurd rfl (hi _)
    | callTrap => exact absurd rfl (hi _)
    | callThrow => exact absurd rfl (hi _)
    | opOk _ h' hflat' hk =>
      cases evalDet hargs h'
      rw [hflat] at hflat'; cases hflat'
      exact ih hk
    | opStop _ h' hflat' hfl =>
      cases evalDet hargs h'
      rw [hflat] at hflat'; cases hflat'
      exact absurd trivial hfl
  | block har _ ih =>
    intro r h
    cases h with
    | blockOk har' h' => rw [har] at har'; cases har'; exact ih h'
    | blockBrk har' h' => rw [har] at har'; cases har'; exact ih h'
    | blockEsc har' h' => rw [har] at har'; cases har'; exact ih h'
  | @blockK s s₁ f f₁ stk vs bt body es np nr fl y har hbody hvs _ ih =>
    intro r h
    cases h with
    | blockOk har' h' hvs' hk =>
      rw [har] at har'; cases har'
      cases evalDet hbody h'
      rw [hvs] at hvs'; cases hvs'
      exact ih hk
    | blockBrk har' h' =>
      rw [har] at har'; cases har'
      cases evalDet hbody h'
      simp [Flow.blockVals] at hvs
    | blockEsc har' h' hesc =>
      rw [har] at har'; cases har'
      cases evalDet hbody h'
      cases fl <;> simp_all [Flow.blockVals, Flow.Escapes]
  | loop har _ ih =>
    intro r h
    cases h with
    | loopOk har' h' => rw [har] at har'; cases har'; exact ih h'
    | loopBack har' h' => rw [har] at har'; cases har'; exact ih h'
    | loopBrk har' h' => rw [har] at har'; cases har'; exact ih h'
    | loopEsc har' h' => rw [har] at har'; cases har'; exact ih h'
  | @loopK s s₁ f f₁ stk vs bt body es np nr y har hbody _ ih =>
    intro r h
    cases h with
    | loopOk har' h' hk =>
      rw [har] at har'; cases har'
      cases evalDet hbody h'
      exact ih hk
    | loopBack har' h' => rw [har] at har'; cases har'; cases evalDet hbody h'
    | loopBrk har' h' => rw [har] at har'; cases har'; cases evalDet hbody h'
    | loopEsc har' h' hesc => rw [har] at har'; cases har'; cases evalDet hbody h'; exact hesc.elim
  | @loopBack s s₁ f f₁ stk vs bt body es np nr y har hbody _ ih =>
    intro r h
    cases h with
    | loopOk har' h' => rw [har] at har'; cases har'; cases evalDet hbody h'
    | loopBack har' h' hk =>
      rw [har] at har'; cases har'
      cases evalDet hbody h'
      exact ih hk
    | loopBrk har' h' => rw [har] at har'; cases har'; cases evalDet hbody h'
    | loopEsc har' h' hesc => rw [har] at har'; cases har'; cases evalDet hbody h'; exact hesc.elim
  | cond _ ih =>
    intro r h
    cases h with
    | ifOk h' => exact ih h'
    | ifBrk h' => exact ih h'
    | ifEsc h' => exact ih h'
    | ifAbort h' => exact ih h'
  | @arm s s₁ f f₁ stk stk₁ cv b bt c t el es np nr y hc hb har _ ih =>
    intro r h
    cases h with
    | ifOk hc' hb' har' harm =>
      cases evalDet hc hc'
      rw [hb] at hb'; cases hb'
      rw [har] at har'; cases har'
      exact ih harm
    | ifBrk hc' hb' har' harm =>
      cases evalDet hc hc'
      rw [hb] at hb'; cases hb'
      rw [har] at har'; cases har'
      exact ih harm
    | ifEsc hc' hb' har' harm =>
      cases evalDet hc hc'
      rw [hb] at hb'; cases hb'
      rw [har] at har'; cases har'
      exact ih harm
    | ifAbort hc' hfl => cases evalDet hc hc'; exact absurd trivial hfl
  | @ifK s s₁ s₂ f f₁ f₂ stk stk₁ vs cv b bt c t el es np nr fl y hc hb har harm hvs _ ih =>
    intro r h
    cases h with
    | ifOk hc' hb' har' harm' hvs' hk =>
      cases evalDet hc hc'
      rw [hb] at hb'; cases hb'
      rw [har] at har'; cases har'
      cases evalDet harm harm'
      rw [hvs] at hvs'; cases hvs'
      exact ih hk
    | ifBrk hc' hb' har' harm' =>
      cases evalDet hc hc'
      rw [hb] at hb'; cases hb'
      rw [har] at har'; cases har'
      cases evalDet harm harm'
      simp [Flow.blockVals] at hvs
    | ifEsc hc' hb' har' harm' hesc =>
      cases evalDet hc hc'
      rw [hb] at hb'; cases hb'
      rw [har] at har'; cases har'
      cases evalDet harm harm'
      cases fl <;> simp_all [Flow.blockVals, Flow.Escapes]
    | ifAbort hc' hfl => cases evalDet hc hc'; exact absurd trivial hfl

/-- **Under local divergence every reached call returns** (or traps or throws)
in `closedCall`: no callee diverges. -/
theorem localDiv_reach_call {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {y : (wasmOShape H).self.Op} (hR : Reach s f stk es y) :
    Interp.LocalDiv s f stk es → ∃ out, closedCall y.2.2 y.1 y.2.1 out := by
  induction hR with
  | @here s s₁ f f₁ stk stk₁ x args es a fi ps rs hargs hfi hty =>
    intro hL
    cases Interp.localDiv_iff_step.1 hL with
    | args h => exact (notEval_of_localDiv h hargs).elim
    | callee _ _ _ _ h => exact h.elim
    | callRet h' hfi' hcode hty' hbody =>
      cases evalDet hargs h'
      rw [hfi] at hfi'; cases hfi'
      rw [hty] at hty'; cases hty'
      exact ⟨_, closedCall_of_eval hfi hcode hty hbody⟩
    | opK hi => exact absurd rfl (hi x)
  | @args s f stk i args es y hR ih =>
    intro hL
    cases Interp.localDiv_iff_step.1 hL with
    | args h => exact ih h
    | callee _ _ _ _ h => exact h.elim
    | callRet h' => exact reach_eval_call hR h'
    | opK _ h' => exact reach_eval_call hR h'
  | @callK s s₁ s₂ f f₁ f₂ stk stk₁ vs x args es a fi fn ps rs fl y hargs hfi hcode hty hbody hvs _ ih =>
    intro hL
    cases Interp.localDiv_iff_step.1 hL with
    | args h => exact (notEval_of_localDiv h hargs).elim
    | callee _ _ _ _ h => exact h.elim
    | callRet h' hfi' hcode' hty' hbody' hvs' hk =>
      cases evalDet hargs h'
      rw [hfi] at hfi'; cases hfi'
      rw [hcode] at hcode'; cases hcode'
      rw [hty] at hty'; cases hty'
      cases evalDet hbody hbody'
      rw [hvs] at hvs'; cases hvs'
      exact ih hk
    | opK hi => exact absurd rfl (hi x)
  | @opK s s₁ s₂ f f₁ f₂ stk stk₁ stk₂ i args es y hi hargs hflat _ ih =>
    intro hL
    cases Interp.localDiv_iff_step.1 hL with
    | args h => exact (notEval_of_localDiv h hargs).elim
    | callee => exact absurd rfl (hi _)
    | callRet => exact absurd rfl (hi _)
    | opK _ h' hflat' hk =>
      cases evalDet hargs h'
      rw [hflat] at hflat'; cases hflat'
      exact ih hk
  | @block s f stk bt body es np nr y har hR ih =>
    intro hL
    cases Interp.localDiv_iff_step.1 hL with
    | block har' h => rw [har] at har'; cases har'; exact ih h
    | blockK har' h' => rw [har] at har'; cases har'; exact reach_eval_call hR h'
  | @blockK s s₁ f f₁ stk vs bt body es np nr fl y har hbody hvs _ ih =>
    intro hL
    cases Interp.localDiv_iff_step.1 hL with
    | block har' h => rw [har] at har'; cases har'; exact (notEval_of_localDiv h hbody).elim
    | blockK har' h' hvs' hk =>
      rw [har] at har'; cases har'
      cases evalDet hbody h'
      rw [hvs] at hvs'; cases hvs'
      exact ih hk
  | @loop s f stk bt body es np nr y har hR ih =>
    intro hL
    cases Interp.localDiv_iff_step.1 hL with
    | loop har' h => rw [har] at har'; cases har'; exact ih h
    | loopK har' h' => rw [har] at har'; cases har'; exact reach_eval_call hR h'
    | loopBack har' h' => rw [har] at har'; cases har'; exact reach_eval_call hR h'
  | @loopK s s₁ f f₁ stk vs bt body es np nr y har hbody _ ih =>
    intro hL
    cases Interp.localDiv_iff_step.1 hL with
    | loop har' h => rw [har] at har'; cases har'; exact (notEval_of_localDiv h hbody).elim
    | loopK har' h' hk =>
      rw [har] at har'; cases har'
      cases evalDet hbody h'
      exact ih hk
    | loopBack har' h' => rw [har] at har'; cases har'; cases evalDet hbody h'
  | @loopBack s s₁ f f₁ stk vs bt body es np nr y har hbody _ ih =>
    intro hL
    cases Interp.localDiv_iff_step.1 hL with
    | loop har' h => rw [har] at har'; cases har'; exact (notEval_of_localDiv h hbody).elim
    | loopK har' h' => rw [har] at har'; cases har'; cases evalDet hbody h'
    | loopBack har' h' hk =>
      rw [har] at har'; cases har'
      cases evalDet hbody h'
      exact ih hk
  | @cond s f stk bt c t el es y hR ih =>
    intro hL
    cases Interp.localDiv_iff_step.1 hL with
    | cond h => exact ih h
    | arm hc' => exact reach_eval_call hR hc'
    | ifK hc' => exact reach_eval_call hR hc'
  | @arm s s₁ f f₁ stk stk₁ cv b bt c t el es np nr y hc hb har hR ih =>
    intro hL
    cases Interp.localDiv_iff_step.1 hL with
    | cond h => exact (notEval_of_localDiv h hc).elim
    | arm hc' hb' har' h =>
      cases evalDet hc hc'
      rw [hb] at hb'; cases hb'
      rw [har] at har'; cases har'
      exact ih h
    | ifK hc' hb' har' harm =>
      cases evalDet hc hc'
      rw [hb] at hb'; cases hb'
      rw [har] at har'; cases har'
      exact reach_eval_call hR harm
  | @ifK s s₁ s₂ f f₁ f₂ stk stk₁ vs cv b bt c t el es np nr fl y hc hb har harm hvs _ ih =>
    intro hL
    cases Interp.localDiv_iff_step.1 hL with
    | cond h => exact (notEval_of_localDiv h hc).elim
    | arm hc' hb' har' h =>
      cases evalDet hc hc'
      rw [hb] at hb'; cases hb'
      rw [har] at har'; cases har'
      exact (notEval_of_localDiv h harm).elim
    | ifK hc' hb' har' harm' hvs' hk =>
      cases evalDet hc hc'
      rw [hb] at hb'; cases hb'
      rw [har] at har'; cases har'
      cases evalDet harm harm'
      rw [hvs] at hvs'; cases hvs'
      exact ih hk

/-! ## Local divergence is silent divergence or an infinite answered run -/

theorem closedCall_fun {s : Store H} {a : Nat} {args : List Val} {o₁ o₂ : Store H × Flow}
    (h₁ : closedCall s a args o₁) (h₂ : closedCall s a args o₂) : o₁ = o₂ := by
  rw [closedCall_eq] at h₁ h₂
  obtain ⟨fi, fn, ps, rs, f₂, hf, hc, -, hb⟩ := h₁
  obtain ⟨fi', fn', ps', rs', f₂', hf', hc', -, hb'⟩ := h₂
  rw [hf] at hf'; cases hf'
  rw [hc] at hc'; cases hc'
  have := evalDet hb hb'
  simp only [Prod.mk.injEq] at this
  obtain ⟨h1, -, h2⟩ := this
  exact Prod.ext h1 h2

/-- Answered pending prefixes of one tree are comparable (answers are functional). -/
theorem pend_coh {X : Type 1} {t : Tree (SigEv (CallSig H)) X} {cs : List (Call (CallSig H))}
    {m : (CallSig H).Op} (h : Pend t cs m) :
    ∀ {cs' : List (Call (CallSig H))} {m' : (CallSig H).Op}, Pend t cs' m' →
      Answered closedCall cs → Answered closedCall cs' → cs.length ≤ cs'.length → cs <+: cs' := by
  induction h with
  | here => intro _ _ _ _ _ _; exact List.nil_prefix
  | @vis t R e k n cs m ht hp ih =>
    intro cs' m' h' hA hA' hl
    rw [ht] at h'
    rcases pend_vis_inv h' with ⟨rfl, -⟩ | ⟨n', cs₀, rfl, hp'⟩
    · simp at hl
    · have e1 := hA _ (List.mem_cons_self ..)
      have e2 := hA' _ (List.mem_cons_self ..)
      have hn : n = n' := by
        have := closedCall_fun e1 e2
        have h3 := congrArg (cast e.2) this
        simpa using h3
      subst hn
      have := ih hp' (fun c hc => hA c (List.mem_cons_of_mem _ hc))
        (fun c hc => hA' c (List.mem_cons_of_mem _ hc)) (by simpa using hl)
      exact List.prefix_cons_inj _ |>.2 this

theorem path_of_treach {X : Type 1} {t t' : Tree (SigEv (CallSig H)) X}
    {cs cs' : List (Call (CallSig H))} {r : PathEnd X} (h : BodyTrace.Reach t cs t')
    (hp : Path t' cs' r) : Path t (cs ++ cs') r := by
  induction h with
  | nil => exact hp
  | vis ht _ ih => exact .vis ht (ih hp)

theorem pend_of_treach {X : Type 1} {t t' : Tree (SigEv (CallSig H)) X}
    {cs cs' : List (Call (CallSig H))} {m : (CallSig H).Op} (h : BodyTrace.Reach t cs t')
    (hp : Pend t' cs' m) : Pend t (cs ++ cs') m := by
  induction h with
  | nil => exact hp
  | vis ht _ ih => exact .vis ht (ih hp)

theorem take_get : ∀ (n : Nat) (ω : Stream' (Call (CallSig H))) (i : Nat) (hi : i < (Stream'.take n ω).length),
    (Stream'.take n ω)[i] = ω i
  | 0, _, _, hi => by simp at hi
  | n + 1, ω, 0, _ => rfl
  | n + 1, ω, i + 1, hi => by
    simp only [Stream'.take_succ, List.getElem_cons_succ]
    rw [take_get n _ i (by simpa using hi)]
    rfl

theorem call_cast {m : (CallSig H).Op} {R : Type} (h : (CallSig H).Ar m = R)
    (out : (CallSig H).Ar m) : (⟨m, cast h.symm (cast h out)⟩ : Call (CallSig H)) = ⟨m, out⟩ := by
  subst h; rfl

/-- **Local divergence, on the exposed body.** If the problem diverges within
its function (every call it makes returns), the exposed body diverges silently
after `closedCall`-answered events, or has an infinite `closedCall`-answered run. -/
theorem exposed_of_localDiv {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    (hL : Interp.LocalDiv s f stk es) :
    (∃ cs, Answered closedCall cs ∧
        Path (run' (denListC callEv es f stk : M (CallSig H) H Res) ⟨s⟩) cs .div) ∨
      ProdE s f stk es := by
  set t := run' (denListC callEv es f stk : M (CallSig H) H Res) ⟨s⟩ with ht
  have noVal : ∀ cs v, Answered closedCall cs → Path t cs (.val v) → False := by
    intro cs v hA hp
    obtain ⟨r, hev, -⟩ := lans_closed es s f stk cs _ hA hp (by simp)
    exact notEval_of_localDiv hL (eval_of_evalO hev)
  let P : Nat → Prop := fun n => ∃ cs m, cs.length = n ∧ Answered closedCall cs ∧ Pend t cs m
  by_cases hall : ∀ n, P n
  · right
    choose C m hlen hA hp using hall
    let ω : Stream' (Call (CallSig H)) := fun n => (C (n + 1))[n]'(by rw [hlen]; omega)
    have hω : ∀ n i (hi : i < n), (C n)[i]'(by rw [hlen]; exact hi) = ω i := by
      intro n i hi
      have hpre : C (i + 1) <+: C n ∨ C n <+: C (i + 1) := by
        rcases le_total (C (i + 1)).length (C n).length with h | h
        · exact .inl (pend_coh (hp _) (hp _) (hA _) (hA _) h)
        · exact .inr (pend_coh (hp _) (hp _) (hA _) (hA _) h)
      rcases hpre with h | h
      · exact (List.IsPrefix.getElem h (by rw [hlen]; omega)).symm
      · exact List.IsPrefix.getElem h _
    refine ⟨ω, fun n => hA (n + 1) _ (List.getElem_mem _), ?_⟩
    refine Silmaril.Wasm.Abstract.BodyTrace.infPath_iff_pend.2 fun n => ⟨m n, ?_⟩
    have : Stream'.take n ω = C n := by
      apply List.ext_getElem
      · simp [hlen]
      · intro i h1 h2
        rw [take_get]
        exact (hω n i (by simpa using h1)).symm
    rw [this]
    exact hp n
  · classical
    push Not at hall
    have hex : ∃ n, ¬ P n := hall
    let N := Nat.find hex
    have hN : ¬ P N := Nat.find_spec hex
    have hmin : ∀ k < N, P k := fun k hk => by
      have := Nat.find_min hex hk
      exact not_not.1 this
    cases hN0 : N with
    | zero =>
      rw [hN0] at hN
      rcases cases_visible t with hd | ⟨v, hv⟩ | ⟨R, e, k, hv⟩
      · exact .inl ⟨[], answered_nil, .div hd⟩
      · exact (noVal [] v answered_nil (.ret hv)).elim
      · exact (hN ⟨[], e.1, rfl, answered_nil, .here hv⟩).elim
    | succ n =>
      obtain ⟨cs, mm, hl, hA, hp⟩ := hmin n (by omega)
      have hreach := list_pend es s f stk cs mm hA hp
      obtain ⟨out, hout⟩ := localDiv_reach_call hreach hL
      obtain ⟨R, e, k, hr, hem⟩ := pend_iff_reach.1 hp
      let r : R := cast e.2 out
      have hc : (⟨e.1, cast e.2.symm r⟩ : Call (CallSig H)) = ⟨mm, out⟩ := by
        subst hem
        exact call_cast e.2 out
      have hAns : Answered closedCall (cs ++ [⟨mm, out⟩]) :=
        answered_append hA (answered_single hout)
      have hr' : BodyTrace.Reach t (cs ++ [⟨mm, out⟩]) (k r) := by
        rw [← hc]
        exact reach_append.2 ⟨_, hr, .vis rfl .nil⟩
      rcases cases_visible (k r) with hd | ⟨v, hv⟩ | ⟨R', e', k', hv⟩
      · left
        refine ⟨cs ++ [⟨mm, out⟩], hAns, ?_⟩
        have := path_of_treach hr' (Path.div hd)
        simpa using this
      · exact (noVal _ v hAns (by simpa using path_of_treach hr' (Path.ret hv))).elim
      · refine (hN ?_).elim
        rw [hN0]
        refine ⟨cs ++ [⟨mm, out⟩], e'.1, by simp [hl], hAns, ?_⟩
        simpa using pend_of_treach hr' (Pend.here hv)

/-! ## Silent divergence against terminating runs -/

/-- Two finished paths of one tree with `closedCall`-answered events end alike
(answers are functional). -/
theorem path_unique {X : Type 1} {t : Tree (SigEv (CallSig H)) X} {cs₁ : List (Call (CallSig H))}
    {e₁ : PathEnd X} (h₁ : Path t cs₁ e₁) :
    ∀ {cs₂ : List (Call (CallSig H))} {e₂ : PathEnd X}, Path t cs₂ e₂ →
      Answered closedCall cs₁ → Answered closedCall cs₂ → e₁ = e₂ := by
  induction h₁ with
  | ret ht => intro _ _ h₂ _ _; exact ((path_ret_inv ht h₂).2).symm
  | div ht => intro _ _ h₂ _ _; rw [ht] at h₂; exact ((path_diverge_inv h₂).2).symm
  | @vis t R e k n cs r ht hp ih =>
    intro cs₂ e₂ h₂ hA hA'
    rw [ht] at h₂
    obtain ⟨n', cs', rfl, hp'⟩ := Silmaril.Wasm.Abstract.BodyTrace.path_vis_inv h₂
    have e1 := hA _ (List.mem_cons_self ..)
    have e2 := hA' _ (List.mem_cons_self ..)
    have hn : n = n' := by
      have := closedCall_fun e1 e2
      have h3 := congrArg (cast e.2) this
      simpa using h3
    subst hn
    exact ih hp' (fun c hc => hA c (List.mem_cons_of_mem _ hc))
      (fun c hc => hA' c (List.mem_cons_of_mem _ hc))

/-- A call whose body evaluates has no silent exposed divergence. -/
theorem not_silent_of_eval {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {r : Store H × Frame × Flow} (hev : Eval s f stk es r) {cs : List (Call (CallSig H))}
    (hA : Answered closedCall cs)
    (hp : Path (run' (denListC callEv es f stk : M (CallSig H) H Res) ⟨s⟩) cs .div) : False := by
  obtain ⟨cs', hA', hp'⟩ := eval_path' hev
  have := path_unique hp hp' hA hA'
  cases r with
  | mk s' rest =>
    obtain ⟨f', fl⟩ := rest
    cases fl <;> simp [endR] at this

/-- A call whose body evaluates has no infinite exposed run. -/
theorem not_inf_of_eval {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {r : Store H × Frame × Flow} (hev : Eval s f stk es r) (hp : ProdE s f stk es) : False :=
  notEval_of_localDiv (localDiv_of_prod hp) hev

/-- Descents from an evaluating call reach evaluating calls. -/
theorem eval_of_bodyReach {x y : (wasmOShape H).self.Op} (h : BodyReach x y)
    (hx : ∃ fi fn r, x.2.2.funcs[x.1]? = some fi ∧ fi.code = .wasm fn ∧
      Eval x.2.2 (Frame.forCall fi.module x.2.1 fn.locals) [] (liftInstrs fn.body) r) :
    ∃ fi fn r, y.2.2.funcs[y.1]? = some fi ∧ fi.code = .wasm fn ∧
      Eval y.2.2 (Frame.forCall fi.module y.2.1 fn.locals) [] (liftInstrs fn.body) r := by
  obtain ⟨fi, fn, hfi, hcode, hR⟩ := h
  obtain ⟨fi', fn', r, hfi', hcode', hev⟩ := hx
  rw [hfi] at hfi'; cases hfi'
  rw [hcode] at hcode'; cases hcode'
  obtain ⟨out, hout⟩ := reach_eval_call hR hev
  rw [closedCall_eq] at hout
  obtain ⟨fi₂, fn₂, ps, rs, f₂, hf₂, hc₂, -, hb⟩ := hout
  exact ⟨fi₂, fn₂, _, hf₂, hc₂, hb⟩

theorem eval_of_bodyPath {x z : (wasmOShape H).self.Op} (h : BodyPath x z)
    (hx : ∃ fi fn r, x.2.2.funcs[x.1]? = some fi ∧ fi.code = .wasm fn ∧
      Eval x.2.2 (Frame.forCall fi.module x.2.1 fn.locals) [] (liftInstrs fn.body) r) :
    ∃ fi fn r, z.2.2.funcs[z.1]? = some fi ∧ fi.code = .wasm fn ∧
      Eval z.2.2 (Frame.forCall fi.module z.2.1 fn.locals) [] (liftInstrs fn.body) r := by
  induction h with
  | refl => exact hx
  | step hr _ ih => exact ih (eval_of_bodyReach hr hx)

/-- A terminating native invocation evaluates its body. -/
theorem eval_of_invokeRun {s : Store H} {a : Nat} {vs : List Val} {fuel : Nat}
    {r : Store H × Flow} (hF : NativeFuncsOk s.funcs) (h : invokeRun fuel s a vs = some r) :
    ∃ fi fn r', s.funcs[a]? = some fi ∧ fi.code = .wasm fn ∧
      Eval s (Frame.forCall fi.module vs fn.locals) [] (liftInstrs fn.body) r' := by
  cases hfi : s.funcs[a]? with
  | none =>
    rw [Silmaril.Proofs.Wasm.Abstract.StoreBody.invokeRun_none
      (fun _ _ _ _ h' => by rw [hfi] at h'; cases h')] at h
    cases h
  | some fi =>
    obtain ⟨fn, hcode, -⟩ := hF fi (List.mem_of_getElem? hfi)
    cases hty : Validation.DefType.funcType? fi.type with
    | none =>
      rw [Silmaril.Proofs.Wasm.Abstract.StoreBody.invokeRun_none
        (fun _ _ _ _ h' _ ht' => by rw [hfi] at h'; cases h'; rw [hty] at ht'; cases ht')] at h
      cases h
    | some p =>
      obtain ⟨ps, rs⟩ := p
      rw [Silmaril.Proofs.Wasm.Abstract.StoreBody.invokeRun_of hfi hcode hty] at h
      cases hr : run fuel s (Frame.forCall fi.module vs fn.locals) [] (liftInstrs fn.body) with
      | none => rw [hr] at h; cases h
      | some r' => exact ⟨fi, fn, r', rfl, hcode, eval_of_run hr⟩

end Silmaril.Proofs.Wasm.Abstract.StoreCall

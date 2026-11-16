module

public import Silmaril.Proofs.Wasm.Cfg.RegionDiv
public import Silmaril.Proofs.Wasm.Cfg.RegionCallComplete
import Silmaril.Wasm.Execution.Core.Sim.Closure.Frame

@[expose] public section

/-!
# Core 3.0 divergence of code with calls is a diverging region run

For the fragment with calls (`FragC`: direct, `call_indirect`, `call_ref`), a diverging Core run is a `RunDivC` run, with any
complete oracle (`CallCompleteG`) and any complete divergence predicate (`DivCallComplete`), their
guard holding at every call the run reaches (`GuardedCalls`). At a call, the divergent run either
diverges inside the callee (through its frame and any chain of tail calls out of it: the call
alone diverges, so `D` names it) or the callee returns and the continuation diverges
(`callRef_seq_div`, the divergent analogue of `call_seq_split`). Labels and handlers split as in
the call-free proof (`label_exit`, `handler_exit`); their finite bodies are `RunC` runs
(`completeC`), under the guard restricted to the body (`guarded_seq`, `guarded_label`,
`guarded_handler`).
-/

namespace Silmaril.Wasm.Cfg.Proofs.Region

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Region Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

variable {H : Type} {P : Profile} {host : HostSemantics H} {C : Abstract.CallRel H}
  {D : Store H → Nat → List Val → Prop} {G : Store H → Nat → List Val → Prop}

/-! ## The guard on sub-configurations -/

theorem guarded_steps {c₀ c₁ : Config H} (hG : GuardedCalls P host G c₀) (h : Steps P host c₀ c₁) :
    GuardedCalls P host G c₁ :=
  fun c₂ E ws us a cr rest fi ps rs h₂ => hG c₂ E ws us a cr rest fi ps rs (h.trans h₂)

theorem fill_seq (vs : List Val) (code : List Admin) (E : Ctx) (W : List Val) (y : Admin)
    (rest : List Admin) : ∃ (E' : Ctx) (W' : List Val) (rest' : List Admin),
      (∀ us, vals vs ++ E.fill (vals (W ++ us) ++ y :: rest) ++ code =
        E'.fill (vals (W' ++ us) ++ y :: rest')) := by
  cases E with
  | hole => exact ⟨.hole, vs ++ W, rest ++ code, fun us => by simp [Ctx.fill]⟩
  | label ws n cont E r =>
    exact ⟨.label (vs ++ ws) n cont E (r ++ code), W, rest, fun us => by simp [Ctx.fill]⟩
  | handler ws n cs E r =>
    exact ⟨.handler (vs ++ ws) n cs E (r ++ code), W, rest, fun us => by simp [Ctx.fill]⟩

/-- **The guard restricted to a part of a sequence.** -/
theorem guarded_seq {s : Store H} {f : Frame} {vs : List Val} {X code : List Admin}
    (hG : GuardedCalls P host G ⟨s, f, vals vs ++ X ++ code⟩) : GuardedCalls P host G ⟨s, f, X⟩ := by
  intro c₂ E ws us a cr rest fi ps rs h₂ hc hcr hd hfi he hn
  obtain ⟨s₂, f₂, X₂⟩ := c₂
  simp only at hc hfi ⊢
  obtain ⟨E'', W'', rest'', hE''⟩ : ∃ (E'' : Ctx) (W'' : List Val) (rest'' : List Admin),
      vals vs ++ E.fill (vals (ws ++ us) ++ .ref (.func a) :: cr :: rest) ++ code =
        E''.fill (vals (W'' ++ us) ++ .ref (.func a) :: cr :: rest'') := by
    cases E with
    | hole => exact ⟨.hole, vs ++ ws, rest ++ code, by simp [Ctx.fill]⟩
    | label ws' n cont E r =>
      exact ⟨.label (vs ++ ws') n cont E (r ++ code), ws, rest, by simp [Ctx.fill]⟩
    | handler ws' n cs E r =>
      exact ⟨.handler (vs ++ ws') n cs E (r ++ code), ws, rest, by simp [Ctx.fill]⟩
  exact hG ⟨s₂, f₂, vals vs ++ X₂ ++ code⟩ E'' W'' us a cr rest'' fi ps rs (steps_in vs code h₂)
    (by simp only; rw [hc, hE'']) hcr hd hfi he hn

/-- **The guard restricted to a label's body.** -/
theorem guarded_label {s : Store H} {f : Frame} {n : Nat} {cont : List Instr} {X : List Admin}
    (hG : GuardedCalls P host G ⟨s, f, [.label n cont X]⟩) : GuardedCalls P host G ⟨s, f, X⟩ := by
  intro c₂ E ws us a cr rest fi ps rs h₂ hc hcr hd hfi he hn
  obtain ⟨s₂, f₂, X₂⟩ := c₂
  simp only at hc hfi ⊢
  exact hG ⟨s₂, f₂, [.label n cont X₂]⟩ (.label [] n cont E []) ws us a cr rest fi ps rs
    (steps_label n cont h₂) (by simp [Ctx.fill, hc]) hcr hd hfi he hn

/-- **The guard restricted to a handler's body.** -/
theorem guarded_handler {s : Store H} {f : Frame} {n : Nat} {cs : List Catch} {X : List Admin}
    (hG : GuardedCalls P host G ⟨s, f, [.handler n cs X]⟩) : GuardedCalls P host G ⟨s, f, X⟩ := by
  intro c₂ E ws us a cr rest fi ps rs h₂ hc hcr hd hfi he hn
  obtain ⟨s₂, f₂, X₂⟩ := c₂
  simp only at hc hfi ⊢
  exact hG ⟨s₂, f₂, [.handler n cs X₂]⟩ (.handler [] n cs E []) ws us a cr rest fi ps rs
    (steps_handler n cs h₂) (by simp [Ctx.fill, hc]) hcr hd hfi he hn

/-- The guard and the placement of pending tail calls, along the run. -/
def GT (P : Profile) (host : HostSemantics H) (G : Store H → Nat → List Val → Prop)
    (c₀ : Config H) : Prop :=
  GuardedCalls P host G c₀ ∧ TailsOk P host c₀

theorem gt_steps {c₀ c₁ : Config H} (hG : GT P host G c₀) (h : Steps P host c₀ c₁) :
    GT P host G c₁ :=
  ⟨guarded_steps hG.1 h, fun c₂ h₂ => hG.2 c₂ (h.trans h₂)⟩

theorem gt_seq {s : Store H} {f : Frame} {vs : List Val} {X code : List Admin}
    (hG : GT P host G ⟨s, f, vals vs ++ X ++ code⟩) : GT P host G ⟨s, f, X⟩ := by
  refine ⟨guarded_seq hG.1, fun c₂ h₂ => ?_⟩
  obtain ⟨s₂, f₂, X₂⟩ := c₂
  exact Proofs.Region.tailWF_seq (hG.2 _ (steps_in vs code h₂))

theorem gt_label {s : Store H} {f : Frame} {n : Nat} {cont : List Instr} {X : List Admin}
    (hG : GT P host G ⟨s, f, [.label n cont X]⟩) : GT P host G ⟨s, f, X⟩ := by
  refine ⟨guarded_label hG.1, fun c₂ h₂ => ?_⟩
  obtain ⟨s₂, f₂, X₂⟩ := c₂
  exact Proofs.Region.tailWF_label (hG.2 _ (steps_label n cont h₂))

theorem gt_handler {s : Store H} {f : Frame} {n : Nat} {cs : List Catch} {X : List Admin}
    (hG : GT P host G ⟨s, f, [.handler n cs X]⟩) : GT P host G ⟨s, f, X⟩ := by
  refine ⟨guarded_handler hG.1, fun c₂ h₂ => ?_⟩
  obtain ⟨s₂, f₂, X₂⟩ := c₂
  exact Proofs.Region.tailWF_handler (hG.2 _ (steps_handler n cs h₂))

/-! ## Codes that cannot diverge -/

/-- A pending tail call outside any frame is stuck. -/
theorem retCall_stuck {s : Store H} {f : Frame} {vs : List Val} {e : Admin} {es : List Admin}
    {c : Config H} (he : e.IsReturnCallRef) : ¬ Step P host ⟨s, f, vals vs ++ e :: es⟩ c := by
  intro h
  obtain ⟨s', f', es'⟩ := c
  rcases Sim.Step.split_head (Admin.val?_of_isReturnCallRef he) h with
    ⟨ws, us, is', -, hs, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact Sim.Closure.Step.returnCallRef_stuck_aux hs us e he rfl
  · exact he
  · exact he

theorem retCall_not_div {s : Store H} {f : Frame} {vs : List Val} {e : Admin} {es : List Admin}
    (he : e.IsReturnCallRef) : ¬ Diverges P host ⟨s, f, vals vs ++ e :: es⟩ := fun h => by
  obtain ⟨_, hs, -⟩ := h.unfold
  exact retCall_stuck he hs

theorem result_not_div_seq {s : Store H} {f : Frame} {ws : List Val} {r : Result}
    {rest : List Admin} (hr : ∀ vs, r ≠ .values vs) :
    ¬ Diverges P host ⟨s, f, vals ws ++ r.toAdmin ++ rest⟩ := by
  cases r with
  | values vs => exact (hr vs rfl).elim
  | trap => exact fun h => trapForm_not_div ⟨ws, rest, by simp [Result.toAdmin]⟩ h
  | throw t => exact fun h => throwForm_not_div ⟨ws, t, rest, by simp [Result.toAdmin]⟩ h

/-! ## Splitting a diverging call in a sequence -/

/-- The configurations of a call in progress, alone, whose run in the sequence diverges: a
`call_ref` of a typed function on its arguments, or a frame. -/
def CallProg (P : Profile) (host : HostSemantics H) (f : Frame) (ws : List Val)
    (rest : List Admin) (d : Config H) : Prop :=
  d.frame = f ∧ Diverges P host ⟨d.store, f, vals ws ++ d.code ++ rest⟩ ∧
    ((∃ (us : List Val) (a : Nat) (cr : Admin) (fi : FuncInst H) (ps rs : Ty (.list .val)),
        d.code = vals us ++ [.ref (.func a), cr] ∧ cr.IsCallRef ∧ d.store.funcs[a]? = some fi ∧
        Expand fi.type (.func ps rs) ∧ us.length = ps.length) ∨
      ∃ (n : Nat) (F : Frame) (Y : List Admin), d.code = [.frame n F Y])

theorem callProg_step {f : Frame} {ws : List Val} {rest : List Admin} {d : Config H}
    (h : CallProg P host f ws rest d) :
    (∃ d', Step P host d d' ∧ CallProg P host f ws rest d') ∨
      ∃ (s₁ : Store H) (r : Result), Step P host d ⟨s₁, f, r.toAdmin⟩ ∧
        Diverges P host ⟨s₁, f, vals ws ++ r.toAdmin ++ rest⟩ := by
  obtain ⟨st, fd, code⟩ := d
  obtain ⟨hf, hd, ⟨us, a, cr, fi, ps, rs, hc, hcr, hfi, he, hn⟩ | ⟨n, F, Y, hc⟩⟩ := h
  · simp only at hf hc hd hfi; subst hf hc
    obtain ⟨c₁, hs, hd₁⟩ := hd.unfold
    have hs' : Step P host ⟨st, fd, vals (ws ++ us) ++ .ref (.func a) :: cr :: rest⟩ c₁ := by
      simpa using hs
    cases hcode : fi.code with
    | wasm code =>
      obtain ⟨vs₁, vs₂, ps', rs', hsplit, he', hn', rfl⟩ :=
        Step.callRef_wasm_inv_seq hcr hfi hcode hs'
      obtain ⟨rfl, rfl⟩ := expand_func_inj he he'
      obtain ⟨rfl, rfl⟩ := List.append_inj' hsplit.symm (by omega)
      exact .inl ⟨_, Step.callRefFunc hcr hfi he hn hcode,
        rfl, by unfold Diverges; simpa using hd₁, .inr ⟨_, _, _, rfl⟩⟩
    | host hh =>
      obtain ⟨vs₁, vs₂, ps', rs', hsplit, he', hn', hres⟩ :=
        Step.callRef_host_inv_seq hcr hfi hcode hs'
      obtain ⟨rfl, rfl⟩ := expand_func_inj he he'
      obtain ⟨rfl, rfl⟩ := List.append_inj' hsplit.symm (by omega)
      rcases hres with ⟨s', res, hhost, rfl⟩ | ⟨hhost, rfl⟩
      · exact .inr ⟨s', res, Step.callRefHost hcr hfi he hn hcode hhost, hd₁⟩
      · exact .inl ⟨_, Step.callRefHostDiv hcr hfi he hn hcode hhost, rfl,
          by unfold Diverges; simpa using hd₁, .inl ⟨vs₂, a, cr, fi, ps, rs, rfl, hcr, hfi, he, hn⟩⟩
  · simp only at hf hc hd; subst hf hc
    obtain ⟨c₁, hs, hd₁⟩ := hd.unfold
    obtain ⟨c₀, h₀, rfl⟩ := Step.ctx_in_seq (X := .frame n F Y) trivial (by simpa using hs)
    rcases Step.frame_inv h₀ with ⟨s', F', Y', hin, rfl⟩ | ⟨out, hx, rfl⟩
    · exact .inl ⟨_, h₀, rfl, by unfold Diverges; simpa using hd₁, .inr ⟨n, F', Y', rfl⟩⟩
    · cases hx with
      | vals hn' => exact .inr ⟨st, .values _, h₀, by unfold Diverges; simpa [Result.toAdmin] using hd₁⟩
      | ret hn' => exact .inr ⟨st, .values _, h₀, by unfold Diverges; simpa [Result.toAdmin] using hd₁⟩
      | trap => exact .inr ⟨st, .trap, h₀, by unfold Diverges; simpa [Result.toAdmin] using hd₁⟩
      | throw t => exact .inr ⟨st, .throw t, h₀, by unfold Diverges; simpa [Result.toAdmin] using hd₁⟩
      | returnCallNull hc' => exact .inr ⟨st, .trap, h₀, by unfold Diverges; simpa [Result.toAdmin] using hd₁⟩
      | returnCallAddr hc' hf' he' hn' =>
        exact .inl ⟨_, h₀, rfl, by unfold Diverges; simpa using hd₁,
          .inl ⟨_, _, _, _, _, _, rfl, isCallRef_retToCallIn hc' F.module, hf', he', hn'⟩⟩

/-- **Splitting a diverging call in a sequence** (every profile and host): a divergent run of
a `call_ref` of a typed function on its arguments `us`, under values `ws` and before `rest`,
diverges in the call alone (inside the callee, through any chain of tail calls), or the call
alone runs to a result in the caller's frame and the sequence diverges after it. -/
theorem callRef_seq_div {s : Store H} {f : Frame} {ws us : List Val} {a : Nat} {cr : Admin}
    {fi : FuncInst H} {ps rs : Ty (.list .val)} {rest : List Admin} (hcr : cr.IsCallRef)
    (hfi : s.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs)) (hn : us.length = ps.length)
    (h : Diverges P host ⟨s, f, vals ws ++ (vals us ++ [.ref (.func a), cr]) ++ rest⟩) :
    Diverges P host ⟨s, f, vals us ++ [.ref (.func a), cr]⟩ ∨
      ∃ (s₁ : Store H) (r : Result),
        Steps P host ⟨s, f, vals us ++ [.ref (.func a), cr]⟩ ⟨s₁, f, r.toAdmin⟩ ∧
        Diverges P host ⟨s₁, f, vals ws ++ r.toAdmin ++ rest⟩ := by
  classical
  by_cases hfin : ∃ (s₁ : Store H) (r : Result), Steps P host ⟨s, f, vals us ++ [.ref (.func a), cr]⟩ ⟨s₁, f, r.toAdmin⟩ ∧
      Diverges P host ⟨s₁, f, vals ws ++ r.toAdmin ++ rest⟩
  · exact .inr hfin
  refine .inl (InfiniteTrace.coinduct (fun d => Steps P host ⟨s, f, vals us ++ [.ref (.func a), cr]⟩ d ∧
      CallProg P host f ws rest d) ?_ ⟨.refl, rfl, h, .inl ⟨us, a, cr, fi, ps, rs, rfl, hcr, hfi, he, hn⟩⟩)
  rintro d ⟨hr, hp⟩
  rcases callProg_step hp with ⟨d', hs, hp'⟩ | ⟨s₁, r, hs, hd⟩
  · exact ⟨d', hs, hr.tail hs, hp'⟩
  · exact (hfin ⟨s₁, r, hr.tail hs, hd⟩).elim

/-- A step of a `call_ref` in a sequence splits the values at the callee's parameters. -/
theorem callRef_split {s : Store H} {f : Frame} {vs : List Val} {a : Nat} {cr : Admin}
    {fi : FuncInst H} {rest : List Admin} {c : Config H} (hcr : cr.IsCallRef)
    (hfi : s.funcs[a]? = some fi) (h : Step P host ⟨s, f, vals vs ++ .ref (.func a) :: cr :: rest⟩ c) :
    ∃ (ws us : List Val) (ps rs : Ty (.list .val)), vs = ws ++ us ∧
      Expand fi.type (.func ps rs) ∧ us.length = ps.length := by
  cases hcode : fi.code with
  | wasm code =>
    obtain ⟨vs₁, vs₂, ps, rs, h1, he, hn, -⟩ := Step.callRef_wasm_inv_seq hcr hfi hcode h
    exact ⟨vs₁, vs₂, ps, rs, h1, he, hn⟩
  | host hh =>
    obtain ⟨vs₁, vs₂, ps, rs, h1, he, hn, -⟩ := Step.callRef_host_inv_seq hcr hfi hcode h
    exact ⟨vs₁, vs₂, ps, rs, h1, he, hn⟩

/-! ## Completeness for divergence with calls -/

/-- The invariant of the coinduction: fragment code with calls, diverging, guarded. -/
def DivInv (P : Profile) (host : HostSemantics H) (G : Store H → Nat → List Val → Prop)
    (s : Store H) (f : Frame) (vs : List Val) (code : List Admin) : Prop :=
  FragC code ∧ Diverges P host ⟨s, f, vals vs ++ code⟩ ∧ GT P host G ⟨s, f, vals vs ++ code⟩

/-- **A diverging direct call is one layer of a diverging region run**: `D` names it (it
diverges inside the callee), or `C` answers it with values and the continuation diverges. -/
theorem div_call (hC : CallCompleteG P host G C) (hD : DivCallComplete P host G D)
    {s : Store H} {f : Frame} {vs : List Val} {x : FuncIdx} {code : List Admin}
    (hF : FragC code) (hd : Diverges P host ⟨s, f, vals vs ++ .plain (.call x) :: code⟩)
    (hG : GT P host G ⟨s, f, vals vs ++ .plain (.call x) :: code⟩) :
    DivFC P host C D (DivInv P host G) s f vs (.plain (.call x) :: code) := by
  obtain ⟨c₁, hs, hd₁⟩ := hd.unfold
  obtain ⟨a, fi, hx, hfi, rfl⟩ := Step.call_vals_inv_seq hs
  obtain ⟨c₂, hs₂, -⟩ := hd₁.unfold
  obtain ⟨ws, us, ps, rs, rfl, he, hn⟩ := callRef_split (cr := .callRefType fi.type) trivial hfi hs₂
  have hfunc : s.func? f x = some (a, fi) := by simp [Store.func?, hx, hfi]
  have hty := funcType_of_expand he
  have hGc : G s a us := guarded_call (E := .hole) (ws := ws) (rest := code) hG.1 .refl (by simp [Ctx.fill]) hx hfi he hn
  have hd₂ : Diverges P host
      ⟨s, f, vals ws ++ (vals us ++ [.ref (.func a), .callRefType fi.type]) ++ code⟩ := by
    unfold Diverges; simpa using hd₁
  rcases callRef_seq_div (cr := .callRefType fi.type) trivial hfi he hn hd₂ with hdiv | ⟨s₁, r, hcs, hd₃⟩
  · exact .callDiv hfunc hty hn (hD s f a fi _ _ us (.callRefType fi.type) hGc trivial hfi hty hn hdiv)
  · cases r with
    | values vs₁ =>
      obtain ⟨-, fl, hcall, hres⟩ := hC s s₁ f f a fi _ _ us (.callRefType fi.type) (.values vs₁) hGc trivial hfi hty hn hcs
      obtain ⟨w, hw, rfl⟩ := hres
      have hsteps : Steps P host ⟨s, f, vals (ws ++ us) ++ .plain (.call x) :: code⟩
          ⟨s₁, f, vals (ws ++ ((w.take rs.toList.length).reverse)) ++ code⟩ := by
        refine .head (call_head hfunc) ?_
        simpa [Result.toAdmin] using steps_in ws code hcs
      exact .call hfunc hty hn hcall hw ⟨hF, by unfold Diverges at hd₃ ⊢; simpa [Result.toAdmin] using hd₃,
        gt_steps hG hsteps⟩
    | trap => exact (result_not_div_seq (r := .trap) (by simp) hd₃).elim
    | throw t => exact (result_not_div_seq (r := .throw t) (by simp) hd₃).elim

/-- A diverging `call_ref y` in a sequence is of a function reference, and diverges in the call
alone or after a Core result of the call (a null reference traps, any other value is stuck). -/
theorem callRef_div_cases {s : Store H} {f : Frame} {V : List Val} {y : TypeIdx}
    {code : List Admin} (hd : Diverges P host ⟨s, f, vals V ++ .plain (.callRef y) :: code⟩) :
    ∃ (ws us : List Val) (a : Nat) (fi : FuncInst H) (ps rs : Ty (.list .val)),
      V = ws ++ us ++ [.ref (.func a)] ∧ s.funcs[a]? = some fi ∧
      Expand fi.type (.func ps rs) ∧ us.length = ps.length ∧
      (Diverges P host ⟨s, f, vals us ++ [.ref (.func a), .plain (.callRef y)]⟩ ∨
        ∃ (s₁ : Store H) (r : Result),
          Steps P host ⟨s, f, vals us ++ [.ref (.func a), .plain (.callRef y)]⟩ ⟨s₁, f, r.toAdmin⟩ ∧
          Diverges P host ⟨s₁, f, vals ws ++ r.toAdmin ++ code⟩) := by
  obtain ⟨c₁, hs, hd₁⟩ := hd.unfold
  rcases Step.callRef_top_inv_seq (r := .plain (.callRef y)) trivial hs with
    ⟨w, rfl, rfl⟩ | ⟨w, a, fi, rfl, hfi⟩
  · exact (trapForm_not_div ⟨w, code, rfl⟩ hd₁).elim
  · have hs' : Step P host ⟨s, f, vals w ++ .ref (.func a) :: .plain (.callRef y) :: code⟩ c₁ := by
      simpa [vals, Val.toAdmin] using hs
    obtain ⟨ws, us, ps, rs, rfl, he, hn⟩ := callRef_split (cr := .plain (.callRef y)) trivial hfi hs'
    have hd₂ : Diverges P host
        ⟨s, f, vals ws ++ (vals us ++ [.ref (.func a), .plain (.callRef y)]) ++ code⟩ := by
      have h' := hd
      unfold Diverges at h' ⊢; simpa [vals, Val.toAdmin] using h'
    exact ⟨ws, us, a, fi, ps, rs, rfl, hfi, he, hn,
      callRef_seq_div (cr := .plain (.callRef y)) trivial hfi he hn hd₂⟩

/-- **A diverging `call_ref` of a resolved function is one layer of a diverging region run**,
given the callee's argument split (`callRef_div_cases`): `D` names it, or `C` answers it with
values and the continuation diverges. `hk` relates the region stack to the Core one. -/
theorem div_callRefAt (hC : CallCompleteG P host G C) (hD : DivCallComplete P host G D)
    {s : Store H} {f : Frame} {ws us : List Val} {a : Nat} {fi : FuncInst H}
    {ps rs : Ty (.list .val)} {y : TypeIdx} {code : List Admin} (hF : FragC code)
    (hfi : s.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs)) (hn : us.length = ps.length)
    (hGc : G s a us)
    (hG : ∀ {s₁ : Store H} {W : List Val},
      Steps P host ⟨s, f, vals us ++ [.ref (.func a), .plain (.callRef y)]⟩ ⟨s₁, f, vals W⟩ →
      GT P host G ⟨s₁, f, vals (ws ++ W) ++ code⟩)
    (hcases : Diverges P host ⟨s, f, vals us ++ [.ref (.func a), .plain (.callRef y)]⟩ ∨
        ∃ (s₁ : Store H) (r : Result),
          Steps P host ⟨s, f, vals us ++ [.ref (.func a), .plain (.callRef y)]⟩ ⟨s₁, f, r.toAdmin⟩ ∧
          Diverges P host ⟨s₁, f, vals ws ++ r.toAdmin ++ code⟩) :
    (D s a us) ∨ ∃ (s₁ : Store H) (fl : Binaryen.Flow) (vs₁ : List Val),
      C s a us (s₁, fl) ∧ fl.retVals = some vs₁ ∧
      DivInv P host G s₁ f (ws ++ (vs₁.take rs.toList.length).reverse) code := by
  have hty := funcType_of_expand he
  rcases hcases with hdiv | ⟨s₁, r, hcs, hd₃⟩
  · exact .inl (hD s f a fi _ _ us (.plain (.callRef y)) hGc trivial hfi hty hn hdiv)
  · cases r with
    | values vs₁ =>
      obtain ⟨-, fl, hcall, hres⟩ :=
        hC s s₁ f f a fi _ _ us (.plain (.callRef y)) (.values vs₁) hGc trivial hfi hty hn hcs
      obtain ⟨w, hw, rfl⟩ := hres
      refine .inr ⟨s₁, fl, w, hcall, hw, hF, ?_, ?_⟩
      · unfold Diverges at hd₃ ⊢; simpa [Result.toAdmin] using hd₃
      · simpa using hG (by simpa [Result.toAdmin] using hcs)
    | trap => exact (result_not_div_seq (r := .trap) (by simp) hd₃).elim
    | throw t => exact (result_not_div_seq (r := .throw t) (by simp) hd₃).elim

/-- **A diverging `call_ref` is one layer of a diverging region run.** -/
theorem div_callRef (hC : CallCompleteG P host G C) (hD : DivCallComplete P host G D)
    {s : Store H} {f : Frame} {vs : List Val} {y : TypeIdx} {code : List Admin}
    (hF : FragC code) (hd : Diverges P host ⟨s, f, vals vs ++ .plain (.callRef y) :: code⟩)
    (hG : GT P host G ⟨s, f, vals vs ++ .plain (.callRef y) :: code⟩) :
    DivFC P host C D (DivInv P host G) s f vs (.plain (.callRef y) :: code) := by
  obtain ⟨ws, us, a, fi, ps, rs, rfl, hfi, he, hn, hcases⟩ := callRef_div_cases hd
  have hcode : vals (ws ++ us ++ [.ref (.func a)]) ++ .plain (.callRef y) :: code =
      Ctx.hole.fill (vals (ws ++ us) ++ .ref (.func a) :: .plain (.callRef y) :: code) := by
    simp [Ctx.fill, vals, Val.toAdmin]
  have hGc : G s a us := hG.1 _ .hole ws us a (.plain (.callRef y)) code fi ps rs .refl hcode trivial
    (fun d hd => by cases hd) hfi he hn
  have hty := funcType_of_expand he
  rcases div_callRefAt hC hD hF hfi he hn hGc (fun hcs => gt_steps hG (by
      rw [hcode]; simpa [Ctx.fill] using steps_in ws code hcs)) hcases with
    hdiv | ⟨s₁, fl, vs₁, hcall, hw, hinv⟩
  · exact .callRefDiv hfi hty hn hdiv
  · exact .callRef hfi hty hn hcall hw hinv

/-- The first step of a non-control instruction in a sequence, by its family's rule. -/
theorem noncontrol_head {s : Store H} {f : Frame} {vs : List Val} {i : Instr} {rest : List Admin}
    {c : Config H} (hk : SingleThreaded.Det.famOf (.plain i) ≠ .control)
    (h : Step P host ⟨s, f, vals vs ++ .plain i :: rest⟩ c) :
    ∃ ws us c₀, vs = ws ++ us ∧ FamStep P ⟨s, f, vals us ++ [.plain i]⟩ c₀ ∧
      c = ⟨c₀.store, c₀.frame, vals ws ++ c₀.code ++ rest⟩ := by
  obtain ⟨s₁, f₁, x₁⟩ := c
  have hv : (Admin.plain i).val? = none := Proofs.Exec.val_none_of_noncontrol hk
  have hnt : i ≠ .throwRef := by rintro rfl; simp [SingleThreaded.Det.famOf] at hk
  obtain ⟨ws, us, is', rfl, hs', rfl⟩ := Proofs.Exec.head_of hv hnt h
  obtain ⟨ws', vs', c₀, rfl, hf, he⟩ := Step.noncontrol_vals_inv hk hs'
  simp only [Config.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  exact ⟨ws ++ ws', vs', c₀, by simp, hf, by simp⟩

/-- **A diverging `call_indirect` is one layer of a diverging region run**: the index resolves
(`CallRes.IndRes`) to a function, which `D` names or `C` answers with values; an unresolved
index traps, so it never diverges. -/
theorem div_callInd (hC : CallCompleteG P host G C) (hD : DivCallComplete P host G D)
    {s : Store H} {f : Frame} {vs : List Val} {x : TableIdx} {y : TypeIdx} {code : List Admin}
    (hF : FragC code) (hd : Diverges P host ⟨s, f, vals vs ++ .plain (.callIndirect x y) :: code⟩)
    (hG : GT P host G ⟨s, f, vals vs ++ .plain (.callIndirect x y) :: code⟩) :
    DivFC P host C D (DivInv P host G) s f vs (.plain (.callIndirect x y) :: code) := by
  obtain ⟨c₁, hs, hd₁⟩ := hd.unfold
  have hc₁ := Step.callIndirect_vals_inv_seq hs
  subst hc₁
  -- `table.get`
  obtain ⟨c₂, hs₂, hd₂⟩ := hd₁.unfold
  obtain ⟨W, us₀, c₀, rfl, hf₀, rfl⟩ := noncontrol_head (famOf_tableGet' x) hs₂
  obtain ⟨ad, i, ta, ti, rfl, ht, ⟨r, hr, rfl⟩ | ⟨-, rfl⟩⟩ := famStep_tableGet_inv hf₀
  swap
  · exact (trapForm_not_div ⟨W, .plain (.refCast ⟨true, .typeIdx y⟩) :: .plain (.callRef y) :: code,
      by simp⟩ hd₂).elim
  -- `ref.cast`
  obtain ⟨c₃, hs₃, hd₃⟩ := hd₂.unfold
  have hs₃' : Step P host ⟨s, f, vals (W ++ [.ref r]) ++ .plain (.refCast ⟨true, .typeIdx y⟩) ::
      .plain (.callRef y) :: code⟩ c₃ := by rw [vals_snoc_ref]; exact hs₃
  obtain ⟨W', us₁, c₀', hW, hf₁, rfl⟩ := noncontrol_head (famOf_refCast' _) hs₃'
  obtain ⟨r', rfl, ⟨hok, rfl⟩ | ⟨-, rfl⟩⟩ := famStep_refCast_inv hf₁
  swap
  · exact (trapForm_not_div ⟨W', .plain (.callRef y) :: code, by simp⟩ hd₃).elim
  obtain ⟨rfl, hrr⟩ := List.append_inj' hW rfl
  simp only [List.cons.injEq, Val.ref.injEq, and_true] at hrr
  subst hrr
  -- `call_ref`
  have hd₄ : Diverges P host ⟨s, f, vals (W ++ [.ref r]) ++ .plain (.callRef y) :: code⟩ := by
    rw [vals_snoc_ref]; exact hd₃
  obtain ⟨ws, us, a, fi, ps, rs, hV, hfi, he, hn, hcases⟩ := callRef_div_cases hd₄
  obtain ⟨hW', hrr⟩ := List.append_inj' hV rfl
  simp only [List.cons.injEq, Val.ref.injEq, and_true] at hrr
  subst hW' hrr
  have hres : Abstract.CallRes.IndRes s f x y ad i (some a) := .func ht hr hok
  have hpre : Steps P host ⟨s, f, vals (ws ++ us ++ [.num ⟨.int ad.intType, i⟩]) ++
      .plain (.callIndirect x y) :: code⟩
      ⟨s, f, vals ws ++ (vals us ++ [.ref (.func a), .plain (.callRef y)]) ++ code⟩ :=
    callInd_head (P := P) (host := host) hres
  have hcode : vals ws ++ (vals us ++ [.ref (.func a), .plain (.callRef y)]) ++ code =
      Ctx.hole.fill (vals (ws ++ us) ++ .ref (.func a) :: .plain (.callRef y) :: code) := by
    simp [Ctx.fill]
  have hGc : G s a us := hG.1 _ .hole ws us a (.plain (.callRef y)) code fi ps rs hpre hcode trivial
    (fun d hd => by cases hd) hfi he hn
  have hty := funcType_of_expand he
  rcases div_callRefAt hC hD hF hfi he hn hGc (fun hcs => gt_steps hG (hpre.trans (by
      simpa using steps_in ws code hcs))) hcases with
    hdiv | ⟨s₁, fl, vs₁, hcall, hw, hinv⟩
  · exact .callIndDiv hres hfi hty hn hdiv
  · exact .callInd hres hfi hty hn hcall hw hinv

/-- **Completeness for divergence with calls**: under the atomic obligation, a complete
oracle `C` and a complete divergence predicate `D`, their guard `G` holding at every call the run
reaches, every diverging Core run of fragment code with calls is a diverging region run. -/
theorem div_completeC (hA : AtomTerm P host) (hC : CallCompleteG P host G C)
    (hD : DivCallComplete P host G D) {s : Store H} {f : Frame} {vs : List Val}
    {code : List Admin} (hF : FragC code) (hG : GuardedCalls P host G ⟨s, f, vals vs ++ code⟩)
    (hW : TailsOk P host ⟨s, f, vals vs ++ code⟩)
    (hd : Diverges P host ⟨s, f, vals vs ++ code⟩) : RunDivC P host C D s f vs code := by
  refine ⟨DivInv P host G, ?_, hF, hd, ⟨hG, hW⟩⟩
  rintro s f vs code ⟨hF, hd, hG⟩
  rcases code with _ | ⟨a, code⟩
  · obtain ⟨c', hs, -⟩ := hd.unfold
    exact (Step.not_vals (by simpa using hs)).elim
  have hF' : FragC code := fun x hx => hF x (by simp [hx])
  have ha := hF a (by simp)
  have val_case : ∀ v, a.val? = some v → DivFC P host C D (DivInv P host G) s f vs (a :: code) :=
    fun v hv => .val hv ⟨hF', by rw [Admin.eq_of_val? hv] at hd; simpa [vals] using hd,
      by rw [Admin.eq_of_val? hv] at hG; simpa [vals] using hG⟩
  cases ha with
  | val h =>
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 h
    exact val_case v hv
  | trap => exact (trapForm_not_div ⟨vs, code, rfl⟩ hd).elim
  | retType d => exact (retCall_not_div (vs := vs) (es := code) (e := .returnCallRefType d) trivial hd).elim
  | @label _ n cont inner hc hi =>
    have hGi : GT P host G ⟨s, f, inner⟩ :=
      gt_label (gt_seq (vs := vs) (code := code) (X := [.label n cont inner])
        (by simpa using hG))
    rcases label_exit hd with hin | ⟨⟨sa, fa, xa⟩, hr, out, hx, hb⟩
    · exact .labelIn ⟨hi, by simpa [vals] using hin, by simpa [vals] using hGi⟩
    · have hst : Steps P host ⟨s, f, vals vs ++ .label n cont inner :: code⟩
          ⟨sa, fa, vals vs ++ [.label n cont xa] ++ code⟩ := by
        simpa using steps_in vs code (steps_label n cont hr)
      cases hx with
      | vals ws =>
        have hin : RunC P host C s f [] inner sa fa (.normal ws) := completeC hC hGi.1 hGi.2 hi hr rfl
        have h2 := step_in (P := P) (host := host) vs code
          (Step.labelVals (s := sa) (f := fa) (n := n) (cont := cont) (vs := ws))
        exact .labelNormal hin ⟨hF', by simpa using hb,
          by simpa using gt_steps hG (hst.tail h2)⟩
      | @brZero vs' us l rest hl hn =>
        have hin : RunC P host C s f [] inner sa fa (.br 0 (vs' ++ us)) :=
          completeC hC hGi.1 hGi.2 hi hr ⟨l, rest, hl, by simp⟩
        have h2 := step_in (P := P) (host := host) vs code
          (Step.brLabelZero (s := sa) (f := fa) (n := n) (cont := cont) (vs' := vs') (vs := us)
            (l := l) (rest := rest) hl hn)
        refine .labelBr0 hin hn ⟨?_, by simpa using hb,
          by simpa using gt_steps hG (hst.tail h2)⟩
        exact frag_append.2 ⟨frag_append.2 ⟨frag_vals _, frag_expression hc⟩, hF'⟩
      | @brSucc us l rest _ =>
        obtain ⟨c', hs, -⟩ := hb.unfold
        exact (br_stuck_seq (vs := vs ++ us) (rest := code) (by simpa using hs)).elim
      | @ret us rest =>
        obtain ⟨c', hs, -⟩ := hb.unfold
        exact (ret_stuck_seq (vs := vs ++ us) (rest := code) (by simpa using hs)).elim
      | @returnCall us c rest hc' =>
        exact (retCall_not_div (vs := vs ++ us) (es := code) hc' (by simpa using hb)).elim
      | throw a => exact (throwForm_not_div ⟨vs, a, code, by simp⟩ hb).elim
      | trap => exact (trapForm_not_div ⟨vs, code, by simp⟩ hb).elim
  | @handler _ n cs inner hi =>
    have hGi : GT P host G ⟨s, f, inner⟩ :=
      gt_handler (gt_seq (vs := vs) (code := code) (X := [.handler n cs inner])
        (by simpa using hG))
    rcases handler_exit hd with hin | ⟨⟨sa, fa, xa⟩, hr, out, hx, hb⟩
    · exact .handlerIn ⟨hi, by simpa [vals] using hin, by simpa [vals] using hGi⟩
    · have hst : Steps P host ⟨s, f, vals vs ++ .handler n cs inner :: code⟩
          ⟨sa, fa, vals vs ++ [.handler n cs xa] ++ code⟩ := by
        simpa using steps_in vs code (steps_handler n cs hr)
      cases hx with
      | vals ws =>
        have hin : RunC P host C s f [] inner sa fa (.normal ws) := completeC hC hGi.1 hGi.2 hi hr rfl
        have h2 := step_in (P := P) (host := host) vs code
          (Step.handlerVals (s := sa) (f := fa) (n := n) (cs := cs) (vs := ws))
        exact .handlerNormal hin ⟨hF', by simpa using hb,
          by simpa using gt_steps hG (hst.tail h2)⟩
      | @br _ us l rest =>
        obtain ⟨c', hs, -⟩ := hb.unfold
        exact (br_stuck_seq (vs := vs ++ us) (rest := code) (by simpa using hs)).elim
      | @ret _ us rest =>
        obtain ⟨c', hs, -⟩ := hb.unfold
        exact (ret_stuck_seq (vs := vs ++ us) (rest := code) (by simpa using hs)).elim
      | @returnCall _ us c rest hc' =>
        exact (retCall_not_div (vs := vs ++ us) (es := code) hc' (by simpa using hb)).elim
      | trap => exact (trapForm_not_div ⟨vs, code, by simp⟩ hb).elim
      | throwEmpty a => exact (throwForm_not_div ⟨vs, a, code, by simp⟩ hb).elim
      | catch_ =>
        obtain ⟨c', hs, -⟩ := hb.unfold
        exact (br_stuck_seq (vs := vs ++ _) (rest := code) (by simpa using hs)).elim
      | catchRef =>
        obtain ⟨c', hs, -⟩ := hb.unfold
        exact (br_stuck_seq (vs := vs ++ (_ ++ [.ref (.exn _)])) (rest := code)
          (by simpa [vals, Val.toAdmin] using hs)).elim
      | catchAll =>
        obtain ⟨c', hs, -⟩ := hb.unfold
        exact (br_stuck_seq (vs := vs) (rest := code) (by simpa using hs)).elim
      | catchAllRef =>
        obtain ⟨c', hs, -⟩ := hb.unfold
        exact (br_stuck_seq (vs := vs ++ [.ref (.exn _)]) (rest := code)
          (by simpa [vals, Val.toAdmin] using hs)).elim
      | next => exact (handler_throwing_not_div (by simpa using hb)).elim
  | @plain _ i hI =>
    cases hI with
    | call x => exact div_call hC hD hF' hd hG
    | callIndirect x y => exact div_callInd hC hD hF' hd hG
    | callRef y => exact div_callRef hC hD hF' hd hG
    | returnCallRef y =>
      exact (retCall_not_div (vs := vs) (es := code) (e := .plain (.returnCallRef y)) trivial hd).elim
    | returnCall x =>
      obtain ⟨c₁, hs, hd₁⟩ := hd.unfold
      obtain ⟨a, fi, -, -, rfl⟩ := Step.returnCall_vals_inv_seq hs
      exact (retCall_not_div (vs := vs ++ [.ref (.func a)]) (e := .returnCallRefType fi.type)
        (es := code) trivial (by unfold Diverges; simpa [vals_snoc_ref, Val.toAdmin] using hd₁)).elim
    | returnCallIndirect x y =>
      obtain ⟨c₁, hs, hd₁⟩ := hd.unfold
      have hc₁ := Step.returnCallIndirect_vals_inv_seq hs
      subst hc₁
      obtain ⟨c₂, hs₂, hd₂⟩ := hd₁.unfold
      obtain ⟨W, us₀, c₀, rfl, hf₀, rfl⟩ := noncontrol_head (famOf_tableGet' x) hs₂
      obtain ⟨ad, i, ta, ti, rfl, ht, ⟨r, hr, rfl⟩ | ⟨-, rfl⟩⟩ := famStep_tableGet_inv hf₀
      swap
      · exact (trapForm_not_div ⟨W, .plain (.refCast ⟨true, .typeIdx y⟩) ::
          .plain (.returnCallRef y) :: code, by simp⟩ hd₂).elim
      obtain ⟨c₃, hs₃, hd₃⟩ := hd₂.unfold
      have hs₃' : Step P host ⟨s, f, vals (W ++ [.ref r]) ++ .plain (.refCast ⟨true, .typeIdx y⟩) ::
          .plain (.returnCallRef y) :: code⟩ c₃ := by rw [vals_snoc_ref]; exact hs₃
      obtain ⟨W', us₁, c₀', hW, hf₁, rfl⟩ := noncontrol_head (famOf_refCast' _) hs₃'
      obtain ⟨r', rfl, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := famStep_refCast_inv hf₁
      · exact (retCall_not_div (vs := W' ++ [.ref r']) (e := .plain (.returnCallRef y)) (es := code)
          trivial (by unfold Diverges; simpa [vals_snoc_ref, Val.toAdmin] using hd₃)).elim
      · exact (trapForm_not_div ⟨W', .plain (.returnCallRef y) :: code, by simp⟩ hd₃).elim
    | throw x =>
      obtain ⟨⟨s₁, f₁, x₁⟩, hs, hd₁⟩ := hd.unfold
      obtain ⟨ws, us, is', rfl, hs', rfl⟩ := Proofs.Exec.head_of rfl (by simp) hs
      obtain ⟨ws', vs', ta, ti, ts, rfl, -, -, -, he⟩ := Step.throw_vals_inv hs'
      simp only [Config.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      exact (throwForm_not_div ⟨ws ++ ws', s.exns.length, code, by simp⟩ hd₁).elim
    | throwRef =>
      exact (by
        obtain ⟨⟨s₁, f₁, x₁⟩, hs, hd₁⟩ := hd.unfold
        rcases Sim.Step.split_head rfl hs with ⟨ws, us, is', rfl, hs', rfl⟩ | ⟨h, -⟩ |
            ⟨-, -, -, ws, us, x, r, r', hus, rfl, hne, rfl⟩
        · rcases Step.throwRef_vals_inv hs' with ⟨w, rfl, he⟩ | ⟨w, w', b, rfl, -, he⟩
          · simp only [Config.mk.injEq] at he; obtain ⟨rfl, rfl, rfl⟩ := he
            exact (trapForm_not_div ⟨ws ++ w, code, by simp⟩ hd₁).elim
          · simp only [Config.mk.injEq] at he; obtain ⟨rfl, rfl, rfl⟩ := he
            exact (throwForm_not_div ⟨ws ++ w, b, code, by simp⟩ hd₁).elim
        · cases h
        · exact (throwForm_not_div ⟨ws, x, r', by simp⟩ hd₁).elim)
    | @tryTable _ bt cs b hb =>
      obtain ⟨⟨s₁, f₁, x₁⟩, hs, hd₁⟩ := hd.unfold
      obtain ⟨ws, us, is', rfl, hs', rfl⟩ := Proofs.Exec.head_of rfl (by simp) hs
      obtain ⟨ws', us', t₁, t₂, rfl, hbt, hm, he⟩ := Step.tryTable_vals_inv hs'
      simp only [Config.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      have hFl : FragC (.handler t₂.length cs [.label t₂.length [] (vals us' ++ expression b)] ::
          code) := by
        intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact .handler (fun y hy => by
            simp at hy; subst hy
            exact .label (by simp) (frag_append.2 ⟨frag_vals _, frag_expression hb⟩))
        · exact hF' x hx
      have := DivFC.tryTable (P := P) (host := host) (C := C) (D := D) (R := DivInv P host G)
        (ws := ws ++ ws') (code := code) hbt hm ⟨hFl, by unfold Diverges; simpa using hd₁,
          by simpa using gt_steps hG (.single hs)⟩
      simpa using this
    | simple hk =>
      obtain ⟨s₁, f₁, vs₁, h₁, hd₁⟩ := atom_exit hk (hA s f vs i hk) hd
      exact .simple hk h₁ ⟨hF', hd₁, gt_steps hG (by simpa using steps_in [] code h₁)⟩
    | const h =>
      obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 h
      exact val_case v hv
    | @block _ bt b hb =>
      obtain ⟨⟨s₁, f₁, x₁⟩, hs, hd₁⟩ := hd.unfold
      obtain ⟨ws, us, is', rfl, hs', rfl⟩ := Proofs.Exec.head_of rfl (by simp) hs
      obtain ⟨ws', us', t₁, t₂, rfl, hbt, hm, he⟩ := Step.block_vals_inv hs'
      simp only [Config.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      have hFl : FragC (.label t₂.length [] (vals us' ++ expression b) :: code) := by
        intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact .label (by simp) (frag_append.2 ⟨frag_vals _, frag_expression hb⟩)
        · exact hF' x hx
      have := DivFC.block (P := P) (host := host) (C := C) (D := D) (R := DivInv P host G)
        (ws := ws ++ ws') (code := code) hbt hm ⟨hFl, by unfold Diverges; simpa using hd₁,
          by simpa using gt_steps hG (.single hs)⟩
      simpa using this
    | @loop _ bt b hb =>
      obtain ⟨⟨s₁, f₁, x₁⟩, hs, hd₁⟩ := hd.unfold
      obtain ⟨ws, us, is', rfl, hs', rfl⟩ := Proofs.Exec.head_of rfl (by simp) hs
      obtain ⟨ws', us', t₁, t₂, rfl, hbt, hm, he⟩ := Step.loop_vals_inv hs'
      simp only [Config.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      have hFl : FragC (.label t₁.length [.loop bt b] (vals us' ++ expression b) :: code) := by
        intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact .label (by simp [FragIB.loop hb]) (frag_append.2 ⟨frag_vals _, frag_expression hb⟩)
        · exact hF' x hx
      have := DivFC.loop (P := P) (host := host) (C := C) (D := D) (R := DivInv P host G)
        (ws := ws ++ ws') (code := code) hbt hm ⟨hFl, by unfold Diverges; simpa using hd₁,
          by simpa using gt_steps hG (.single hs)⟩
      simpa using this
    | @if_ _ bt t e ht he' =>
      obtain ⟨⟨s₁, f₁, x₁⟩, hs, hd₁⟩ := hd.unfold
      obtain ⟨ws, us, is', rfl, hs', rfl⟩ := Proofs.Exec.head_of rfl (by simp) hs
      obtain ⟨ws', k, rfl, he⟩ := Step.if_vals_inv hs'
      simp only [Config.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      have hFl : FragC (.plain (.block bt (if k = 0 then e else t)) :: code) := by
        intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · split
          · exact .plain (.block he')
          · exact .plain (.block ht)
        · exact hF' x hx
      have := DivFC.if_ (P := P) (host := host) (C := C) (D := D) (R := DivInv P host G)
        (ws := ws ++ ws') (k := k) (t := t) (e := e) (code := code)
        ⟨hFl, by unfold Diverges; simpa using hd₁,
          by simpa using gt_steps hG (.single hs)⟩
      simpa using this
    | @brData _ i hb =>
      obtain ⟨⟨s₁, f₁, x₁⟩, hs, hd₁⟩ := hd.unfold
      have hv : (Admin.plain i).val? = none := by cases i <;> simp_all [Instr.IsBrData, Admin.val?]
      have hnt : i ≠ .throwRef := by rintro rfl; simp [Instr.IsBrData] at hb
      obtain ⟨ws, us, is', rfl, hs', rfl⟩ := Proofs.Exec.head_of hv hnt hs
      obtain ⟨ws', us', us'', X, rfl, hB, he⟩ := Step.brData_vals_inv hb hs'
      simp only [Config.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      have hFl : FragC (X ++ code) := frag_append.2 ⟨(frag_append.1 (expand_br (P := P) (C := C)
        (host := host) (cf := true) hB).1).2, hF'⟩
      have := DivFC.brData (P := P) (host := host) (C := C) (D := D) (R := DivInv P host G)
        (ws := ws ++ ws') (code := code) hB ⟨hFl, by unfold Diverges; simpa using hd₁,
          by simpa using gt_steps hG (.single hs)⟩
      simpa using this
    | br l =>
      obtain ⟨c', hs, -⟩ := hd.unfold
      exact (br_stuck_seq hs).elim
    | return_ =>
      obtain ⟨c', hs, -⟩ := hd.unfold
      exact (ret_stuck_seq hs).elim
    | brIf l =>
      obtain ⟨⟨s₁, f₁, x₁⟩, hs, hd₁⟩ := hd.unfold
      obtain ⟨ws, us, is', rfl, hs', rfl⟩ := Proofs.Exec.head_of rfl (by simp) hs
      obtain ⟨ws', k, rfl, he⟩ := Step.brIf_vals_inv hs'
      simp only [Config.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      have hFl : FragC ((if k = 0 then [] else [.plain (.br l)]) ++ code) := by
        refine frag_append.2 ⟨?_, hF'⟩
        split
        · intro x hx; simp at hx
        · intro x hx; simp only [List.mem_singleton] at hx; subst hx; exact .plain (.br l)
      have := DivFC.brIf (P := P) (host := host) (C := C) (D := D) (R := DivInv P host G)
        (ws := ws ++ ws') (k := k) (l := l) (code := code) ⟨hFl, by unfold Diverges; simpa using hd₁,
          by simpa using gt_steps hG (.single hs)⟩
      simpa using this

/-! ## The call-free fragment as an instance -/

theorem fragIB_true {cf : Bool} {i : Instr} (h : FragIB cf i) : FragIB true i := by
  induction h with
  | simple h => exact .simple h
  | const h => exact .const h
  | block _ ih => exact .block ih
  | loop _ ih => exact .loop ih
  | if_ _ _ iht ihe => exact .if_ iht ihe
  | br l => exact .br l
  | brIf l => exact .brIf l
  | return_ => exact .return_
  | brData h => exact .brData h
  | throw x => exact .throw x
  | throwRef => exact .throwRef
  | tryTable _ ih => exact .tryTable ih
  | call x => exact .call x
  | callIndirect x y => exact .callIndirect x y
  | callRef y => exact .callRef y
  | returnCall x => exact .returnCall x
  | returnCallIndirect x y => exact .returnCallIndirect x y
  | returnCallRef y => exact .returnCallRef y

theorem fragAB_true {cf : Bool} {a : Admin} (h : FragAB cf a) : FragAB true a := by
  induction h with
  | val h => exact .val h
  | plain h => exact .plain (fragIB_true h)
  | trap => exact .trap
  | label hc _ ih => exact .label (fun i hi => fragIB_true (hc i hi)) ih
  | handler _ ih => exact .handler ih
  | retType d => exact .retType d

/-- Call-free fragment code holds no direct call, in any context. -/
theorem frag_fill_call : ∀ (E : Ctx) {W : List Val} {x : FuncIdx} {rest : List Admin},
    ¬ Frag (E.fill (vals W ++ .plain (.call x) :: rest))
  | .hole, W, x, rest, hF => by
    have h := hF (.plain (.call x)) (by simp [Ctx.fill])
    cases h with
    | val h => simp [Admin.val?] at h
    | plain h => cases h with
      | simple h => simp [SingleThreaded.Det.famOf] at h
      | const h => simp [Admin.val?] at h
      | brData h => simp [Instr.IsBrData] at h
  | .label ws n cont E r, W, x, rest, hF => by
    have h := hF (.label n cont (E.fill (vals W ++ .plain (.call x) :: rest))) (by simp [Ctx.fill])
    cases h with
    | val h => simp [Admin.val?] at h
    | label _ hi => exact frag_fill_call E hi
  | .handler ws n cs E r, W, x, rest, hF => by
    have h := hF (.handler n cs (E.fill (vals W ++ .plain (.call x) :: rest))) (by simp [Ctx.fill])
    cases h with
    | val h => simp [Admin.val?] at h
    | handler hi => exact frag_fill_call E hi

/-- Call-free fragment code holds no call of a function reference, in any context. -/
theorem frag_fill_callRef : ∀ (E : Ctx) {W : List Val} {a : Nat} {cr : Admin} {rest : List Admin},
    cr.IsCallRef → ¬ Frag (E.fill (vals W ++ .ref (.func a) :: cr :: rest))
  | .hole, W, a, cr, rest, hcr, hF => by
    obtain ⟨y, h1, -⟩ := fragA_callRef (hF cr (by simp [Ctx.fill])) hcr
    cases h1
  | .label ws n cont E r, W, a, cr, rest, hcr, hF => by
    have h := hF (.label n cont (E.fill (vals W ++ .ref (.func a) :: cr :: rest)))
      (by simp [Ctx.fill])
    cases h with
    | val h => simp [Admin.val?] at h
    | label _ hi => exact frag_fill_callRef E hcr hi
  | .handler ws n cs E r, W, a, cr, rest, hcr, hF => by
    have h := hF (.handler n cs (E.fill (vals W ++ .ref (.func a) :: cr :: rest)))
      (by simp [Ctx.fill])
    cases h with
    | val h => simp [Admin.val?] at h
    | handler hi => exact frag_fill_callRef E hcr hi

/-- A run of call-free fragment code reaches no call: any guard holds at every call. -/
theorem guardedCalls_frag {c₀ : Config H} (hF : Frag c₀.code) : GuardedCalls P host G c₀ :=
  fun _ E _ _ _ _ _ _ _ _ h₂ hc hcr => ((frag_fill_callRef E hcr) (hc ▸ frag_steps h₂ hF)).elim

/-- Call-free fragment code keeps its (absent) pending tail calls well placed. -/
theorem tailsOk_frag {c₀ : Config H} (hF : Frag c₀.code) : TailsOk P host c₀ :=
  fun _ h₂ => Proofs.Region.tailWF_of_frag (frag_steps h₂ hF)

/-- **Completeness for call-free divergence**: the instance of `div_completeC` with no call. -/
theorem div_complete {s : Store H} {f : Frame} {vs : List Val} {code : List Admin}
    (hA : AtomTerm P host) (hF : Frag code) (hd : Diverges P host ⟨s, f, vals vs ++ code⟩) :
    RunDiv P host s f vs code :=
  div_completeC (G := fun _ _ _ => False) hA (fun _ _ _ _ _ _ _ _ _ _ _ hg => hg.elim)
    (fun _ _ _ _ _ _ _ _ hg => hg.elim) (fun a ha => fragAB_true (hF a ha))
    (guardedCalls_frag (frag_append.2 ⟨frag_vals vs, hF⟩))
    (fun _ h₂ => Proofs.Region.tailWF_of_frag (frag_steps h₂ (frag_append.2 ⟨frag_vals vs, hF⟩)))
    hd

/-- **Adequacy for call-free divergence**, given the atomic obligation. -/
theorem div_adequate {s : Store H} {f : Frame} {vs : List Val} {code : List Admin}
    (hA : AtomTerm P host) (hF : Frag code) :
    RunDiv P host s f vs code ↔ Diverges P host ⟨s, f, vals vs ++ code⟩ :=
  ⟨div_sound, div_complete hA hF⟩

end Silmaril.Wasm.Cfg.Proofs.Region

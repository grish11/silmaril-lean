module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack.InfLoop

/-!
# Productive runs: the trees, calls and invocations (proofs)

* `inf_trees`: `InfG J es` for all trees, by induction on their size: the head tree runs
  productively alone (the head cases), or runs to values (`J.evRunN_back_vals`) and the trees after
  it go on (`head_consI`, `cont_typedH`).
* `callInf_step`: a typed call running productively (`CallInfX J`): its callee is a Wasm function
  (a host function answers its event and stops); entering its frame is its only step. Its body
  runs productively within the function (`InfLXP`), or reaches a call (a descent,
  `descends_reach`), or ends in a pending tail call, which leaves the frame at the tail callee's
  call (a descent, `descends_tailL`). Every other end of the body is a finished closed behaviour
  of the call, a Core run to a final form, ruled out by `noInf_of_evRun`. A descent without host
  call is a nonempty host-free run into a context around the next call.
* `callInf_closure`, by choice of the descents: the productive runs of a call are in
  `wasmEvInfNXP`: a productive run within a body after finitely many descents (`closeInfL`), or
  an infinite descent chain (`closeInf`), with unboundedly many host calls since infinitely many
  host-free descents in a row would be host-free divergence (`J.coreInf_not_diverges`).
* `coreInf_wasmEvInfNXP'`: a productive Core run of a typed invocation is in `wasmEvInfNXP`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Interp
open Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Abstract.CallXP (POut)
open Silmaril.Wasm.Binaryen (BExpr liftInstrs)
open Shape (streamAppend)

variable {H : Type} {tags : List TagInst} {o : GrowOracle} {host : HostSemantics H} {J : Silmaril.Wasm.Interp.BackInv H}

/-! ## Trees -/

/-- **The productive backward simulation of trees**, by induction on their size. -/
theorem inf_trees (hT : J.HostOk host) (hH : HostSliceT host) (hE : HostSliceE tags host) :
    ∀ es, InfG J tags o host es := by
  intro es
  induction hsz : sizeOf es using Nat.strong_induction_on generalizing es with
  | _ k ihk =>
  have ih : ∀ es', sizeOf es' < sizeOf es → InfG J tags o host es' :=
    fun es' h => ihk _ (hsz ▸ h) es' rfl
  intro s f stk ω ht hdv
  rcases es with _ | ⟨e, es⟩
  · refine (coreInf_no_step (fun c' h => ?_) hdv).elim
    exact Sim.Step.not_vals (by simpa [pcfg, xcode, expression] using h)
  have hX : (pcfg s f stk (e :: es) : Config H) =
      ⟨s, f, xcode stk [e] ++ expression (Binaryen.BExpr.lowerList es)⟩ := by
    simp only [pcfg, xcode_cons_eq]
  rw [hX] at hdv
  rcases coreInf_split_seq hdv with hdh | ⟨cs₁, ω₂, ⟨s₂, f₂, k₂⟩, n₁, ws, rfl, hr₁, hw, hd₁⟩
  · rcases e with ⟨i, args⟩ | ⟨bt, body⟩ | ⟨bt, body⟩ | ⟨bt, c, t, el⟩ | ⟨bt, cl, body⟩
    · exact headInf_op hT hH hE (ih _ size_args) ht hdh
    · exact headInf_block hT hH hE (ih _ size_block) ht hdh
    · exact headInf_loop hT hH hE (ih _ size_loop) ht hdh
    · exact headInf_if hT hH hE (ih _ size_cond) (fun b => ih _ (size_arm b)) ht hdh
    · exact headInf_try hT hH hE (ih _ size_try) ht hdh
  dsimp only at hw hd₁
  subst hw
  obtain ⟨l₁, stk₂, hd, hq, rfl⟩ := J.evRunN_back_vals hT hH hE (typedP_head ht) hr₁
  have hcons := consistent_of_coreInf hdv
  have hst : Steps (profile o) host (pcfg s f stk (e :: es)) (pcfg s₂ f₂ stk₂ es) := by
    rw [hX]
    exact Steps.append _ (evRunN_steps hr₁)
  have htk := cont_typedH hT hH hE ht hd hq hcons hst
  refine infOut_lift (head_consI hd es) (head_cons hd es).2 hq (fun h0 => ⟨_, lifts_id, ?_⟩)
    (ih es size_tail s₂ f₂ stk₂ ω₂ htk hd₁)
  subst h0
  rw [hX]
  exact (lifts_suffix (o := o) _).rtg (evRunN_nil_dsteps hr₁)

/-! ## Calls -/

/-- **At a host call** the first event of a productive run answers it, and the run goes on. -/
theorem coreInf_at_host {P : Numerics.Profile} {K : Config H} {x : Ctx × Nat × H × List Val}
    {ω : Nat → Call (wasmHostSig H)} (hdK : decompose? K.store K.code = some x)
    (h : CoreInf P host K ω) :
    ∃ K₁, HEvStep P host K (some (ω 0)) K₁ ∧ CoreInf P host K₁ (fun k => ω (k + 1)) := by
  obtain ⟨g, hg0, hg⟩ := h
  obtain ⟨c₁, hs, he⟩ := hg 0
  rw [hg0] at hs
  obtain ⟨k, hk⟩ := silent_evRunN' hs
  obtain rfl := evRunN_nil_at_host hdK hk
  exact ⟨g 1, he, fun n => g (n + 1), rfl, fun n => hg (n + 1)⟩

/-- **One step of the productive run of a call**: within the callee's body, or a descent to the
next call running productively. -/
def CallStepOut (J : Silmaril.Wasm.Interp.BackInv H) (tags : List TagInst) (o : GrowOracle) (host : HostSemantics H)
    (z : (wasmOShape H).self.Op) (K : Config H) (ω : Nat → Call (wasmHostSig H)) : Prop :=
  (∃ (fi : FuncInst H) (fn : Func) (ν : Nat → OCall H), z.2.2.funcs[z.1]? = some fi ∧
    fi.code = .wasm fn ∧
    InfLXP z.2.2 (Frame.forCall fi.module z.2.1 fn.locals) [] (liftInstrs fn.body) ν ∧
    Shape.SubstInf Cl (fun i => (ν i).lift) ω) ∨
  ∃ (z' : (wasmOShape H).self.Op) (K' : Config H) (q : List (Call (wasmHostSig H)))
    (ω' : Nat → Call (wasmHostSig H)), Shape.Descends wasmHOpenXP Cl z q z' ∧
    CallInfX J tags o host z' K' ω' ∧ ω = q ++ω ω' ∧
    (q = [] → ∃ W, Lifts o W ∧ Relation.TransGen (Det.DStep o) K (W K'))

/-- **The productive run of a typed call, one step.** -/
theorem callInf_step (hT : J.HostOk host) (hH : HostSliceT host) (hE : HostSliceE tags host)
    {z : (wasmOShape H).self.Op} {K : Config H} {ω : Nat → Call (wasmHostSig H)}
    (h : CallInfX J tags o host z K ω) : CallStepOut J tags o host z K ω := by
  obtain ⟨a, us, s⟩ := z
  obtain ⟨f, pre, cr, hcr, rfl, hcc, hct, hdv⟩ := h
  obtain ⟨hS, hts, fi, ps, rs, hfi, hty, hn⟩ := id hcc
  obtain ⟨ps', rs', hex, hpl, hrl⟩ := expand_of_funcType hty
  have hn' : us.length = ps'.length := hn.trans hpl.symm
  cases hcode : fi.code with
  | host hh =>
    exfalso
    have hd : decompose? s (Interp.callCode pre us a cr []) = some (.top pre [], a, hh, us) := by
      have := decompose?_wrap (s := s) pre [] (decompose?_redex hcr hfi hex hn' hcode)
      simpa [Ctx.wrap, Interp.callCode] using this
    obtain ⟨K₁, he, hd₁⟩ := coreInf_at_host (K := ⟨s, f, Interp.callCode pre us a cr []⟩) hd hdv
    generalize ω 0 = e at he
    obtain ⟨⟨hh', s₀, us'⟩, ⟨s', r⟩⟩ := e
    obtain ⟨E, a', hd', hs₀, hans, rfl⟩ := he
    dsimp only at hd' hs₀ hans
    rw [hd] at hd'
    simp only [Option.some.injEq, Prod.mk.injEq] at hd'
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hd'
    subst hs₀
    rcases r with ws | t | _
    · refine coreInf_no_step (fun c' h => ?_) hd₁
      have h' : Step (profile o) host ⟨s', f, vals (pre ++ ws)⟩ c' := by
        simpa [Ctx.fill, Result.toAdmin, vals] using h
      exact Sim.Step.not_vals h'
    · exact coreInf_throw_head (ws := pre) (x := t) (r := [])
        (by simpa [Ctx.fill, Result.toAdmin] using hd₁)
    · exact coreInf_trap_head (ws := pre) (r := []) (by simpa [Ctx.fill, Result.toAdmin] using hd₁)
  | wasm fn =>
    let F := Frame.forCall fi.module us fn.locals
    have hcodeB : xcode [] (liftInstrs fn.body) = expression fn.body := by
      simp [xcode, Binaryen.lowerList_liftInstrs, vals]
    have hstep : Step (profile o) Det.noHost ⟨s, f, Interp.callCode pre us a cr []⟩
        ⟨s, f, vals pre ++ [.frame rs.length F [.label rs.length [] (xcode [] (liftInstrs fn.body))]] ++
          []⟩ := by
      rw [hcodeB, ← hrl]
      exact Silmaril.Wasm.Logic.Core.Step.ctx pre [] (Step.callRefFunc hcr hfi hex hn' hcode)
    have hdK := coreInf_through_dsteps (.single hstep) hdv
    have htK := J.steps hct (.single hstep)
    have hctB : J.TypedP tags s F [] (liftInstrs fn.body) :=
      J.callee_typedP ⟨hcc, f, cr, pre, [], hcr, hct⟩ hfi hcode
    rcases coreInf_split_frame hdK with hdb | ⟨cs₁, ω₂, cb, N₁, rfl, hb, hsb, hdc, hd₄⟩
    · -- the body runs productively
      rcases inf_trees hT hH hE _ s F [] ω hctB hdb with ⟨ν, hν, hs⟩ |
          ⟨l, z', q, K', ω', hr, hq, hci, rfl, hl⟩
      · exact .inl ⟨fi, fn, ν, hfi, hcode, hν, hs⟩
      · refine .inr ⟨z', K', q, ω', descends_reach hfi hcode hty hr hq, hci, rfl, fun h0 => ?_⟩
        obtain ⟨W, hW, hrt⟩ := hl h0
        exact ⟨_, (lifts_frame f pre rs.length []).comp hW,
          tg_trans_rtg (.single hstep) ((lifts_frame (o := o) f pre rs.length []).rtg hrt)⟩
    -- the body ends
    obtain ⟨l, ⟨s', f₂, ob⟩, hd, hres, hok⟩ := J.evRunN_back hT hH hE hctB hb hsb hdc
    have hcons₁ := consistent_of_coreInf hdv
    obtain ⟨ob₀, hbc⟩ := body_chkP (tags := tags) hS hfi hcode hty hn
    have hstB : Steps (profile o) host ⟨s, f, Interp.callCode pre us a cr []⟩
        ⟨cb.store, f, vals pre ++ [.frame rs.length cb.frame [.label rs.length [] cb.code]] ++
          []⟩ :=
      (Relation.ReflTransGen.single (Step.of_noHost host hstep)).trans
        (Steps.ctx pre [] (Steps.frame rs.length (Steps.label rs.length [] (evRunN_steps hb))))
    have hctX := J.steps_host hT hct hstB
    have hfin : ∀ e : End (Store H) (List Val ⊕ Nat), (cs₁, e) ∈ wasmEvFunXP s (a, us) →
        False := by
      intro e he
      obtain ⟨s'', code, oc, hend, hrun⟩ :=
        wasmEvFunXP_evRun_call (P := profile o) hH hE he hcons₁ hts hS hfi hty hn f cr hcr
      obtain ⟨X, hX, hXs⟩ := final_of_ends (P := profile o) hend s'' f pre
      have hrun' : EvRun (profile o) host ⟨s, f, Interp.callCode pre us a cr []⟩ cs₁ X := by
        have h1 := evRun_ctx pre [] hrun
        simp only [List.append_nil] at h1
        have := evRun_trans h1 (evRun_of_free (host := host) hX)
        simpa [Interp.callCode] using this
      exact noInf_of_evRun hrun' (hXs host) hdv
    rcases hres with hq | ⟨htr, l₁, l₂, g, args, s₁, b, s₂, q₁, c₁, rfl, hq₁, hct₁, hcs₁⟩
    swap
    · -- cut at a trapping callee
      exfalso
      simp only at htr
      subst htr hcs₁
      refine hfin .trap ?_
      refine close_of_open' (.inl ⟨fi, fn, ps, rs, s', f₂, .trap, .trap, _, hfi, hcode, hty, hd,
        rfl, rfl⟩) ?_
      rw [List.map_append, List.map_cons]
      exact subst_of_pre_then hq₁ (Shape.Subst.intTrap (rest := l₂.map OCall.lift) (ans := (b, s₂))
        hct₁)
    obtain ⟨hev, -⟩ := evalLXPh_evRun (P := profile o) hH hE hd hq hcons₁
    obtain ⟨t₁, hA, -⟩ := Silmaril.Wasm.Interp.HostEvalP.evalOXP_host_good (P := profile o) hH hE
      hev hts
    obtain ⟨hpo, hinv, htw⟩ := hA hS hbc
    cases ob with
    | flow bfl =>
      exfalso
      obtain ⟨fl, hxf⟩ : ∃ fl, exitFlow rs.length bfl = some fl := by
        rcases bfl with w | ⟨_ | k, w⟩ | w | _ | t
        · exact ⟨_, rfl⟩
        · exact ⟨_, rfl⟩
        · obtain ⟨k', hk', -⟩ := hpo
          simp at hk'
        · exact ⟨_, rfl⟩
        · exact ⟨_, rfl⟩
        · exact ⟨_, rfl⟩
      exact hfin _ (close_of_open' (.inl ⟨fi, fn, ps, rs, s', f₂, bfl, fl, l, hfi, hcode, hty, hd,
        hxf, rfl⟩) (subst_of_pre hq _))
    | tail a' args k =>
      have hkr : k = rs.length := hpo
      subst hkr
      obtain ⟨fi₂, ps₂, rs₂, hfi₂, hty₂, hargs, -⟩ := htw a' args rs.length rfl
      obtain ⟨ps₂', rs₂', hex₂, hpl₂, -⟩ := expand_of_funcType hty₂
      rcases hok with ⟨oc, he, hm'⟩ | ⟨h, -⟩
      swap
      · cases h
      obtain ⟨vs₁, c₀, rfl, hc₀, hs', -⟩ := matchP_tail_iff.mp hm'
      obtain ⟨-, rest₀, hcb⟩ := he
      have hex' := frame_tail_exit (P := profile o) (host := NH) (s := cb.store) (f := f)
        (k := rs.length) (F := cb.frame) (vs₁ := vs₁) (rest := rest₀) hc₀ (hs' ▸ hfi₂) hex₂
        (hargs.trans hpl₂.symm)
      rw [← hcb] at hex'
      have hst := Steps.ctx pre [] hex'
      have hd₅ := coreInf_through_dsteps hst hd₄
      have hcc₂ : CallChkP tags s' a' args :=
        ⟨storeChk_inv hinv hS, t₁, fi₂, ps₂, rs₂, hfi₂, hty₂, hargs⟩
      have hK' : (⟨cb.store, f, vals pre ++ (vals args ++
          [.ref (.func a'), c₀.retToCallIn cb.frame.module]) ++ []⟩ : Config H) =
          ⟨s', f, Interp.callCode pre args a' (c₀.retToCallIn cb.frame.module) []⟩ := by
        rw [hs']
      have hct₂ : J.CT ⟨s', f,
          Interp.callCode pre args a' (c₀.retToCallIn cb.frame.module) []⟩ := by
        rw [← hK']
        exact J.steps_host hT hctX (steps_host hst)
      have hd₆ : CoreInf (profile o) host ⟨s', f,
          Interp.callCode pre args a' (c₀.retToCallIn cb.frame.module) []⟩ ω₂ := by
        rw [← hK']
        exact hd₅
      refine .inr ⟨⟨a', (args, s')⟩, _, cs₁, ω₂, descends_tailL hfi hcode hty hd hq,
        ⟨f, pre, _, isCallRef_retToCallIn hc₀ _, rfl, hcc₂, hct₂, hd₆⟩, rfl, fun h0 => ?_⟩
      subst h0
      refine ⟨_, lifts_id, ?_⟩
      have hin := (lifts_frame (o := o) f pre rs.length []).rtg (evRunN_nil_dsteps hb)
      have := tg_trans_rtg (.single hstep) (hin.trans hst)
      rw [hK'] at this
      exact this

/-! ## The closure -/

/-- **The productive runs of a typed call are in `wasmEvInfNXP`**, by choice of the descents. -/
theorem callInf_closure (hT : J.HostOk host) (hH : HostSliceT host)
    (hE : HostSliceE tags host) (z : (wasmOShape H).self.Op) (K : Config H)
    (ω : Nat → Call (wasmHostSig H)) (hz : CallInfX J tags o host z K ω) :
    ω ∈ wasmEvInfNXP z.2.2 (z.1, z.2.1) := by
  classical
  by_contra hno
  let Good : (wasmOShape H).self.Op × Config H × (Nat → Call (wasmHostSig H)) → Prop := fun p =>
    CallInfX J tags o host p.1 p.2.1 p.2.2 ∧ p.2.2 ∉ wasmEvInfNXP p.1.2.2 (p.1.1, p.1.2.1)
  have step : ∀ p : {p // Good p}, ∃ (p' : {p // Good p}) (q : List (Call (wasmHostSig H))),
      Shape.Descends wasmHOpenXP Cl p.1.1 q p'.1.1 ∧ p.1.2.2 = q ++ω p'.1.2.2 ∧
      (q = [] → ∃ W, Lifts o W ∧ Relation.TransGen (Det.DStep o) p.1.2.1 (W p'.1.2.1)) := by
    rintro ⟨⟨y, K, ω⟩, hy, hnq⟩
    rcases callInf_step hT hH hE hy with ⟨fi, fn, ν, hf, hc, hν, hs⟩ |
        ⟨z', K', q, ω', hD, hz', rfl, hl⟩
    · exact (hnq (Shape.mem_closeInfL_of_open ⟨fi, fn, ν, hf, hc, hν, rfl⟩ hs)).elim
    · exact ⟨⟨⟨z', K', ω'⟩, hz', fun hq => hnq (Shape.closeInfL_descends hD hq)⟩, q, hD, rfl, hl⟩
  choose nx q hD hω hlink using step
  let G : Nat → {p // Good p} := fun n => nx^[n] ⟨(z, K, ω), hz, hno⟩
  have hG : ∀ n, G (n + 1) = nx (G n) := fun n => Function.iterate_succ_apply' nx n _
  have hfreq : ∀ N, ∃ n, N ≤ n ∧ q (G n) ≠ [] := by
    intro N
    by_contra hall
    push Not at hall
    have hL : ∀ k, ∃ W : Config H → Config H, Lifts o W ∧ Relation.TransGen (Det.DStep o)
        (G (N + k)).1.2.1 (W (G (N + k + 1)).1.2.1) := by
      intro k
      obtain ⟨W, hW, htg⟩ := hlink (G (N + k)) (hall _ (Nat.le_add_right _ _))
      rw [← hG] at htg
      exact ⟨W, hW, htg⟩
    choose W hW htg using hL
    let Φ : Nat → Config H → Config H := fun k => Nat.rec (fun c => c) (fun k Φk c => Φk (W k c)) k
    have hΦ : ∀ k, Lifts o (Φ k) := by
      intro k
      induction k with
      | zero => exact lifts_id
      | succ k ihk => exact ihk.comp (hW k)
    have hdiv := trace_of_tgChain (R := Det.DStep o)
      (x := fun k => Φ k (G (N + k)).1.2.1) (fun k => (hΦ k).tg (htg k))
    obtain ⟨-, -, -, -, -, -, hct, hd⟩ := (G N).2.1
    exact J.coreInf_not_diverges hct hdiv hd
  have hchainω : ∀ n, (G n).1.2.2 = q (G n) ++ω (G (n + 1)).1.2.2 := fun n => by
    rw [hG]; exact hω (G n)
  have hcsω := Shape.streamConcat_of_chain (w := fun n => (G n).1.2.2) hchainω
    (Shape.unbounded_of_frequently _ hfreq)
  refine hno (Shape.closeInf_subset_closeInfL _ _ _ _ _
    ⟨fun n => (G n).1.1, fun n => q (G n), rfl, fun n => ?_, hcsω.1, hcsω.2⟩)
  have := hD (G n)
  rw [← hG] at this
  exact this

/-! ## Invocations -/

/-- **A productive Core run of a typed invocation is in `wasmEvInfNXP`** (deterministic
profile). -/
theorem coreInf_wasmEvInfNXP' (hT : J.HostOk host) (hH : HostSliceT host)
    (hE : HostSliceE tags host) {s : Store H} {a : Nat} {vs : List Val} (hct₀ : J.CT (invoke s a vs))
    (hS : StoreChkE (ehExt tags) s.funcs) (hts : TagsOk tags s) (hok : InvokeOk s a vs)
    {ω : Nat → Call (wasmHostSig H)} (h : CoreInf (profile o) host (invoke s a vs) ω) :
    ω ∈ wasmEvInfNXP s (a, vs) := by
  have hct := J.invoke_callTyped hct₀ hok hS hts
  obtain ⟨⟨-, -, fi, ps, rs, hfi, hty, hlen⟩, -⟩ := id hct
  have hctx := hct₀
  have hinv : invoke s a vs = ⟨s, {}, Interp.callCode [] vs a (.callRefType fi.type) []⟩ := by
    rw [invoke_eqP hfi]; simp [Interp.callCode, vals]
  rw [hinv] at h hctx
  exact callInf_closure hT hH hE ⟨a, (vs, s)⟩ _ ω
    ⟨{}, [], .callRefType fi.type, trivial, rfl, hct.1, hctx, h⟩

end Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack

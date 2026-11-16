module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack.DivBase

/-!
# Divergence after a nonempty log: the statements and calls (proofs)

In the deterministic profile `SingleThreaded.profile o`, for a host with typed answers in the
host slices (`HostTyped`, `NativeHostSlice`, `HostSliceE tags`):

* `DivOut s f stk es cs`: the trees perform logged calls resolving to exactly `cs` and then
  diverge host-free (`LogDivXP`), or reach a call after a resolved prefix `q` whose callee
  diverges after the rest `q'` in `wasmEvFunDXP`;
* `DivG n es`: a typed problem whose Core run makes the host events `cs` and then diverges
  host-free, cut at its last event within `n` steps (`EvDiv`), is `DivOut`;
* `CallDivG n`: the same for a typed call in any `call_ref` form under values, with nothing
  after it: the call diverges after `cs` in `wasmEvFunDXP`.

`callDiv_step`: `CallDivG n` from `DivG m` and `CallDivG m` for `m < n`. With no event, the call
diverges host-free, so `FunDivXP` (`funDivXP_of_call_diverges`, `div_of_funDivXP`). A host callee
answers its event and stops. A Wasm callee's only step enters its frame, strictly shorter with
events; its body diverges (a descent, `DivG`), or ends: a pending tail call leaves the frame at the
tail callee's call (`frame_tail_exit`, `CallDivG` on the rest, a descent), and every other end is
a finished closed behaviour of the call (`wasmEvFunXP_evRun_call`), a Core run to a final form,
which does not diverge (`noDiv_of_evRun`).
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

variable {H : Type}

/-! ## The statements -/

/-- **Divergence of trees after the host events `cs`**: logged host-free divergence with exactly
that log, or a reached call after a resolved prefix whose callee diverges after the rest. -/
def DivOut (s : Store H) (f : Frame) (stk : List Val) (es : List BExpr)
    (cs : List (Call (wasmHostSig H))) : Prop :=
  (∃ l, LogDivXP s f stk es l ∧ Shape.SubstPre Cl (l.map OCall.lift) cs) ∨
    ∃ (l : List (OCall H)) (z : (wasmOShape H).self.Op) (q q' : List (Call (wasmHostSig H))),
      ReachLXP s f stk es l z ∧ Shape.SubstPre Cl (l.map OCall.lift) q ∧
      (q', .div) ∈ wasmEvFunDXP z.2.2 (z.1, z.2.1) ∧ cs = q ++ q'

/-- **The divergent backward simulation of trees**, for divergences cut within `n` steps. -/
def DivG (tags : List TagInst) (o : GrowOracle) (host : HostSemantics H) (n : Nat)
    (es : List BExpr) : Prop :=
  ∀ (s : Store H) (f : Frame) (stk : List Val) (cs : List (Call (wasmHostSig H))),
    TypedP tags s f stk es → EvDiv (profile o) host n ⟨s, f, xcode stk es⟩ cs →
    DivOut s f stk es cs

/-- **The divergent backward simulation of calls**, for divergences cut within `n` steps. -/
def CallDivG (tags : List TagInst) (o : GrowOracle) (host : HostSemantics H) (n : Nat) : Prop :=
  ∀ (s : Store H) (f : Frame) (pre us : List Val) (a : Nat) (cr : Admin)
    (cs : List (Call (wasmHostSig H))), cr.IsCallRef → CallChkP tags s a us →
    Sim.ContextTyped ⟨s, f, Interp.callCode pre us a cr []⟩ →
    EvDiv (profile o) host n ⟨s, f, Interp.callCode pre us a cr []⟩ cs →
    (cs, .div) ∈ wasmEvFunDXP s (a, us)

/-! ## Glue -/

theorem divOut_lift {s s' : Store H} {f f' : Frame} {stk stk' : List Val} {es es' : List BExpr}
    {l₀ : List (OCall H)} {q₀ cs : List (Call (wasmHostSig H))}
    (hd : ∀ l, LogDivXP s' f' stk' es' l → LogDivXP s f stk es (l₀ ++ l))
    (hr : ∀ l z, ReachLXP s' f' stk' es' l z → ReachLXP s f stk es (l₀ ++ l) z)
    (h₀ : Shape.SubstPre Cl (l₀.map OCall.lift) q₀) (h : DivOut s' f' stk' es' cs) :
    DivOut s f stk es (q₀ ++ cs) := by
  rcases h with ⟨l, hl, hq⟩ | ⟨l, z, q, q', hz, hq, hd', rfl⟩
  · exact .inl ⟨l₀ ++ l, hd l hl, by rw [List.map_append]; exact substPre_append' h₀ hq⟩
  · exact .inr ⟨l₀ ++ l, z, q₀ ++ q, q', hr l z hz,
      by rw [List.map_append]; exact substPre_append' h₀ hq, hd', by simp⟩

theorem divOut_lift₀ {s s' : Store H} {f f' : Frame} {stk stk' : List Val} {es es' : List BExpr}
    {cs : List (Call (wasmHostSig H))}
    (hd : ∀ l, LogDivXP s' f' stk' es' l → LogDivXP s f stk es l)
    (hr : ∀ l z, ReachLXP s' f' stk' es' l z → ReachLXP s f stk es l z)
    (h : DivOut s' f' stk' es' cs) : DivOut s f stk es cs := by
  simpa using divOut_lift (l₀ := []) (q₀ := []) (fun l h => by simpa using hd l h)
    (fun l z h => by simpa using hr l z h) .nil h

variable {tags : List TagInst} {o : GrowOracle} {host : HostSemantics H}

/-- **With no event**, host-free divergence: logged divergence with the empty log. -/
theorem divOut_nil {n : Nat} {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    (ht : TypedP tags s f stk es) (h : EvDiv (profile o) host n ⟨s, f, xcode stk es⟩ []) :
    DivOut s f stk es [] :=
  .inl ⟨[], .div (evalDivXP_of_diverges ht (evDiv_nil h)), .nil⟩

/-- **The divergence of a callee's body is that of the call.** -/
theorem callDiv_of_body {s : Store H} {a : Nat} {us : List Val} {fi : FuncInst H} {fn : Func}
    {ps rs : List Validation.CValType} {cs : List (Call (wasmHostSig H))}
    (hf : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (h : DivOut s (Frame.forCall fi.module us fn.locals) [] (liftInstrs fn.body) cs) :
    (cs, .div) ∈ wasmEvFunDXP s (a, us) := by
  rcases h with ⟨l, hl, hq⟩ | ⟨l, z, q, q', hr, hq, hz, rfl⟩
  · exact div_logDiv hf hcode hl hq
  · exact div_descend (x := ⟨a, (us, s)⟩) (descends_reach hf hcode hty hr hq) hz

theorem subst_of_pre {L : List (HCall H)} {q : List (Call (wasmHostSig H))}
    (h : Shape.SubstPre Cl L q) (e : End (Store H) (List Val ⊕ Nat)) :
    Shape.Subst Cl L e (q, e) := by
  induction h with
  | nil => exact .nil (c := Cl) e
  | ext _ ih => exact .ext ih
  | int hc _ ih => exact .int hc ih

theorem subst_of_pre_then {L M : List (HCall H)} {q : List (Call (wasmHostSig H))}
    {e : End (Store H) (List Val ⊕ Nat)} {y : CallBeh (wasmHostSig H) (Store H) (List Val ⊕ Nat)}
    (h : Shape.SubstPre Cl L q) (hm : Shape.Subst Cl M e y) :
    Shape.Subst Cl (L ++ M) e (q ++ y.1, y.2) := by
  induction h with
  | nil => simpa using hm
  | ext _ ih => exact .ext ih
  | int hc _ ih =>
    rw [List.cons_append, List.append_assoc]
    exact Shape.Subst.int hc ih

/-- **Entering a Wasm callee is the only step of a `call_ref` form on exactly its arguments.** -/
theorem callRef_wasm_unique {P : Numerics.Profile} {s : Store H} {f : Frame} {pre us : List Val}
    {a : Nat} {cr : Admin} {rest : List Admin} {fi : FuncInst H} {fn : Func}
    {ps rs : Validation.Ty (.list .val)} {c₁ : Config H} (hcr : cr.IsCallRef)
    (hf : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (hex : Validation.Expand fi.type (.func ps rs)) (hn : us.length = ps.length)
    (h : Step P host ⟨s, f, Interp.callCode pre us a cr rest⟩ c₁) :
    c₁ = ⟨s, f, vals pre ++ [.frame rs.length (Frame.forCall fi.module us fn.locals)
      [.label rs.length [] (expression fn.body)]] ++ rest⟩ := by
  have e : Interp.callCode pre us a cr rest = vals (pre ++ us) ++ .ref (.func a) :: cr :: rest := by
    simp [Interp.callCode]
  rw [e] at h
  obtain ⟨vs₁, vs₂, ps', rs', hsplit, he, hn', rfl⟩ := Step.callRef_wasm_inv_seq hcr hf hcode h
  have := (Validation.Expand.iff.1 hex).symm.trans (Validation.Expand.iff.1 he)
  simp only [Option.some.injEq, Validation.Ty.func.injEq] at this
  obtain ⟨rfl, rfl⟩ := this
  obtain ⟨rfl, rfl⟩ := List.append_inj' hsplit (hn.trans hn'.symm)
  simp

/-! ## Calls -/

/-- **The divergent backward simulation of a call**, from the statements for strictly shorter
divergences. -/
theorem callDiv_step (hT : HostTyped host) (hH : NativeHostSlice host) (hE : HostSliceE tags host)
    {n : Nat} (ihB : ∀ m < n, ∀ es, DivG tags o host m es) (ihC : ∀ m < n, CallDivG tags o host m) :
    CallDivG tags o host n := by
  intro s f pre us a cr cs hcr hcc hct hdv
  obtain ⟨hS, hts, fi, ps, rs, hfi, hty, hn⟩ := id hcc
  by_cases hcs : cs = []
  · subst hcs
    exact div_of_funDivXP (x := ⟨a, (us, s)⟩) ⟨fi, ps, rs, hfi, hty⟩
      (funDivXP_of_call_diverges hcr hcc hct (evDiv_nil hdv))
  obtain ⟨ps', rs', hex, hpl, hrl⟩ := expand_of_funcType hty
  have hn' : us.length = ps'.length := hn.trans hpl.symm
  have hcons : (coreHostRel host).Consistent cs := evDiv_consistent hdv
  cases hcode : fi.code with
  | host hh =>
    exfalso
    have hd : decompose? s (Interp.callCode pre us a cr []) = some (.top pre [], a, hh, us) := by
      have := decompose?_wrap (s := s) pre [] (decompose?_redex hcr hfi hex hn' hcode)
      simpa [Ctx.wrap, Interp.callCode] using this
    obtain ⟨e, rest, K₁, m, rfl, he, hd₁⟩ :=
      evDiv_at_host (K := ⟨s, f, Interp.callCode pre us a cr []⟩) hd hdv
    obtain ⟨⟨hh', s₀, us'⟩, ⟨s', r⟩⟩ := e
    obtain ⟨E, a', hd', hs₀, hans, rfl⟩ := he
    dsimp only at hd' hs₀ hans
    rw [hd] at hd'
    simp only [Option.some.injEq, Prod.mk.injEq] at hd'
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hd'
    subst hs₀
    rcases r with ws | t | _
    · refine evDiv_stuck (fun c' h => ?_) hd₁
      have h' : Step (profile o) host ⟨s', f, vals (pre ++ ws)⟩ c' := by
        simpa [Ctx.fill, Result.toAdmin, vals] using h
      exact Sim.Step.not_vals h'
    · exact hH.noThrow _ _ _ _ _ hans
    · exact evDiv_trap (ws := pre) (r := []) (by simpa [Ctx.fill, Result.toAdmin] using hd₁)
  | wasm fn =>
    let F := Frame.forCall fi.module us fn.locals
    have hstep : Step (profile o) Det.noHost ⟨s, f, Interp.callCode pre us a cr []⟩
        ⟨s, f, vals pre ++ [.frame rs'.length F [.label rs'.length [] (expression fn.body)]] ++
          []⟩ :=
      Silmaril.Wasm.Logic.Core.Step.ctx pre [] (Step.callRefFunc hcr hfi hex hn' hcode)
    obtain ⟨m, hm, hd₁⟩ := evDiv_unique (fun c₁ h => callRef_wasm_unique hcr hfi hcode hex hn' h)
      hstep hcs hdv
    have htK := hct.steps (.single hstep)
    rw [hrl] at hd₁ htK
    have hctB : TypedP tags s F [] (liftInstrs fn.body) :=
      callee_typedP ⟨hcc, f, cr, pre, [], hcr, hct⟩ hfi hcode
    have hcodeB : xcode [] (liftInstrs fn.body) = expression fn.body := by
      simp [xcode, Binaryen.lowerList_liftInstrs, vals]
    rcases evDiv_frame_seq_split hd₁ with hdb |
        ⟨cb, N₁, mm, cs₁, cs₂, rfl, hmm, hb, hsb, hdc, hd₄⟩
    · -- the body diverges: a descent
      exact callDiv_of_body hfi hcode hty (ihB m hm _ s F [] _ hctB (by rw [hcodeB]; exact hdb))
    -- the body ends
    have hb' : EvRunN (profile o) host N₁ ⟨s, F, xcode [] (liftInstrs fn.body)⟩ cs₁ cb := by
      rw [hcodeB]; exact hb
    obtain ⟨l, ⟨s', f₂, ob⟩, hd, hres, hok⟩ := evRunN_back hT hH hE hctB hb' hsb hdc
    have hcons₁ := (consistent_append hcons).1
    obtain ⟨ob₀, hbc⟩ := body_chkP (tags := tags) hS hfi hcode hty hn
    have hstB : Steps (profile o) host ⟨s, f, Interp.callCode pre us a cr []⟩
        ⟨cb.store, f, vals pre ++ [.frame rs.length cb.frame [.label rs.length [] cb.code]] ++
          []⟩ := by
      refine (Relation.ReflTransGen.single (Step.of_noHost host hstep)).trans ?_
      rw [hrl]
      exact Steps.ctx pre [] (Steps.frame rs.length (Steps.label rs.length [] (evRunN_steps hb)))
    have hctX := ContextTyped.steps_typed hT hct hstB
    -- a finished closed behaviour of the call rules the divergence out
    have hfin : ∀ e : End (Store H) (List Val ⊕ Nat), (cs₁, e) ∈ wasmEvFunXP s (a, us) → False := by
      intro e he
      obtain ⟨s'', code, oc, hend, hrun⟩ :=
        wasmEvFunXP_evRun_call (P := profile o) hH hE he hcons₁ hts hS hfi hty hn f cr hcr
      obtain ⟨X, hX, hXs⟩ := final_of_ends (P := profile o) hend s'' f pre
      have hrun' : EvRun (profile o) host ⟨s, f, Interp.callCode pre us a cr []⟩ (cs₁ ++ []) X := by
        have h1 := evRun_ctx pre [] hrun
        simp only [List.append_nil] at h1
        have := evRun_trans h1 (evRun_of_free (host := host) hX)
        simpa [Interp.callCode] using this
      exact noDiv_of_evRun hT hrun' (hXs host) hct (q' := cs₂) (by simpa using hdv)
    rcases hres with hq | ⟨htr, l₁, l₂, g, args, s₁, b, s₂, q₁, c₁, rfl, hq₁, hct₁, hcs₁⟩
    swap
    · -- cut at a trapping callee
      simp only at htr
      subst htr hcs₁
      refine (hfin .trap ?_).elim
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
      have hd₅ := evDiv_through_steps hst hctX hd₄
      have hcc₂ : CallChkP tags s' a' args :=
        ⟨storeChk_inv hinv hS, t₁, fi₂, ps₂, rs₂, hfi₂, hty₂, hargs⟩
      have hct₂ : Sim.ContextTyped ⟨s', f,
          Interp.callCode pre args a' (c₀.retToCallIn cb.frame.module) []⟩ := by
        have := ContextTyped.steps_typed hT hctX (steps_host hst)
        rw [hs'] at this
        simpa [Interp.callCode] using this
      have hd₆ : EvDiv (profile o) host mm ⟨s', f,
          Interp.callCode pre args a' (c₀.retToCallIn cb.frame.module) []⟩ cs₂ := by
        rw [← hs']
        simpa [Interp.callCode] using hd₅
      have hz := ihC mm (by omega) s' f pre args a' _ cs₂ (isCallRef_retToCallIn hc₀ _) hcc₂ hct₂
        hd₆
      exact div_descend (x := ⟨a, (us, s)⟩) (descends_tailL hfi hcode hty hd hq) hz

end Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack

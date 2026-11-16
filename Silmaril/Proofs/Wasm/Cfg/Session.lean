module

public import Silmaril.Wasm.Cfg.Session.Defs
public import Silmaril.Wasm.Cfg.FunctionCfg.Thms
public import Silmaril.Wasm.Abstract.NodeBridge.Thms
public import Silmaril.Wasm.Abstract.HostCall.Thms
public import Silmaril.Wasm.Abstract.XDiverge.Thms
public import Silmaril.Wasm.Abstract.XRecursion.Thms
public import Silmaril.Wasm.Abstract.InstSession.Thms
public import Silmaril.Wasm.Abstract.InstSessionD.Defs
public import Silmaril.Wasm.Game.Adequacy.Thms
public import Silmaril.Wasm.Execution.Core.Inversion.Thms
public import Silmaril.Wasm.Execution.Core.Soundness
public import Silmaril.Wasm.Execution.Core.Soundness.PureRedex
public import Silmaril.Wasm.SingleThreaded.Locality
public import Silmaril.Wasm.Execution.Core.Sim.ExitLift

@[expose] public section

/-!
# The CFG session of a host-free instance (proofs)

See `Silmaril.Wasm.Cfg.Session.Thms`.
-/

namespace Silmaril.Wasm.Cfg.Proofs.Session

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine
  Silmaril.Wasm.Cfg.Bridge Silmaril.Wasm.Cfg.Session
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Binaryen Silmaril.Wasm.Interp Silmaril.Wasm.Validation
open Silmaril.Wasm.Abstract.InstSession (Res sAns instFinS instTripleS instSession)
open Silmaril.Wasm.Abstract.XRecursion (closedCallX)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)
open Silmaril.Games.Abstract.StratThread (Reach InfRounds)

/-! ## Reading sink states -/

section Sink

variable {H : Type}

theorem ends_inv {st : MState H} {o : Region.Out} (h : Ends st o) :
    (st.node = .exit ∧ (o = .normal st.stk ∨ o = .ret st.stk ∨ o = .br 0 st.stk)) ∨
      (st.node = .trap ∧ (o = .trap ∨ ∃ W c, o = .tailNull W c)) ∨
      (st.node = .raise ∧ ∃ t, st.stk = [.ref (.exn t)] ∧ o = .throw t) := by
  unfold Ends at h
  split at h <;> simp_all

/-- A non-tail end is an `Ends` end in the final store, and its native result keeps that store
and relates its flow by `FlowRel`. -/
theorem endsC_resOut {C : Abstract.CallRel H} {st : MState H} {S : Store H} {F : Frame}
    {o : Region.Out} {r : Store H × Frame × Flow} (ho : ∀ W a c, o ≠ .tail W a c)
    (hE : EndsC C st S F o) (hR : ResOut C S F o r) :
    Ends st o ∧ st.store = S ∧ r.1 = S ∧ FlowRel r.2.2 o := by
  cases o with
  | tail W a c => exact absurd rfl (ho W a c)
  | _ => exact ⟨hE.1, hE.2.1, hR.1, hR.2.2⟩

/-- `sink_cases` away from pending tail calls. -/
theorem sink_nontail {st : MState H} {S S' : Store H} {o : Region.Out} {fl : Flow}
    (hEn : Ends st o) (hs : st.store = S) (hr : S' = S) (hfl : FlowRel fl o) :
    (∃ ws, fl.retVals = some ws ∧ st.store = S' ∧
        ∀ n, n ≤ ws.length → sinkResult n st = some (.values (ws.take n).reverse)) ∨
      (fl = .trap ∧ st.store = S' ∧ ∀ n, sinkResult n st = some .trap) ∨
      ∃ t, fl = .throw t := by
  subst hr
  obtain ⟨node, stk, ls, s₀, f₀⟩ := st
  simp only at hs
  subst hs
  rcases ends_inv hEn with ⟨hn, ho⟩ | ⟨hn, ho⟩ | ⟨hn, t, hst, ho⟩ <;> simp only at hn ho <;>
    subst hn
  · rcases ho with rfl | rfl | rfl <;> cases fl <;> simp only [FlowRel] at hfl
    · subst hfl; exact .inl ⟨_, rfl, rfl, fun n _ => by simp [sinkResult]⟩
    · obtain ⟨junk, rfl⟩ := hfl
      exact .inl ⟨_, rfl, rfl, fun n hn => by
        simp [sinkResult, List.reverse_append, List.take_append_of_le_length hn]⟩
    · obtain ⟨rfl, junk, rfl⟩ := hfl
      exact .inl ⟨_, rfl, rfl, fun n hn => by
        simp [sinkResult, List.reverse_append, List.take_append_of_le_length hn]⟩
  · rcases ho with rfl | ⟨W, c, rfl⟩ <;> cases fl <;> simp only [FlowRel] at hfl <;>
      exact .inr (.inl ⟨rfl, rfl, fun n => by simp [sinkResult]⟩)
  · subst ho
    cases fl <;> simp only [FlowRel] at hfl
    exact .inr (.inr ⟨_, rfl⟩)

/-- **What a sink state reads as, against its native result**: a run ending (`EndsC`) as the
native result `(S', F', fl)` (`ResOut`) reads as the values of `fl` (the top `n`, for any `n` up
to their number) with the final store, or as a trap with the final store, or `fl` is an
exception. The oracle must be functional (it answers a pending tail call). -/
theorem sink_cases {C : Abstract.CallRel H}
    (hC : ∀ s a us o₁ o₂, C s a us o₁ → C s a us o₂ → o₁ = o₂)
    {st : MState H} {S S' : Store H} {F F' : Frame} {out : Region.Out} {fl : Flow}
    (hE : EndsC C st S F out) (hR : ResOut C S F out (S', F', fl)) :
    (∃ ws, fl.retVals = some ws ∧ st.store = S' ∧
        ∀ n, n ≤ ws.length → sinkResult n st = some (.values (ws.take n).reverse)) ∨
      (fl = .trap ∧ st.store = S' ∧ ∀ n, sinkResult n st = some .trap) ∨
      ∃ t, fl = .throw t := by
  obtain ⟨node, stk, ls, s₀, f₀⟩ := st
  cases out with
  | tail W a c =>
    obtain ⟨fi, ps, rs, W₀, args, fl₁, s₃, hfi, hty, hW, hn, hc, hend⟩ := hE
    obtain ⟨fi', ps', rs', W₀', args', fl₂, hfi', hty', hW', hn', hc', -, -, rfl⟩ := hR
    rw [hfi] at hfi'; cases hfi'
    rw [hty] at hty'; cases hty'
    have hargs : args = args' := by
      rw [hW] at hW'
      exact (List.append_inj' hW' (hn.trans hn'.symm)).2
    subst hargs
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (hC _ _ _ _ _ hc hc')
    cases fl₁ with
    | normal vs =>
      simp only [tailEnd, Flow.retVals, Option.map_some, Option.some.injEq, MState.mk.injEq] at hend
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hend
      exact .inl ⟨_, rfl, rfl, fun n _ => by simp [sinkResult]⟩
    | ret vs =>
      simp only [tailEnd, Flow.retVals, Option.map_some, Option.some.injEq, MState.mk.injEq] at hend
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hend
      exact .inl ⟨_, rfl, rfl, fun n _ => by simp [sinkResult]⟩
    | brk l vs =>
      cases l with
      | zero =>
        simp only [tailEnd, Flow.retVals, Option.map_some, Option.some.injEq,
          MState.mk.injEq] at hend
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hend
        exact .inl ⟨_, rfl, rfl, fun n _ => by simp [sinkResult]⟩
      | succ l => simp [tailEnd, Flow.retVals] at hend
    | trap =>
      simp only [tailEnd, Option.some.injEq, MState.mk.injEq] at hend
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hend
      exact .inr (.inl ⟨rfl, rfl, fun n => rfl⟩)
    | throw t => exact .inr (.inr ⟨t, rfl⟩)
  | _ =>
    obtain ⟨hEn, hs, hr, hfl⟩ := endsC_resOut (by intros; exact nofun) hE hR
    exact sink_nontail hEn hs hr hfl

end Sink

/-! ## Typing -/

section Typing

variable {H : Type}

theorem expand_of_funcType {d : DefType} {ps rs : List CValType}
    (hf : d.funcType? = some (ps, rs)) : Expand d (.func (Ty.ofList ps) (Ty.ofList rs)) := by
  rw [Expand.iff]
  unfold DefType.funcType? at hf
  split at hf
  next P R hex =>
    obtain ⟨hP, hR⟩ : P.toList = ps ∧ R.toList = rs := by
      simpa only [Option.some.injEq, Prod.mk.injEq] using hf
    rw [← hP, ← hR, Ty.ofList_toList, Ty.ofList_toList]
    exact hex
  next => cases hf

theorem hostTyped_noHostX : Abstract.HostTyped (noHostX : HostSemantics H) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ h => h.elim

/-- **The values a typed invocation returns are as many as its results** (Core 3.0, no host). -/
theorem invoke_vals_length {P : Numerics.Profile} {s : Store H} {a : Nat} {vs : List Val}
    {fi : FuncInst H} {ps rs : List CValType} (hs : StoreOk s) (hok : InvokeOk s a vs)
    (hfi : s.funcs[a]? = some fi) (hty : DefType.funcType? fi.type = some (ps, rs))
    {s' : Store H} {f' : Frame} {X : List Val}
    (h : Steps P noHostX (invoke s a vs) ⟨s', f', vals X⟩) : X.length = rs.length := by
  obtain ⟨fi', ps', rs', hfi', hexp, hcfg⟩ := invoke_ok hs hok
  rw [hfi] at hfi'; cases hfi'
  have key : ∀ c, Steps P noHostX (invoke s a vs) c → ConfigOk c rs'.toList := fun c h => by
    induction h with
    | refl => exact hcfg
    | tail _ hst ih => exact (Abstract.Step.preservation_typed hostTyped_noHostX ih hst).1
  have hc := key _ h
  obtain ⟨C, -, hA⟩ := hc
  have hl := AdminsOk.vals_len hA X rfl
  have heq := Expand.func_eq hexp (expand_of_funcType hty)
  simp only [Ty.func.injEq] at heq
  rw [heq.2, Ty.toList_ofList] at hl
  simpa using hl.symm

theorem toAdmin_ne_trap (v : Val) : v.toAdmin ≠ .trap := by
  rcases v with ⟨⟨t | t⟩, b⟩ | b | r <;> simp [Val.toAdmin]

theorem toAdmin_ne_throwRef (v : Val) : v.toAdmin ≠ .plain .throwRef := by
  rcases v with ⟨⟨t | t⟩, b⟩ | b | r <;> simp [Val.toAdmin]

/-- A result whose code is a value sequence is those values. -/
theorem result_of_toAdmin_vals {r : Result} {X : List Val} (h : r.toAdmin = vals X) :
    r = .values X := by
  cases r with
  | values ws =>
    exact congrArg Result.values (List.map_injective_iff.2 Sim.Val.toAdmin_injective h)
  | trap =>
    cases X with
    | nil => simp [Result.toAdmin, vals] at h
    | cons x X =>
      simp only [Result.toAdmin, vals, List.map_cons, List.cons.injEq] at h
      exact absurd h.1.symm (toAdmin_ne_trap x)
  | throw t =>
    match X, h with
    | [], h => simp [Result.toAdmin, vals] at h
    | [_], h => simp [Result.toAdmin, vals] at h
    | _ :: y :: _, h =>
      simp only [Result.toAdmin, vals, List.map_cons, List.cons.injEq] at h
      exact absurd h.2.1.symm (toAdmin_ne_throwRef y)

/-- A result whose code is a trap is a trap. -/
theorem result_of_toAdmin_trap {r : Result} (h : r.toAdmin = [.trap]) : r = .trap := by
  cases r with
  | trap => rfl
  | values X =>
    cases X with
    | nil => simp [Result.toAdmin, vals] at h
    | cons x _ =>
      simp only [Result.toAdmin, vals, List.map_cons, List.cons.injEq] at h
      exact absurd h.1 (toAdmin_ne_trap x)
  | throw t => simp [Result.toAdmin] at h

/-- A typed scalar answer to values has as many values as the result types. -/
theorem ofResult_values_length {ft : FnType} {X : List Val} {v : Answer ft}
    (h : Answer.ofResult? ft (.values X) = some v) : X.length = ft.results.length := by
  simp only [Answer.ofResult?] at h
  split at h
  next hx => exact hx.length_eq.symm
  next => cases h

end Typing

/-! ## Host-free runs -/

section Runs

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

theorem steps_funcs {c c' : Config H} (h : Steps P noHostX c c') :
    c'.store.funcs = c.store.funcs := by
  induction h with
  | refl => rfl
  | tail _ hs ih => exact (SingleThreaded.Step.framesLocal hs).1.trans ih

theorem host_mono_steps {c c' : Config H} (h : Steps P noHostX c c') : Steps P host c c' := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (Abstract.Step.host_mono (fun _ _ _ _ (h : False) => h.elim) hs)

/-- A configuration that does not diverge reaches a normal form. -/
theorem exists_nf {c : Config H} (hnd : ¬ Diverges P host c) :
    ∃ c', Steps P host c c' ∧ ∀ x, ¬ Step P host c' x := by
  by_contra hne
  push Not at hne
  exact hnd (InfiniteTrace.coinduct (fun c' => Steps P host c c')
    (fun c' hc' => let ⟨x, hx⟩ := hne c' hc'; ⟨x, hx, hc'.tail hx⟩) .refl)

end Runs

/-- **A tExt-checked invocation never ends in an exception** (deterministic profile, no host): a
closed outcome of the invocation is not a throw. -/
theorem closedCallX_not_throw {H : Type} {o : GrowOracle} {s : Store H} {a : Nat} {vs : List Val}
    {fi : FuncInst H} {ps rs : List CValType} (hs : StoreOk s) (hok : InvokeOk s a vs)
    (hS : StoreChkE tExt s.funcs) (hW : WasmFuncsT s) (hfi : s.funcs[a]? = some fi)
    (hty : DefType.funcType? fi.type = some (ps, rs)) {S' : Store H} {t : Nat}
    (hcl : closedCallX s a vs (S', .throw t)) : False := by
  have hnd : ¬ Diverges (profile o) noHostX (invoke s a vs) := fun hd => by
    obtain ⟨fi', fn', hfi', hc', hdx⟩ := (XProgress.invoke_diverges_iff_funDivX hs hok hS hW).1 hd
    have hcl' := hcl
    rw [Abstract.XRecursion.closedCallX_fixpoint] at hcl'
    obtain ⟨fi'', fn'', ps', rs', f₂, hfi'', hc'', -, hev⟩ := hcl'
    rw [hfi'] at hfi''; cases hfi''
    rw [hc'] at hc''; cases hc''
    exact Abstract.XDiverge.not_evalDivX_of_evalOX hev hdx
  obtain ⟨c', hst, hnf⟩ := exists_nf hnd
  obtain ⟨-, s₂, fl, hcl', hsh⟩ :=
    (XProgress.invoke_closedX_adequacy (o := o) hs hok hS hW hfi hty).2.1 c' hst hnf
  cases Abstract.XDiverge.closedCallX_det hcl hcl'
  rcases hsh with ⟨ws, hws, -⟩ | ⟨h, -⟩ <;> simp [Flow.retVals] at *

/-- The typed closed extended oracle is functional. -/
theorem cx_det {H : Type} :
    ∀ (s : Store H) a us o₁ o₂, CX (closedCallX : Abstract.CallRel H) s a us o₁ →
      CX closedCallX s a us o₂ → o₁ = o₂ :=
  fun _ _ _ _ _ h₁ h₂ => Abstract.XDiverge.closedCallX_det h₁.2 h₂.2

theorem isSink_of_sinkResult {H : Type} {n : Nat} {st : MState H} {r : Result}
    (h : sinkResult n st = some r) : st.node.IsSink := by
  obtain ⟨node, stk, _, _, _⟩ := st
  cases node <;> simp only [sinkResult] at h <;> trivial

/-! ## The instance -/

section Inst

variable {I : ScalarInstance} {o : GrowOracle} {P : Numerics.Profile}

theorem op_isEmpty (h : I.imports = []) : IsEmpty I.E.Op :=
  ⟨fun ⟨i, _⟩ => by have := i.2; simp [h] at this⟩

theorem call_isEmpty (h : I.imports = []) : IsEmpty (Call I.E) :=
  ⟨fun x => (op_isEmpty h).false x.1⟩

theorem log_nil (h : I.imports = []) (c : List (Call I.E)) : c = [] := by
  cases c with
  | nil => rfl
  | cons x _ => exact ((call_isEmpty h).false x).elim

theorem evRun_nil_steps {x y : Config Nat}
    (hr : Abstract.EvRun P (Abstract.NodeBridge.instHost I) x [] y) :
    Steps P noHostX x y := by
  have h := Abstract.evRun_nil_silentRun hr
  clear hr
  induction h with
  | refl => exact .refl
  | tail _ hs ih =>
    rcases hs with hs | ⟨-, _, _, _, _, -, hd⟩
    · exact ih.tail hs
    · exact absurd hd Abstract.NodeBridge.not_instHost_diverged

theorem steps_evRun {x y : Config Nat} (hr : Steps P noHostX x y) :
    Abstract.EvRun P (Abstract.NodeBridge.instHost I) x [] y := by
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl _
  | head hs _ ih => exact .silent (Or.inl hs) ih

theorem forall₂_valOk_of_hasVal (s : Store Nat) :
    ∀ {ts : List ScalarType} {vs : List Val}, List.Forall₂ ScalarType.HasVal ts vs →
      List.Forall₂ (ValOk s) vs (ts.map ScalarType.toC)
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h hs =>
    .cons ((ScalarType.hasVal_iff_valOk s _ _).mp h) (forall₂_valOk_of_hasVal s hs)

/-- **The exported function of a question**, on the fragment: a Wasm function of the export's
type, invoked with typed arguments. -/
theorem export_fn {s : Store Nat} (h : HFOk I s) (a : I.F.Op) :
    ∃ (fi : FuncInst Nat) (fn : Func) (ps rs : List CValType),
      s.funcs[I.addr a.1]? = some fi ∧ fi.code = .wasm fn ∧
      DefType.funcType? fi.type = some (ps, rs) ∧
      rs = (I.exports.get a.1).results.map ScalarType.toC ∧ InvokeOk s (I.addr a.1) a.2.1 := by
  obtain ⟨fi, hfi, hexp⟩ := h.wf.export_type a.1
  obtain ⟨fn, ps, rs, hcode, hty⟩ := h.wasm _ fi hfi
  have heq := Expand.func_eq (expand_of_funcType hty) hexp
  simp only [FnType.toComp, Ty.func.injEq] at heq
  have hrs : rs = (I.exports.get a.1).results.map ScalarType.toC := by
    simpa using congrArg Ty.toList heq.2
  refine ⟨fi, fn, ps, rs, hfi, hcode, hty, hrs, fi, _, _, hfi, hexp, ?_⟩
  rw [Ty.toList_ofList]
  exact forall₂_valOk_of_hasVal s a.2.2

/-- An answer read from Core values: if the values `(ws.take n).reverse` are typed at the
export's `n` results, then `n ≤ ws.length`. -/
theorem le_of_take_length {ws : List Val} {n : Nat} (h : ((ws.take n).reverse).length = n) :
    n ≤ ws.length := by
  simp only [List.length_reverse, List.length_take] at h
  omega

/-- **Core activations are CFG activations** on the fragment. -/
theorem instFinS_sub {s : Store Nat} (h : HFOk I s) (a : I.F.Op) :
    instFinS I (profile o) s a ⊆ cfgFinS I o s a := by
  rintro ⟨c, e⟩ hx
  have hc : c = [] := log_nil h.noImports c
  subst hc
  obtain ⟨fi, fn, ps, rs, hfi, hcode, hty, hrs, hok⟩ := export_fn h a
  rcases hx with ⟨v, s', he, hp⟩ | ⟨he, hp⟩
  · obtain ⟨cs, hcs, r, hv, hrun⟩ := Abstract.NodeBridge.ret_iff.1 hp
    cases List.forall₂_nil_left_iff.1 hcs
    have hst : Steps (profile o) noHostX (invoke s (I.addr a.1) a.2.1) ⟨s', {}, r.toAdmin⟩ :=
      evRun_nil_steps hrun
    obtain ⟨-, s₂, fl, -, hsh, f₂, st, out, s₃, f₃, -, hm, hE, hR⟩ :=
      Function.core_machine (o := o) h.wf.storeOk hok h.chk h.wasm hfi hcode hty hst
        (fun _ => Step.result_stuck r)
    refine ⟨rfl, .inl ⟨v, s', r, he, hv, fi, fn, ps, rs, st, hfi, hcode, hty, hm, ?_⟩⟩
    rcases sink_cases cx_det hE hR with ⟨ws, hws, hss, hread⟩ | ⟨rfl, hss, hread⟩ | ⟨t, rfl⟩
    · rcases hsh with ⟨ws', hws', hceq⟩ | ⟨rfl, -⟩
      · rw [hws] at hws'; cases hws'
        simp only [Config.mk.injEq, true_and] at hceq
        obtain ⟨rfl, hcode'⟩ := hceq
        have hr := result_of_toAdmin_vals hcode'
        subst hr
        have hl := ofResult_values_length hv
        rw [← List.length_map (f := ScalarType.toC), ← hrs] at hl
        exact ⟨hread _ (le_of_take_length hl), hss⟩
      · simp [Flow.retVals] at hws
    · rcases hsh with ⟨ws', hws', -⟩ | ⟨-, hceq⟩
      · simp [Flow.retVals] at hws'
      · simp only [Config.mk.injEq, true_and] at hceq
        obtain ⟨rfl, hcode'⟩ := hceq
        have hr := result_of_toAdmin_trap hcode'
        subst hr
        exact ⟨hread _, hss⟩
    · rcases hsh with ⟨ws', hws', -⟩ | ⟨hft, -⟩
      · simp [Flow.retVals] at hws'
      · cases hft
  · obtain ⟨cs, hcs, c', hrun, hd⟩ := Abstract.NodeBridge.div_iff.1 hp
    cases List.forall₂_nil_left_iff.1 hcs
    have hd' : Diverges (profile o) noHostX (invoke s (I.addr a.1) a.2.1) :=
      InfiniteTrace.of_steps (evRun_nil_steps hrun) hd
    exact ⟨rfl, .inr ⟨he, fi, fn, ps, rs, hfi, hcode, hty,
      (Function.invoke_diverges_iff_mdivT h.wf.storeOk hok h.chk h.wasm hfi hcode hty).1 hd'⟩⟩

/-- **CFG activations are Core activations** on the fragment. -/
theorem cfgFinS_sub {s : Store Nat} (h : HFOk I s) (a : I.F.Op) :
    cfgFinS I o s a ⊆ instFinS I (profile o) s a := by
  rintro ⟨c, e⟩ ⟨hc, hx⟩
  simp only at hc
  subst hc
  obtain ⟨fi', fn', ps', rs', hfi', hcode', hty', hrs, hok⟩ := export_fn h a
  rcases hx with ⟨v, s', r, he, hv, fi, fn, ps, rs, st, hfi, hcode, hty, hm, hsr, hss⟩ |
    ⟨he, fi, fn, ps, rs, hfi, hcode, hty, hmd⟩
  · rw [hfi] at hfi'; cases hfi'
    rw [hcode] at hcode'; cases hcode'
    rw [hty] at hty'; cases hty'
    obtain ⟨out, S, F, ⟨S', F', fl⟩, hE, hR, -, hcl, hvals, htrap⟩ :=
      Function.machine_core (o := o) h.wf.storeOk hok h.chk h.wasm hfi hcode hty hm
        (isSink_of_sinkResult hsr)
    refine .inl ⟨v, s', he, Abstract.NodeBridge.ret_iff.2 ⟨[], .nil, r, hv, ?_⟩⟩
    rcases sink_cases cx_det hE hR with ⟨ws, hws, hss', hread⟩ | ⟨rfl, hss', hread⟩ | ⟨t, rfl⟩
    · have hst := hvals ws hws
      have hl := invoke_vals_length h.wf.storeOk hok hfi hty hst
      rw [hread _ (le_of_take_length hl)] at hsr
      cases hsr
      rw [← hss, hss']
      exact steps_evRun hst
    · rw [hread] at hsr
      cases hsr
      rw [← hss, hss']
      exact steps_evRun (htrap rfl)
    · exact (closedCallX_not_throw (o := o) h.wf.storeOk hok h.chk h.wasm hfi hty hcl).elim
  · have hd := Function.invoke_diverges_of_mdivT hok h.chk hfi hcode hty hmd
    exact .inr ⟨he, Abstract.NodeBridge.div_iff.2 ⟨[], .nil, _, .refl _, hd⟩⟩

/-- **One activation**: on the fragment, the CFG machine's finished behaviours are the
instance's. -/
theorem instFinS_eq {s : Store Nat} (h : HFOk I s) (a : I.F.Op) :
    instFinS I (profile o) s a = cfgFinS I o s a :=
  Set.Subset.antisymm (instFinS_sub h a) (cfgFinS_sub h a)

/-! ## The fragment persists -/

/-- **A returning activation keeps the fragment**: the function list does not change along the
host-free run, and the instance stays well formed (`ScalarInstance.wellFormed_after_run`). -/
theorem hfOk_of_ret {s s₁ : Store Nat} (h : HFOk I s) {a : I.F.Op} {c : List (Call I.E)}
    {b : Res I.exports ⊕ PUnit} (hm : (c, .ret b s₁) ∈ instFinS I (profile o) s a) :
    HFOk I s₁ := by
  rcases hm with ⟨v, s', he, hp⟩ | ⟨he, -⟩
  · simp only [End.ret.injEq] at he
    obtain ⟨-, rfl⟩ := he
    obtain ⟨cs, hcs, r, -, hrun⟩ := Abstract.NodeBridge.ret_iff.1 hp
    have hc : c = [] := log_nil h.noImports c
    subst hc
    cases List.forall₂_nil_left_iff.1 hcs
    have hst : Steps (profile o) noHostX (invoke s (I.addr a.1) a.2.1) ⟨s₁, {}, r.toAdmin⟩ :=
      evRun_nil_steps hrun
    have hf : s₁.funcs = s.funcs := steps_funcs hst
    have hE := op_isEmpty h.noImports
    let K : Env I.E := fun e => (hE.false e).elim
    have hK : ThrowsBelow K s.exns.length := fun e => (hE.false e).elim
    have hst' : Steps (profile o) (hostOf I.imports K) (invoke s (I.addr a.1) a.2.1)
        ⟨s₁, {}, r.toAdmin⟩ := host_mono_steps hst
    refine ⟨h.noImports, (ScalarInstance.wellFormed_after_run h.wf hK hst' rfl).1, ?_, ?_⟩
    · intro a' fi hfi
      exact h.wasm a' fi (by rw [← hf]; exact hfi)
    · rw [hf]; exact h.chk
  · cases he

/-- **The fragment holds at every store the instance session reaches.** -/
theorem hfOk_of_reach {s₀ s : Store Nat} (h : HFOk I s₀)
    (hr : Reach (instTripleS I (profile o)) s₀ s) : HFOk I s := by
  induction hr with
  | refl => exact h
  | step hm _ ih => exact ih (hfOk_of_ret h hm)

/-! ## The session -/

theorem satP_eq {s : Store Nat} (h : I.imports = []) :
    satP (instTripleS I (profile o)) s = satP (cfgTripleS I o) s := by
  funext a
  ext ⟨_, m⟩
  exact ((op_isEmpty h).false m).elim

theorem inf_eq {s : Store Nat} (h : I.imports = []) :
    (instTripleS I (profile o)).2.2 s = (cfgTripleS I o).2.2 s := by
  funext a
  ext ω
  exact ((call_isEmpty h).false (ω 0)).elim

/-- **The CFG session is the instance session** on the fragment. -/
theorem cfgSession_eq_instSession {s : Store Nat} (h : HFOk I s) :
    cfgSession I o s = instSession I (profile o) s :=
  (StratSession.threadS_congr (t := instTripleS I (profile o)) (t' := cfgTripleS I o) fun _ hr =>
    ⟨funext fun a => instFinS_eq (o := o) (hfOk_of_reach h hr) a, satP_eq h.noImports,
      inf_eq h.noImports⟩).symm

/-- **Coherent infinite rounds agree**: from a store of the fragment, the coherent infinite
sequences of export rounds of the instance triple are those of the CFG triple. -/
theorem infRounds_iff {s₀ : Store Nat} (h : HFOk I s₀) {a : ℕ → I.F.Op}
    {r : ℕ → List (Call I.E) × (Res I.exports ⊕ PUnit)} {s : ℕ → Store Nat} :
    InfRounds (instTripleS I (profile o)) s₀ a r s ↔ InfRounds (cfgTripleS I o) s₀ a r s := by
  constructor
  · rintro ⟨hz, hs⟩
    have hk : ∀ k, HFOk I (s k) := fun k => by
      induction k with
      | zero => rw [hz]; exact h
      | succ k ih => exact hfOk_of_ret ih (hs k)
    exact ⟨hz, fun k => by
      show _ ∈ cfgFinS I o _ _
      rw [← instFinS_eq (hk k)]; exact hs k⟩
  · rintro ⟨hz, hs⟩
    have hk : ∀ k, HFOk I (s k) ∧ ((r k).1, .ret (r k).2 (s (k + 1))) ∈
        instFinS I (profile o) (s k) (a k) := fun k => by
      induction k with
      | zero =>
        have h0 : HFOk I (s 0) := by rw [hz]; exact h
        exact ⟨h0, by rw [instFinS_eq h0]; exact hs 0⟩
      | succ k ih =>
        have h1 := hfOk_of_ret ih.1 ih.2
        exact ⟨h1, by rw [instFinS_eq h1]; exact hs (k + 1)⟩
    exact ⟨hz, fun k => (hk k).2⟩

/-- **The infinite plays of the CFG session**: exactly the plays of the coherent infinite
sequences of rounds of the CFG triple (trap-resume rounds included); there are no productive
import streams inside a round. -/
theorem mem_inf_cfgSession {s₀ : Store Nat} (h : HFOk I s₀)
    {J : Set (List (Move I.E (Abstract.InstSession.ssig I.exports)))} :
    J ∈ (cfgSession I o s₀).inf ↔
      ∃ a r s, InfRounds (cfgTripleS I o) s₀ a r s ∧ J = StratSession.sroundsPlay a r := by
  rw [cfgSession_eq_instSession h, Abstract.InstSession.mem_inf_instSession]
  constructor
  · rintro (⟨-, -, -, ω, -, -, -⟩ | ⟨a, r, s, hr, rfl⟩)
    · exact ((call_isEmpty h.noImports).false (ω 0)).elim
    · exact ⟨a, r, s, (infRounds_iff h).1 hr, rfl⟩
  · rintro ⟨a, r, s, hr, rfl⟩
    exact .inr ⟨a, r, s, (infRounds_iff h).2 hr, rfl⟩

end Inst

/-- **`core3SemD` through CFG sessions** where the fragment applies. -/
theorem core3SemD_eq_cfgSessions {o : GrowOracle} :
    Abstract.InstSession.core3SemD (profile o) =
      Abstract.InstSession.threadSemSD (cfgSessions o) := by
  unfold Abstract.InstSession.core3SemD
  congr 1
  funext m
  unfold cfgSessions
  split
  · next h => exact (cfgSession_eq_instSession h).symm
  · rfl

end Silmaril.Wasm.Cfg.Proofs.Session

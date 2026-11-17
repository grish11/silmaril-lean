module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingInfXP.Desc
public import Silmaril.Games.Abstract.ModuleInf.Thms

/-!
# Productive canonical runs are productive Core runs (proofs)

* stream lemmas: a resolved stream with a list in front (`substInf_split`), a resolved
  concatenation regrouped by segment (`substInf_regroup`), consistency of streams (`ConsInf`);
* `infLXP_fwd`: a productive run of trees within their function (`InfLXP`), resolved by the
  closure, is a productive Core run of the lowered trees with the resolved events. By induction:
  the finite parts are logged Core runs (`head_glue`, `loopBack_glue`, `arm_glue`), lifted
  through their contexts; a loop iterating forever (`loopInf`) is a chain of iterations
  (`coreInf_of_segments`), its stream regrouped by iteration;
* `infChain_fwd`: an infinite chain of descents is a chain of Core runs, each from the call of
  one descent into the next (`descends_fwd`, the contexts carried by `AtCall`);
* `wasmEvInfNXP_coreInf`: every productive run of `wasmEvInfNXP` whose answers the host allows is
  a productive Core run of the invocation with exactly those events.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingInfXP

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Interp
open Silmaril.Wasm.Abstract.CallXP (POut EvalOXP)
open Shape (streamAppend StreamConcat SubstInf Res1 SubstPre)

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

/-! ## Streams -/

section Streams

universe u

variable {α : Type u}

theorem flatMap_range_add (L : Nat → List α) (a b : Nat) :
    (List.range (a + b)).flatMap L =
      (List.range a).flatMap L ++ (List.range b).flatMap (fun j => L (a + j)) := by
  rw [List.range_add, List.flatMap_append, List.flatMap_map]

theorem flatMap_range_mono (L : Nat → List α) {m n : Nat} (h : m ≤ n) :
    ((List.range m).flatMap L).length ≤ ((List.range n).flatMap L).length := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [flatMap_range_add]
  simp

theorem streamAppend_map {β : Type u} (g : α → β) (l : List α) (ω : Nat → α) :
    (fun i => g ((l ++ω ω) i)) = (l.map g) ++ω (fun i => g (ω i)) := by
  funext i
  by_cases hi : i < l.length
  · rw [Shape.streamAppend_lt hi, Shape.streamAppend_lt (by simpa using hi)]
    simp
  · rw [Shape.streamAppend_ge (by omega), Shape.streamAppend_ge (by simp; omega)]
    simp

variable {sh : Silmaril.Games.Abstract.Shape.{u}} {c : sh.ClosedMod}

theorem substPre_of_res (l : List (Call (sh.E ⊕ₛ sh.self))) (L : Nat → List (Call sh.E))
    (h : ∀ i (hi : i < l.length), Res1 c l[i] (L i)) :
    SubstPre c l ((List.range l.length).flatMap L) := by
  induction l generalizing L with
  | nil => simpa using SubstPre.nil
  | cons x l ih =>
    have h0 : Res1 c x (L 0) := h 0 (by simp)
    have ht := ih (fun j => L (j + 1)) (fun i hi => h (i + 1) (by simp; omega))
    have e : (List.range (x :: l).length).flatMap L =
        L 0 ++ (List.range l.length).flatMap (fun j => L (j + 1)) := by
      rw [List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    rw [e]
    generalize L 0 = l0 at h0 ⊢
    cases h0 with
    | ext => exact .ext ht
    | int hm => exact .int hm ht

/-- **A resolved stream with a finite list in front** is a resolved list in front of a
resolved stream. -/
theorem substInf_split {l : List (Call (sh.E ⊕ₛ sh.self))} {ν : Nat → Call (sh.E ⊕ₛ sh.self)}
    {ω : Nat → Call sh.E} (h : SubstInf c (l ++ω ν) ω) :
    ∃ q ω', ω = q ++ω ω' ∧ SubstPre c l q ∧ SubstInf c ν ω' := by
  obtain ⟨L, hL, hc⟩ := h
  refine ⟨(List.range l.length).flatMap L,
    fun i => ω (((List.range l.length).flatMap L).length + i), ?_, ?_, ?_⟩
  · funext i
    by_cases hi : i < ((List.range l.length).flatMap L).length
    · rw [Shape.streamAppend_lt hi]
      exact hc.1 l.length i hi
    · rw [Shape.streamAppend_ge (by omega)]
      congr 1
      omega
  · exact substPre_of_res l L (fun i hi => by
      have := hL i
      rwa [Shape.streamAppend_lt hi] at this)
  · refine ⟨fun j => L (l.length + j), fun j => ?_, fun n i hi => ?_, fun N => ?_⟩
    · have := hL (l.length + j)
      rwa [Shape.streamAppend_ge (by omega), show l.length + j - l.length = j by omega] at this
    · have hp := hc.1 (l.length + n) (((List.range l.length).flatMap L).length + i)
        (by rw [flatMap_range_add]; simp only [List.length_append]; omega)
      dsimp only
      rw [hp]
      simp only [flatMap_range_add]
      rw [List.getElem_append_right (by omega)]
      simp
    · obtain ⟨m, hm⟩ := hc.2 (N + ((List.range l.length).flatMap L).length)
      refine ⟨m, ?_⟩
      have := flatMap_range_mono L (show m ≤ l.length + m by omega)
      rw [flatMap_range_add] at this
      simp only [List.length_append] at this
      omega

/-- **A resolved concatenation of segments is resolved segment by segment.** -/
theorem substInf_regroup {u : Nat → List (Call (sh.E ⊕ₛ sh.self))}
    {ν : Nat → Call (sh.E ⊕ₛ sh.self)} {ω : Nat → Call sh.E} (hu : StreamConcat u ν)
    (h : SubstInf c ν ω) :
    ∃ q : Nat → List (Call sh.E), (∀ n, SubstPre c (u n) (q n)) ∧ StreamConcat q ω := by
  obtain ⟨L, hL, hc⟩ := h
  let O : Nat → Nat := fun n => ((List.range n).flatMap u).length
  have hO : ∀ n, O (n + 1) = O n + (u n).length := fun n => by
    simp [O, List.range_succ]
  let q : Nat → List (Call sh.E) := fun n =>
    (List.range (u n).length).flatMap (fun j => L (O n + j))
  have hq : ∀ n, (List.range n).flatMap q = (List.range (O n)).flatMap L := by
    intro n
    induction n with
    | zero => simp [O]
    | succ n ih =>
      rw [List.range_succ, List.flatMap_append, ih, hO, flatMap_range_add]
      simp [q]
  refine ⟨q, fun n => substPre_of_res (u n) _ (fun j hj => ?_), fun n => ?_, fun N => ?_⟩
  · have hp := hu.1 (n + 1) (O n + j) (by have := hO n; simp only [O] at this ⊢; omega)
    have := hL (O n + j)
    rw [hp] at this
    simpa [List.range_succ, List.flatMap_append, O, List.getElem_append_right] using this
  · rw [hq]
    exact hc.1 (O n)
  · obtain ⟨m, hm⟩ := hc.2 N
    obtain ⟨n, hn⟩ := hu.2 m
    exact ⟨n, by rw [hq]; exact le_trans hm (flatMap_range_mono L hn)⟩

end Streams

/-- The host answers of a stream are allowed. -/
abbrev ConsInf (host : HostSemantics H) (ω : Nat → Call (wasmHostSig H)) : Prop :=
  ∀ n, coreHostRel host (ω n).1 (.answer (ω n).2)

theorem consInf_split {q : List (Call (wasmHostSig H))} {ω : Nat → Call (wasmHostSig H)}
    (h : ConsInf host (q ++ω ω)) : Cons host q ∧ ConsInf host ω := by
  refine ⟨fun e he => ?_, fun n => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 he
    have := h i
    rwa [Shape.streamAppend_lt hi] at this
  · have := h (q.length + n)
    rwa [Shape.streamAppend_ge (by omega), show q.length + n - q.length = n by omega] at this

theorem cons_of_concat {q : Nat → List (Call (wasmHostSig H))} {ω : Nat → Call (wasmHostSig H)}
    (hq : StreamConcat q ω) (h : ConsInf host ω) (n : Nat) : Cons host (q n) := by
  intro e he
  have hm : e ∈ (List.range (n + 1)).flatMap q :=
    List.mem_flatMap.2 ⟨n, List.mem_range.2 (by omega), he⟩
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hm
  rw [← hq.1 (n + 1) i hi]
  exact h i

/-- A resolved stream with a logged list in front, split with its consistency. -/
theorem split_stream {l : List (OCall H)} {ω₀ : Nat → OCall H} {ω' : Nat → Call (wasmHostSig H)}
    (hs : SubstInf (Shape.close wasmHOpenXP) (fun i => ((l ++ω ω₀) i).lift) ω')
    (hc : ConsInf host ω') :
    ∃ q ω'', ω' = q ++ω ω'' ∧ SubstPre (Shape.close wasmHOpenXP) (l.map OCall.lift) q ∧
      SubstInf (Shape.close wasmHOpenXP) (fun i => (ω₀ i).lift) ω'' ∧ Cons host q ∧
      ConsInf host ω'' := by
  rw [streamAppend_map] at hs
  obtain ⟨q, ω'', rfl, hq, hs'⟩ := substInf_split hs
  obtain ⟨hcq, hc'⟩ := consInf_split hc
  exact ⟨q, ω'', rfl, hq, hs', hcq, hc'⟩

/-! ## Productive runs within a function -/

/-- A productive run of a hole, wrapped in an outer context after host-free steps. -/
theorem coreInf_enter {c₀ c : Config H} {ω : Nat → Call (wasmHostSig H)} (O : Sim.ActiveCtx)
    (enter : Steps P NH c₀ (O.plug c)) (h : CoreInf P host c ω) : CoreInf P host c₀ ω := by
  simpa [Shape.streamAppend_nil] using coreInf_prepend (evRun_of_free enter) (coreInf_plug O h)

section Fwd

variable {tags : List TagInst} (hH : HostSliceT host) (hE : HostSliceE tags host)
include hH hE

/-- **A productive run of trees within their function is a productive Core run** with the
events of its resolution. -/
theorem infLXP_fwd {s : Store H} {f : Frame} {stk : List Val} {es : List Binaryen.BExpr}
    {ω : Nat → OCall H} (h : InfLXP s f stk es ω) :
    ∀ ω', SubstInf (Shape.close wasmHOpenXP) (fun i => (ω i).lift) ω' → ConsInf host ω' →
      ∀ {labels : List Nat} {ret : Nat} {out : Option Nat}, TagsOk tags s →
      StoreChkE (ehExt tags) s.funcs →
      chkE (ehExt tags) s.funcs f.module f.locals.length ret labels (some stk.length) es =
        some out →
      CoreInf P host ⟨s, f, xcode stk es⟩ ω' := by
  induction h with
  | @args s f stk i args es ω _ ih =>
    intro ω' hs hc labels ret out hts hS hchk
    obtain ⟨o, h1, -⟩ := chk_consE.mp hchk
    obtain ⟨oa, ha, -⟩ := chk1_opE h1
    rw [show xcode stk (.op i args :: es) = _ from code_op stk i args es]
    exact coreInf_plug (.suffix _ .hole) (ih ω' hs hc hts hS ha)
  | callK hargs hfi hty _ ih =>
    intro ω' hs hc labels ret out hts hS hchk
    obtain ⟨q, ω'', rfl, hq, hs', hcq, hc'⟩ := split_stream hs hc
    obtain ⟨run, t', hS', hchk'⟩ :=
      head_glue (P := P) hH hE (.callRet hargs hfi hty .nil) hq hcq hts hS hchk
    exact coreInf_prepend run (ih ω'' hs' hc' t' hS' hchk')
  | indK hargs hres hfi hty hy _ ih =>
    intro ω' hs hc labels ret out hts hS hchk
    obtain ⟨q, ω'', rfl, hq, hs', hcq, hc'⟩ := split_stream hs hc
    obtain ⟨run, t', hS', hchk'⟩ :=
      head_glue (P := P) hH hE (.indRet hargs hres hfi hty hy .nil) hq hcq hts hS hchk
    exact coreInf_prepend run (ih ω'' hs' hc' t' hS' hchk')
  | refK hargs hfi hty hy _ ih =>
    intro ω' hs hc labels ret out hts hS hchk
    obtain ⟨q, ω'', rfl, hq, hs', hcq, hc'⟩ := split_stream hs hc
    obtain ⟨run, t', hS', hchk'⟩ :=
      head_glue (P := P) hH hE (.refRet hargs hfi hty hy .nil) hq hcq hts hS hchk
    exact coreInf_prepend run (ih ω'' hs' hc' t' hS' hchk')
  | opK hi hargs hflat _ ih =>
    intro ω' hs hc labels ret out hts hS hchk
    obtain ⟨q, ω'', rfl, hq, hs', hcq, hc'⟩ := split_stream hs hc
    have hE' := EvalLXPh.opOk hi hargs hflat (es := []) .nil
    rw [List.append_nil] at hE'
    obtain ⟨run, t', hS', hchk'⟩ := head_glue (P := P) hH hE hE' hq hcq hts hS hchk
    exact coreInf_prepend run (ih ω'' hs' hc' t' hS' hchk')
  | @block s f stk bt body es np nr ω har _ ih =>
    intro ω' hs hc labels ret out hts hS hchk
    obtain ⟨⟨ob, hbc⟩, enter⟩ := block_enter (P := P) har hchk
    exact coreInf_enter _ enter (ih ω' hs hc hts hS hbc)
  | blockK har hbody hvs _ ih =>
    intro ω' hs hc labels ret out hts hS hchk
    obtain ⟨q, ω'', rfl, hq, hs', hcq, hc'⟩ := split_stream hs hc
    have hE' := EvalLXPh.blockOk har hbody hvs (es := []) .nil
    rw [List.append_nil] at hE'
    obtain ⟨run, t', hS', hchk'⟩ := head_glue (P := P) hH hE hE' hq hcq hts hS hchk
    exact coreInf_prepend run (ih ω'' hs' hc' t' hS' hchk')
  | @loop s f stk bt body es np nr ω har _ ih =>
    intro ω' hs hc labels ret out hts hS hchk
    obtain ⟨⟨ob, hbc⟩, enter⟩ := loop_enter (P := P) har hchk
    exact coreInf_enter _ enter (ih ω' hs hc hts hS hbc)
  | loopK har hbody _ ih =>
    intro ω' hs hc labels ret out hts hS hchk
    obtain ⟨q, ω'', rfl, hq, hs', hcq, hc'⟩ := split_stream hs hc
    have hE' := EvalLXPh.loopOk har hbody (es := []) .nil
    rw [List.append_nil] at hE'
    obtain ⟨run, t', hS', hchk'⟩ := head_glue (P := P) hH hE hE' hq hcq hts hS hchk
    exact coreInf_prepend run (ih ω'' hs' hc' t' hS' hchk')
  | loopBack har hbody _ ih =>
    intro ω' hs hc labels ret out hts hS hchk
    obtain ⟨q, ω'', rfl, hq, hs', hcq, hc'⟩ := split_stream hs hc
    obtain ⟨⟨c₁, st, run⟩, t', hS', hchk'⟩ :=
      loopBack_glue (P := P) hH hE har hbody hq hcq hts hS hchk
    exact coreInf_prepend (.silent (.inl st) run) (ih ω'' hs' hc' t' hS' hchk')
  | @loopInf s f stk bt body es np nr ω st l h0 har hit hω =>
    intro ω' hs hc labels ret out hts hS hchk
    obtain ⟨q, hq, hqc⟩ := substInf_regroup (Shape.streamConcat_map OCall.lift hω) hs
    have hcq := cons_of_concat hqc hc
    choose vs hit₁ hit₂ using hit
    let K : Nat → Config H := fun n => ⟨(st n).1, (st n).2.1, xcode (st n).2.2 (.loop bt body :: es)⟩
    have inv : ∀ n, TagsOk tags (st n).1 ∧ StoreChkE (ehExt tags) (st n).1.funcs ∧
        chkE (ehExt tags) (st n).1.funcs (st n).2.1.module (st n).2.1.locals.length ret labels
          (some (st n).2.2.length) (.loop bt body :: es) = some out := by
      intro n
      induction n with
      | zero => rw [h0]; exact ⟨hts, hS, hchk⟩
      | succ n ih =>
        obtain ⟨-, t', hS', hchk'⟩ := loopBack_glue (P := P) hH hE (har n) (hit₁ n) (hq n)
          (hcq n) ih.1 ih.2.1 ih.2.2
        rw [hit₂ n]
        exact ⟨t', hS', hchk'⟩
    have seg : ∀ n, EvRun P host (K n) (q n) (K (n + 1)) := by
      intro n
      obtain ⟨⟨c₁, st', run⟩, -, -, -⟩ := loopBack_glue (P := P) hH hE (har n) (hit₁ n) (hq n)
        (hcq n) (inv n).1 (inv n).2.1 (inv n).2.2
      simp only [K]
      rw [hit₂ n]
      exact .silent (.inl st') run
    have := coreInf_of_segments K q seg hqc
    simpa [K, h0] using this
  | @cond s f stk bt c t el es ω _ ih =>
    intro ω' hs hc labels ret out hts hS hchk
    obtain ⟨o, h1, -⟩ := chk_consE.mp hchk
    obtain ⟨oc, hco, -⟩ := chk1_ifE h1
    rw [show xcode stk (.if_ bt c t el :: es) = _ from code_if stk bt c t el es]
    exact coreInf_plug (.suffix _ .hole) (ih ω' hs hc hts hS hco)
  | arm hcE hb har _ ih =>
    intro ω' hs hc labels ret out hts hS hchk
    obtain ⟨q, ω'', rfl, hq, hs', hcq, hc'⟩ := split_stream hs hc
    obtain ⟨t', hS', ⟨ob, hbc⟩, run⟩ := arm_glue (P := P) hH hE hcE hb har hq hcq hts hS hchk
    exact coreInf_prepend run (coreInf_plug _ (ih ω'' hs' hc' t' hS' hbc))
  | ifK hcE hb har harm hvs _ ih =>
    intro ω' hs hc labels ret out hts hS hchk
    obtain ⟨q, ω'', rfl, hq, hs', hcq, hc'⟩ := split_stream hs hc
    have hE' := EvalLXPh.ifOk hcE hb har harm hvs (es := []) .nil
    rw [List.append_nil] at hE'
    obtain ⟨run, t', hS', hchk'⟩ := head_glue (P := P) hH hE hE' hq hcq hts hS hchk
    exact coreInf_prepend run (ih ω'' hs' hc' t' hS' hchk')
  | @handler s f stk bt cs body es np nr ω har _ ih =>
    intro ω' hs hc labels ret out hts hS hchk
    obtain ⟨⟨ob, hbc⟩, enter⟩ := try_enter (P := P) har hchk
    exact coreInf_enter _ enter (ih ω' hs hc hts hS hbc)
  | @tryK _ _ _ _ _ _ _ cs _ _ _ _ _ _ _ har hbody hvs _ ih =>
    intro ω' hs hc labels ret out hts hS hchk
    obtain ⟨q, ω'', rfl, hq, hs', hcq, hc'⟩ := split_stream hs hc
    have hE' := EvalLXPh.tryOk (cs := cs) har hbody hvs (es := []) .nil
    rw [List.append_nil] at hE'
    obtain ⟨run, t', hS', hchk'⟩ := head_glue (P := P) hH hE hE' hq hcq hts hS hchk
    exact coreInf_prepend run (ih ω'' hs' hc' t' hS' hchk')

/-- **An infinite chain of descents is a productive Core run**, from the first call. -/
theorem infChain_fwd {x : (wasmHShape H).self.Op} {ω : Nat → Call (wasmHostSig H)}
    (h : Shape.InfChain wasmHOpenXP (Shape.close wasmHOpenXP) x ω) (hc : ConsInf host ω)
    (hx : CallChkP tags x.2.2 x.1 x.2.1) {c₀ : Config H} (hat : AtCall x c₀) :
    CoreInf P host c₀ ω := by
  classical
  obtain ⟨gs, q, rfl, hd, hp, hu⟩ := h
  have hq : StreamConcat q ω := ⟨hp, hu⟩
  have hcq := cons_of_concat hq hc
  have D : ∀ n (c : Config H), AtCall (gs n) c → CallChkP tags (gs n).2.2 (gs n).1 (gs n).2.1 →
      ∃ c', EvRun P host c (q n) c' ∧ AtCall (gs (n + 1)) c' ∧
        CallChkP tags (gs (n + 1)).2.2 (gs (n + 1)).1 (gs (n + 1)).2.1 := by
    intro n c hat hx
    obtain ⟨c₁, c₂, st, run, hat', hy⟩ := descends_fwd (P := P) hH hE (hd n) (hcq n) hx hat
    exact ⟨c₂, .silent (.inl st) run, hat', hy⟩
  let K : (n : Nat) → {c : Config H // AtCall (gs n) c ∧
      CallChkP tags (gs n).2.2 (gs n).1 (gs n).2.1} := fun n =>
    Nat.rec (motive := fun n => {c : Config H // AtCall (gs n) c ∧
        CallChkP tags (gs n).2.2 (gs n).1 (gs n).2.1})
      ⟨c₀, hat, hx⟩
      (fun n Kn => ⟨Classical.choose (D n Kn.1 Kn.2.1 Kn.2.2),
        (Classical.choose_spec (D n Kn.1 Kn.2.1 Kn.2.2)).2⟩) n
  have seg : ∀ n, EvRun P host (K n).1 (q n) (K (n + 1)).1 :=
    fun n => (Classical.choose_spec (D n (K n).1 (K n).2.1 (K n).2.2)).1
  exact coreInf_of_segments (fun n => (K n).1) q seg hq

/-- **The converse bridge**: a productive run of `wasmEvInfNXP` whose answers the host allows is
a productive Core run of the invocation with exactly those events. -/
theorem wasmEvInfNXP_coreInf {s : Store H} {a : Nat} {vs : List Val} (hts : TagsOk tags s)
    (hS : StoreChkE (ehExt tags) s.funcs) (hok : InvokeOk s a vs)
    {ω : Nat → Call (wasmHostSig H)} (h : ω ∈ wasmEvInfNXP s (a, vs)) (hc : ConsInf host ω) :
    CoreInf P host (invoke s a vs) ω := by
  obtain ⟨fi, hfi, hx⟩ := invoke_callChk hS hts hok
  have hat := invoke_atCall (vs := vs) hfi
  rcases h with hch | ⟨z, qs, ν, ω', hpath, ⟨fz, fn, ω₀, hfz, hcode, hinf, rfl⟩, hsi, rfl⟩
  · exact infChain_fwd hH hE hch hc hx hat
  · obtain ⟨hcq, hc'⟩ := consInf_split hc
    obtain ⟨c₁, run₁, ⟨E, F, pre, c₀, rest, hcr, rfl⟩, hcc⟩ :=
      descPath_fwd (P := P) hH hE hpath hcq hx hat
    obtain ⟨hSz, htz, fi', ps, rs, hfi', hty, hn⟩ := hcc
    obtain rfl : fi' = fz := Option.some.inj (hfi'.symm.trans hfz)
    obtain ⟨ob, hbc⟩ := body_chk hSz hfz hcode hty hn
    have st := enter_body (P := P) (E := E) (F := F) (pre := pre) (rest := rest) hcr hfz hcode hty hn
    have hbody := infLXP_fwd (P := P) hH hE hinf ω' hsi hc' htz hSz hbc
    refine coreInf_prepend run₁ ?_
    simpa [Shape.streamAppend_nil] using
      coreInf_prepend (.silent (.inl st) (.refl _)) (coreInf_plug _ hbody)

end Fwd

end Silmaril.Proofs.Wasm.Abstract.HostClosingInfXP

module

public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.LaterCore

/-!
# A later core instantiation that fails quietly

* `nodeQuiet_ready_calls`: in the fragment, a node that is ready with only quiet import calls makes
  no import call at all (each import is wired to a call of `f`), so it is `NodeCalls` with no calls;
* `laterFailStep`: from `LaterInv` at a later core instantiation whose IR node fails quietly (its
  preparation fails, or its start function traps without an import call), the machine runs live to
  a specification trap: the preparation in the shared store fails (`prepareE_gap`), or the start
  run, in the shared store (`run_gap`), traps (`coreTrap`);
* `later_fail`: the later definitions up to a failing node (quiet ready nodes before it, run by
  `laterCoreStep'` with no calls) run live to a specification trap;
* `laterFail_ref`: a quiet failure of node `k ≥ 1` of a binary of `MultiImpFrag` makes the
  reference machine's instantiation trap, given the first node (`FirstK'`);
* `failRefWiredRest'_of_rest''_of_firstK'`: `Task.failRefWiredRest'` from
  `Task.failRefWiredRest''` (its rest) and `FirstK'`.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi

open Silmaril.Games Silmaril.Games.Inst
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore
open Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp
open Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.DecoderBridge
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Instantiate
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Component.InstRef Silmaril.Wasm.Component.InstLitmus
  Silmaril.Wasm.Component.InstTestsRef
open Silmaril.Wasm.Component.Conformance
open Silmaril.Wasm.Component.Reference.Core3Adder (first)
open Silmaril.Wasm.SingleThreaded (GrowOracle Internal status neverFail profile)

local notation "Σh" => Unit × List HLinked2.HostEvent

/-! ## Quiet ready nodes make no call -/

/-- The first import call of a typed start run passes one `i32`. -/
theorem startRun_first {imps : CoreIface} {c c' : (core3P (profile neverFail)).Config Nat}
    {y : Σ _ : (sigN imps.length).Op, Option Payload}
    {cs : List (Σ _ : (sigN imps.length).Op, Option Payload)}
    (hrun : Param.StartRunI (core3P (profile neverFail)) imps c (y :: cs) c') (hR : RTN c.1 c.2) :
    ∃ (h : Fin imps.length) (b : BitVec 32), y.1 = (h, .flat [⟨.int .i32, b⟩]) := by
  cases hrun with
  | @call s s₁ t t₁ h args c'' cs run callout hh r rest =>
    unfold Engine.CoreEngine.Steps at run
    rw [internalP_eqN] at run
    have hR₁ : RTN s₁ t₁ := rtN_run run hR
    obtain ⟨args', hst', hfl⟩ :=
      Silmaril.Wasm.Component.Engine.Core3.Typed.flatStatus_eq_callout' callout
    have hs₁ : status neverFail s₁ t₁ = .callout h args' :=
      (statusP_profile s₁ t₁).symm.trans hst'
    obtain ⟨b, rfl⟩ := args_of_calloutN hR₁ hs₁
    simp only [List.mapM_cons, List.mapM_nil, Silmaril.Wasm.SingleThreaded.toFlat?] at hfl
    cases hfl
    exact ⟨⟨h, hh⟩, b, rfl⟩

/-- **A ready node with quiet import calls makes none.** -/
theorem nodeQuiet_ready_calls {p : Binary.CoreMod × List Impl} (hok : NodeOk p)
    (hq : NodeQuiet hostI.length .ready p.1 p.2) : NodeCalls hostI.length .ready p.1 p.2 [] := by
  obtain ⟨ys, hEI, hys⟩ := hq
  refine ⟨ys, hEI, ?_⟩
  cases ys with
  | nil => exact .nil
  | cons y ys =>
    exfalso
    change EngineInst (core3P (profile neverFail))
      (Param.instOfI (core3P (profile neverFail)) (Binary.coreModule p.1) (CoreModule.imports p.1)
        (CoreModule.exports p.1)) (CoreModule.imports p.1) (y :: ys) _ at hEI
    obtain ⟨-, hsome⟩ := instOfI_cases hok.imps hok.names
    obtain ⟨J, hJ, ⟨-, hnil⟩ | ⟨f, c', fvs, hfs, hrun, -⟩⟩ := hEI
    · cases hnil
    · obtain ⟨mi', hp⟩ := hsome J hJ
      rw [hfs] at hp
      obtain ⟨hs', -, ⟨new, hnew, hwasm⟩, hcfg⟩ :=
        Silmaril.Wasm.Component.Engine.Core3.Typed.prepareE?_typed
          (storeOk_irStore (CoreModule.imports p.1).length) hp
      have hR : RTN J.store (Silmaril.Wasm.SingleThreaded.Thread.invoke f []) := by
        refine ⟨hs', hcfg f rfl, fun fi hfi h hcode => ?_⟩
        rw [hnew] at hfi
        rcases List.mem_append.mp hfi with hfi | hfi
        · simp only [irStore, List.mem_map, List.mem_range] at hfi
          obtain ⟨i, -, rfl⟩ := hfi
          rfl
        · obtain ⟨c, hc⟩ := hwasm fi hfi
          rw [hc] at hcode
          cases hcode
      obtain ⟨h, b, hy⟩ := startRun_first hrun hR
      have hq := hys y List.mem_cons_self
      rw [hy] at hq
      obtain ⟨k, hk, -⟩ := implsN_lowF hok.wires (n := (CoreModule.imports p.1).length) (h := h)
        (by have := h.isLt; have := hok.wl; omega) b
      have e : implsN hostI.length p.2 (CoreModule.imports p.1).length
          (h, .flat [⟨.int .i32, b⟩]) =
          implsN 1 p.2 (CoreModule.imports p.1).length (h, .flat [⟨.int .i32, b⟩]) := rfl
      rw [e, hk] at hq
      cases hq

/-! ## A failing later core instantiation -/

/-- A trap or a throw, mapped into the shared store, is a trap or a throw. -/
theorem code_gap_trap (δ : GShift) {code : List Silmaril.Wasm.Execution.Core.Admin}
    (h : code = [.trap] ∨ ∃ a, code = Silmaril.Wasm.Execution.Core.throwing a) :
    δ.code code = [.trap] ∨ ∃ a, δ.code code = Silmaril.Wasm.Execution.Core.throwing a := by
  rcases h with rfl | ⟨a, rfl⟩
  · left; simp
  · right; exact ⟨δ.ex + a, by simp [GShift.ref, Silmaril.Wasm.Execution.Core.throwing]⟩

/-- **A later core instantiation that fails quietly traps**: the machine runs live, from the
definitions `.coreInstance (.instantiate mi cargs) :: ds` with the invariant, to a configuration
taking a specification trap step. -/
def LaterFailStep : Prop :=
  ∀ (pre : RefComponent) (mi : Nat) (cargs : List (String × Nat)) (ds : RefComponent)
    (sc : Scope (core3 neverFail)) (M : Machine.Config (core3 neverFail) Σh)
    (m : Silmaril.Wasm.Module) (p : Binary.CoreMod × List Impl)
    (K : Scope (core3 neverFail) → Canon.P (core3 neverFail) Σh (Ret (core3 neverFail))),
    (coreMods pre)[mi]? = some m →
    postDefOk (preLowers pre) (preInsts pre) (coreMods pre)
      (.coreInstance (.instantiate mi cargs)) = true →
    Binary.coreModule p.1 = m → (CoreModule.imports p.1).length = m.imports.length → NodeOk p →
    NodeQuiet hostI.length (.fail ()) p.1 p.2 →
    LaterInv pre sc M →
    M.ctl = [.ofProg none
      ((Syntax.Definition.coreInstance (.instantiate mi cargs) :: ds).foldlM
        (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI)) sc >>= K)] →
    ∃ (tr : List (Label (core3 neverFail) Σh)) (mT m' : Machine.Config (core3 neverFail) Σh)
      (r : TrapReason),
      LRun first.prof embL.hr (DG embL.host) M tr mT ∧ Live mT ∧
      Step first.prof embL.hr (DG embL.host) mT (.trap r) m' ∧ ∀ msg, r ≠ .internal msg

theorem laterFailStep : LaterFailStep := by
  intro pre mi cargs ds sc M m p K hmi hok hmod hilen hno hq hI hctl
  obtain ⟨hsplit, hit, hbelow, hlow, hrt, hfun⟩ := postDefOk_core hmi hok
  have hle := imports_le hbelow hlow
  have hseg : m.data = [] ∧ m.elems = [] := by
    simp only [splitMod, Bool.and_eq_true, List.isEmpty_iff] at hsplit
    exact ⟨hsplit.1.2, hsplit.2⟩
  obtain ⟨ys, hEI, hys⟩ := hq
  change EngineInst (core3P (profile neverFail))
    (Param.instOfI (core3P (profile neverFail)) (Binary.coreModule p.1) (CoreModule.imports p.1)
      (CoreModule.exports p.1)) (CoreModule.imports p.1) ys _ at hEI
  have hnames := hno.names
  rw [hmod] at hEI hnames
  have hIR := nodeFailImp_cases (o := neverFail) hnames hno.imps hno.wl hno.wires hEI hys
  rw [hilen] at hIR
  -- the gap of the shared store
  let g : Gap (CanonHost (core3 neverFail)) := ⟨M.store.core, m.imports.length⟩
  have htr : ∀ i, i < g.b → g.pre.funcs[i]? = some (lowFI lowH) :=
    fun i hi => hI.tramp i (Nat.lt_of_lt_of_le hi hle)
  have hP₀ := preOk_irStore g htr
  have hinj : Function.Injective g.sh.fn := fnMap_injective g (PreOk.le_pre g hP₀)
  have hmd : sc.frame.coreModule? mi = some m := by
    simp only [Frame.coreModule?, hI.mods]
    exact hmi
  have hci := coreImportsFor_shared (o := neverFail) (s := M.store.core) (h := lowH) hI.insts
    (fun i hi => hI.tramp i (Nat.lt_of_lt_of_le hi hle)) hlow hrt
  have hX : (List.foldlM (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI)) sc
      (Syntax.Definition.coreInstance (.instantiate mi cargs) :: ds) >>= K) =
      (instantiateCore ⟨0⟩ sc.frame mi cargs >>= fun es =>
        (pushEntry sc.frame (.core .instance_) (.coreInstance es) >>= fun f =>
          pure ({ sc with frame := f } : Scope (core3 neverFail))) >>= fun sc =>
        List.foldlM (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI)) sc ds >>= K) := by
    erw [List.foldlM_cons]
    simp only [instantiateDef, bind_assoc]
  let Kc : List (String × (core3 neverFail).ExternVal) →
      Canon.P (core3 neverFail) Σh (Ret (core3 neverFail)) := fun es =>
    (pushEntry sc.frame (.core .instance_) (.coreInstance es) >>= fun f =>
      pure ({ sc with frame := f } : Scope (core3 neverFail))) >>= fun sc =>
    List.foldlM (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI)) sc ds >>= K
  have hM : M = { M with ctl := ⟨none, .prog (instantiateCore ⟨0⟩ sc.frame mi cargs >>= Kc), []⟩ :: [] } := by
    obtain ⟨S, h₀, conts, ctl, pending, results, cancels⟩ := M
    simp only at hctl ⊢
    rw [hctl, ← hX]
    rfl
  cases hv : Silmaril.Wasm.Validation.validate? m with
  | none =>
    -- the preparation fails
    have hpn : (core3 neverFail).prepare? M.store.core m
        ((List.range (Core3.importTypesE m).length).map
          Silmaril.Wasm.Execution.Core.ExternAddr.func) = none := by
      show Core3.prepareE? _ m _ = none
      unfold Core3.prepareE?
      rw [hv]
    obtain ⟨tr, mT, ht⟩ := instantiateCore_noneX (dispatch := DG embL.host) hmd hci hpn
    obtain ⟨q, segs', rr, hrr, r₂, hlive, hu⟩ :=
      ht.lrun (prof := first.prof) (hr := embL.hr) hI.lock Kc [] []
    rw [← hM] at r₂
    exact ⟨_, _, _, rr, r₂, hlive, hu.1, hrr⟩
  | some mt =>
  rw [importTypesE_length hv] at hci
  have hpg := prepareE_gap g htr hseg
  rcases hIR with hnone | ⟨s', mi', a, c, hp, hrun, hst⟩
  · -- the preparation fails
    rw [hnone] at hpg
    have hpn : (core3 neverFail).prepare? M.store.core m
        ((List.range m.imports.length).map Silmaril.Wasm.Execution.Core.ExternAddr.func) = none :=
      hpg
    obtain ⟨tr, mT, ht⟩ := instantiateCore_noneX (dispatch := DG embL.host) hmd hci hpn
    obtain ⟨q, segs', rr, hrr, r₂, hlive, hu⟩ :=
      ht.lrun (prof := first.prof) (hr := embL.hr) hI.lock Kc [] []
    rw [← hM] at r₂
    exact ⟨_, _, _, rr, r₂, hlive, hu.1, hrr⟩
  · -- the start function traps
    rw [hp] at hpg
    have hpr : (core3 neverFail).prepare? M.store.core m
        ((List.range m.imports.length).map Silmaril.Wasm.Execution.Core.ExternAddr.func) =
        some (g.rel (Store.mapH FirstImp.gL s'), g.sh.minst mi', some (g.sh.fn a)) := hpg
    obtain ⟨hsJ, -, ⟨newJ, hnewJ, hwasmJ⟩, hcfgJ⟩ :=
      Silmaril.Wasm.Component.Engine.Core3.Typed.prepareE?_typed hI.ok hpg
    have hHT : HostTy (g.rel (Store.mapH FirstImp.gL s')) := by
      intro fi hfi h hcode
      rw [hnewJ] at hfi
      rcases List.mem_append.mp hfi with hfi | hfi
      · exact hI.hosts fi hfi h hcode
      · obtain ⟨c, hc⟩ := hwasmJ fi hfi
        rw [hc] at hcode
        cases hcode
    -- the core instantiation, up to its start call
    have hF₂ := instantiateCore_startX (prof := first.prof) (hr := embL.hr)
      (dispatch := DG embL.host) hmd hci hpr
    obtain ⟨K', tr₁, r₁⟩ := hF₂ Kc [] [] hI.lock
    rw [← hM] at r₁
    obtain ⟨ι, hιs, hιok⟩ := hI.inst
    obtain ⟨ι', hadd, -, -, -⟩ := inst_round hιok ⟨M.store.threads.length⟩
    obtain ⟨M₀, thc, Kc₀, segsc, restc, tr₂, r₂, hc₀, hcore₀, hl₀⟩ :=
      start_coreG (impl := embL.host) first.prof
        { ({ M with store := setCoreSt (g.rel (Store.mapH FirstImp.gL s')) M.store } :
            Machine.Config (core3 neverFail) Σh) with
          ctl := [⟨none, .prog (Instantiate.runStart ⟨0⟩ (g.sh.fn a) >>= K'), []⟩] }
        _ ι ι' rfl hI.lock hιs hadd
    -- the IR's instance: good, related to the shared store
    have hsOk₀ : Silmaril.Wasm.Execution.Core.StoreOk
        (Store.mapH FirstImp.gL (irStore m.imports.length)) := by
      rw [mapH_irStore]
      exact storeOk_lowStore _ _
    have hp₀ := prepareE_mapH FirstImp.gL (irStore m.imports.length) m
      ((List.range m.imports.length).map Silmaril.Wasm.Execution.Core.ExternAddr.func)
    rw [hp] at hp₀
    obtain ⟨-, -, ⟨newI, hnewI, -⟩, -⟩ :=
      Silmaril.Wasm.Component.Engine.Core3.Typed.prepareE?_typed hsOk₀ hp₀
    have hPJ : g.PreOk (Store.mapH FirstImp.gL s').funcs := by
      rw [hnewI]
      exact preOk_extend g hP₀
    obtain ⟨mtI, f', st₀, -, -, hi, -, hst₀⟩ :=
      Silmaril.Wasm.Component.Engine.Core3.Typed.prepareE?_inv hp
    have hi' : Silmaril.Wasm.Execution.Core.instantiateOnce? (irStore m.imports.length)
        { m with start := none }
        (Silmaril.Wasm.Link.GC.Preparation.imports (List.range m.imports.length)) =
        some (s', f', none) := by
      rw [instantiateOnce?_noStart,
        show Silmaril.Wasm.Link.GC.Preparation.imports (List.range m.imports.length) =
          (List.range m.imports.length).map Silmaril.Wasm.Execution.Core.ExternAddr.func from rfl,
        hi]
      rfl
    have hprof : Silmaril.Wasm.Link.GC.inProfile { m with start := none } = true := by
      simp only [splitMod, Bool.and_eq_true, List.isEmpty_iff] at hsplit
      simp [Silmaril.Wasm.Link.GC.inProfile, hsplit.1.1.1.1, hsplit.1.1.1.2, hsplit.1.1.2,
        hsplit.1.2, hsplit.2]
      exact List.all_eq_true.mp hfun
    obtain ⟨hgood, hmodg⟩ := storeGood_once hprof hi'
      (fun fi hfi c hc => by
        simp only [irStore, List.mem_map, List.mem_range] at hfi
        obtain ⟨i, -, rfl⟩ := hfi
        cases hc)
      rfl rfl rfl (fun a ha => by simpa [irStore] using ha)
    obtain ⟨x, -, hx⟩ := hst₀ a rfl
    have hfa : (show Nat from a) < (Store.mapH FirstImp.gL s').funcs.length := by
      have h1 : (show Nat from a) < s'.funcs.length := hmodg.funcs a (List.mem_of_getElem? hx)
      simpa [Store.mapH] using h1
    have hgood' := (storeGood_mapH_iff FirstImp.gL s').mpr hgood
    have hG : GapThr g s' (Silmaril.Wasm.SingleThreaded.Thread.invoke a [])
        (Silmaril.Wasm.SingleThreaded.Thread.invoke (g.sh.fn a) []) :=
      ⟨invoke_gap g hPJ a, splitGood_invoke hgood' hfa (fun _ h => by cases h), hPJ⟩
    have hRT : RT (g.rel (Store.mapH FirstImp.gL s'))
        (Silmaril.Wasm.SingleThreaded.Thread.invoke (g.sh.fn a) []) :=
      ⟨hsJ, hcfgJ (g.sh.fn a) rfl, hHT⟩
    have hM₀ : coreCfg M₀ thc Kc₀ segsc restc
        (g.rel (Store.mapH FirstImp.gL s'),
          Silmaril.Wasm.SingleThreaded.Thread.invoke (g.sh.fn a) []) = M₀ := by
      have e := coreCfg_self hc₀
      rw [hcore₀] at e
      exact e
    -- the start run, to the trap
    have hcode := code_of_status_trap hst
    rw [← code_config_mapHG (g := FirstImp.gL)] at hcode
    obtain ⟨tR', tr₃, r₃, hG', -, hsc⟩ := run_gap (prof := first.prof) (th := thc) (K := Kc₀)
      (segs := segsc) (rest := restc) (B := M₀) hl₀ g hinj hrun hG hRT
      (fun tR' hth => by
        rw [status_trap_of_code (by rw [hth]; exact code_gap_trap g.sh hcode)]
        nofun)
    rw [hM₀] at r₃
    have hst' : status neverFail (g.rel (Store.mapH FirstImp.gL c.1)) tR' = .returned .trap :=
      status_trap_of_code (by rw [hG'.cfg]; exact code_gap_trap g.sh hcode)
    have hst3 := status_core3_trap (o := neverFail) (hsc.trans hst')
    exact ⟨tr₁ ++ (tr₂ ++ tr₃), _, _, .coreTrap, r₁.trans (r₂.trans r₃),
      ⟨List.cons_ne_nil _ _, hl₀⟩, (UniqueStep.of_core rfl (by
        show (core3 neverFail).status (g.rel (Store.mapH FirstImp.gL c.1)) tR' ≠ _ ∧
          (core3 neverFail).status (g.rel (Store.mapH FirstImp.gL c.1)) tR' ≠ _
        rw [hst3]; exact ⟨nofun, nofun⟩)
        (.coreTrap rfl hst3)).1, fun _ h => by cases h⟩

/-! ## The later definitions, to the failing node -/

/-- **The later definitions, up to a failing node**: the IR's nodes `ps` of the definitions `ds`
are quiet and ready before `ps[j]`, which fails quietly; the machine runs live to a specification
trap. -/
theorem later_fail {pre : RefComponent} :
    ∀ (ds : RefComponent) (R Rf : RSt) (sc : Scope (core3 neverFail))
      (M : Machine.Config (core3 neverFail) Σh)
      (K : Scope (core3 neverFail) → Canon.P (core3 neverFail) Σh (Ret (core3 neverFail)))
      (L : List HLinked2.HostEvent) (ps : List (Binary.CoreMod × List Impl)) (j : Nat),
      ds.foldlM refStep R = some Rf →
      ds.all (postDefOk (preLowers pre) (preInsts pre) (coreMods pre)) = true →
      (∃ X, Rf.nodes = R.nodes ++ X ∧ List.Forall₂ NodeW (coreNodes ps) X) →
      (∀ p ∈ ps, NodeOk p) →
      (∀ i q, i < j → ps[i]? = some q → NodeQuiet hostI.length .ready q.1 q.2) →
      (∃ q, ps[j]? = some q ∧ NodeQuiet hostI.length (.fail ()) q.1 q.2) →
      FrameRel (coreMods pre) R sc → LaterInv pre sc M →
      M.ctl = [.ofProg none
        (ds.foldlM (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI)) sc >>= K)] →
      M.host = ((), L) →
      ∃ (tr : List (Label (core3 neverFail) Σh)) (mT m' : Machine.Config (core3 neverFail) Σh)
        (r : TrapReason),
        LRun first.prof embL.hr (DG embL.host) M tr mT ∧ Live mT ∧
        Step first.prof embL.hr (DG embL.host) mT (.trap r) m' ∧ ∀ msg, r ≠ .internal msg
  | [], R, Rf, sc, M, K, L, ps, j, hfold, _, hX, _, _, hfail, _, _, _, _ => by
    simp only [List.foldlM_nil] at hfold
    cases hfold
    obtain ⟨X, hX, hW⟩ := hX
    have hX0 : X = [] := by simpa using hX.symm
    subst hX0
    have hps : ps = [] := by
      cases ps with
      | nil => rfl
      | cons _ _ => cases hW
    subst hps
    obtain ⟨q, hq, -⟩ := hfail
    cases hq
  | d :: ds, R, Rf, sc, M, K, L, ps, j, hfold, hpost, hX, hok, hready, hfail, hF, hL, hc, hh => by
    simp only [List.foldlM_cons] at hfold
    cases hR : refStep R d with
    | none => rw [hR] at hfold; cases hfold
    | some R₁ =>
    rw [hR] at hfold
    simp only [List.all_cons, Bool.and_eq_true] at hpost
    obtain ⟨hd, hpost⟩ := hpost
    obtain ⟨X, hX, hW⟩ := hX
    obtain ⟨Y, hY, -⟩ := foldlM_refStep_nodes hfold
    by_cases hi : IsInst d
    · obtain ⟨mi, cargs, rfl⟩ : ∃ mi cargs, d = .coreInstance (.instantiate mi cargs) := by
        cases d with
        | coreInstance ci => cases ci with
          | instantiate mi cargs => exact ⟨mi, cargs, rfl⟩
          | exports => exact hi.elim
        | _ => exact hi.elim
      obtain ⟨m, nm, imps, exps, w, hm, hci, hRn, -⟩ := refStep_inst hR
      have hm' : (coreMods pre)[mi]? = some m := by rw [← hF.rmods]; exact hm
      have hXY : X = (m, w) :: Y := by
        rw [hY, hRn] at hX
        simpa using hX.symm
      subst hXY
      obtain ⟨p, ps', rfl, hpW, hW'⟩ : ∃ p ps', ps = p :: ps' ∧ NodeW (.core p.1 p.2) (m, w) ∧
          List.Forall₂ NodeW (coreNodes ps') Y := by
        cases ps with
        | nil => cases hW
        | cons p ps' => cases hW with | cons h1 h2 => exact ⟨p, ps', rfl, h1, h2⟩
      obtain ⟨cm, he, hdec, hcif⟩ := hpW
      injection he with he₁ he₂
      subst he₁
      have hmod : Binary.coreModule p.1 = m := by
        unfold Binary.coreModule
        rw [hdec]
        rfl
      have hilen : (CoreModule.imports p.1).length = m.imports.length :=
        (FirstImp.coreIface_imports_length hcif).symm ▸ rfl
      rcases j with _ | j
      · obtain ⟨q, hq, hqf⟩ := hfail
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hq
        subst hq
        exact laterFailStep pre mi cargs ds sc M m p K hm' hd hmod hilen
          (hok p List.mem_cons_self) hqf hL hc
      · have hq0 := hready 0 p (Nat.zero_lt_succ _) rfl
        have hnc := nodeQuiet_ready_calls (hok p List.mem_cons_self) hq0
        obtain ⟨tr₁, M₁, sc₁, es, d₁, -, -, hc₁, hL₁, hh₁, -, hci₁, hcf₁, -, hE, hty₁, hfn₁⟩ :=
          laterCoreStep' pre mi cargs ds sc M m p [] L K hm' hd hmod hilen
            (hok p List.mem_cons_self) hnc (fun _ h => by cases h) hL hc hh
        have hF₁ := frameRel_inst hF hR hm' hci₁ hcf₁ hty₁ hfn₁ hE
        obtain ⟨tr₂, mT, m', r, d₂, hlive, hs, hr⟩ :=
          later_fail ds _ Rf sc₁ M₁ K (L ++ logOfCalls []) ps' j hfold hpost ⟨Y, hY, hW'⟩
            (fun q hq => hok q (List.mem_cons_of_mem _ hq))
            (fun i q hij hq => hready (i + 1) q (by omega) (by simpa using hq))
            (by simpa using hfail) hF₁ hL₁ hc₁ hh₁
        exact ⟨tr₁ ++ tr₂, mT, m', r, d₁.trans d₂, hlive, hs, hr⟩
    · obtain ⟨sc₁, M₁, hT, hF₁, hL₁, hh₁⟩ := nonCore_step hd hi hR hF hL
      obtain ⟨tr₁, hq, -⟩ := sruns_tau (dispatch := DG embL.host) hT none rfl
      have d₁ := RunsQ.lrun_at (prof := first.prof) (hr := embL.hr) hq hL.lock
        (fun sc' => ds.foldlM (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI)) sc' >>= K)
        (segs := []) (rest := []) (by rw [hc, ctl_cons]; rfl)
      obtain ⟨Y₁, hY₁, hY₁'⟩ := refStep_nodes hR
      have hY0 := hY₁' hi
      subst hY0
      obtain ⟨tr₂, mT, m', r, d₂, hlive, hs, hr⟩ :=
        later_fail ds R₁ Rf sc₁ { M₁ with ctl := _ } K L ps j hfold hpost
          ⟨X, by rw [hX, hY₁, List.append_nil], hW⟩ hok hready hfail hF₁
          (hL₁.congr rfl rfl (fs := []) (by simp)) rfl (by rw [← hh, ← hh₁])
      exact ⟨tr₁ ++ tr₂, mT, m', r, d₁.trans d₂, hlive, hs, hr⟩

/-! ## A later node fails -/

/-- **A failure of node `k ≥ 1` of a binary of the fragment**, after quiet ready nodes, makes the
reference machine's instantiation trap (given the first node, `FirstK'`). -/
theorem laterFail_ref (h1 : FirstK') {b : ByteArray} {c : Comp Binary.CoreMod} {r : RefComponent}
    {ps : List (Binary.CoreMod × List Impl)} {k : Nat} (hk : k < ps.length) (hk0 : 0 < k)
    (hpc : Binary.parseComponent b = .ok c) (hr : decodeRef b = .ok r) (hf : MultiImpFrag r)
    (himp : c.imports = hostI) (hnodes : c.nodes = coreNodes ps)
    (hq : ∀ j (hj : j < k), NodeQuiet hostI.length .ready (ps[j]'(by omega)).1 (ps[j]'(by omega)).2)
    (hfl : NodeQuiet hostI.length (.fail ()) ps[k].1 ps[k].2) :
    InstResult.traps ∈
      instBehaviours first.prof (Host.ofEmbedder embL) hostConfigX r (importArgs hostI) := by
  obtain ⟨-, hw, -, pre, mi, cargs, post, hs, -, hpostOk⟩ := multiImpFrag_inv hf
  obtain ⟨p, ps', rfl⟩ := nodes_ne_nil hpc hr hf hnodes
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hok := nodeOk_frag hpc hr hf hnodes
  have h₀ : NodeCalls hostI.length .ready p.1 p.2 [] :=
    nodeQuiet_ready_calls (hok p List.mem_cons_self) (hq 0 hk0)
  obtain ⟨sc, M, ⟨⟨tr₀, hs₀, hn₀, ht₀⟩, ⟨K, -, hc⟩, -, hh⟩, hL, hFR⟩ :=
    h1 b c r p ps' [] pre mi cargs post hpc hr hf himp hnodes (fun _ h => by cases h) h₀ hs
  obtain ⟨R, hR, -, -, hN⟩ := relW_of_decode hpc hr (inFrag_of_hostWired hw)
  rw [hnodes] at hN
  have hrr := firstCore?_eq r hs
  unfold refRead at hR
  have hsplit : r = (pre ++ [Syntax.Definition.coreInstance (.instantiate mi cargs)]) ++ post := by
    rw [hrr]; simp
  rw [hsplit, foldlM_option_append] at hR
  cases hR₀ : (pre ++ [Syntax.Definition.coreInstance (.instantiate mi cargs)]).foldlM refStep
      ({ env := (r.filter isFuncImport).length } : RSt) with
  | none =>
    rw [← hsplit, hR₀] at hR
    cases hR
  | some R₀ =>
  rw [← hsplit, hR₀] at hR
  simp only [Option.bind_some] at hR
  rw [foldlM_option_append] at hR₀
  cases hR₁ : pre.foldlM refStep ({ env := (r.filter isFuncImport).length } : RSt) with
  | none => rw [hR₁] at hR₀; cases hR₀
  | some R₁ =>
  rw [hR₁] at hR₀
  simp only [Option.bind_some, List.foldlM_cons, List.foldlM_nil] at hR₀
  obtain ⟨Y₁, hY₁, hY₁'⟩ := foldlM_refStep_nodes hR₁
  have hY₁0 := hY₁' (firstCore?_noInst r hs)
  subst hY₁0
  cases hci : refStep R₁ (.coreInstance (.instantiate mi cargs)) with
  | none => rw [hci] at hR₀; cases hR₀
  | some R₂ =>
  rw [hci] at hR₀
  have hR₀' : R₂ = R₀ := by simpa using hR₀
  subst hR₀'
  obtain ⟨m0, -, -, -, w0, -, -, hn2, -⟩ := refStep_inst hci
  obtain ⟨X, hX, -⟩ := foldlM_refStep_nodes hR
  rw [hX, hn2, hY₁] at hN
  simp only [List.append_nil] at hN
  have hN' : List.Forall₂ NodeW (coreNodes ps') X := by
    simp only [List.nil_append, List.singleton_append] at hN
    cases hN with | cons _ h => exact h
  obtain ⟨tr₁, mT, m', rT, d, hlive, hstep, hrT⟩ :=
    later_fail post _ R sc M K (logOfCalls []) ps' k' hR hpostOk ⟨X, hX, hN'⟩
      (fun q hq => hok q (List.mem_cons_of_mem _ hq))
      (fun i q hi hiq => by
        obtain ⟨hlt, e⟩ := List.getElem?_eq_some_iff.mp hiq
        have := hq (i + 1) (by omega)
        simp only [List.getElem_cons_succ, e] at this
        exact this)
      ⟨ps'[k']'(by simp at hk; omega), by simp, by simpa using hfl⟩
      (hFR _ (by rw [foldlM_option_append, hR₁]; simp [hci])) hL hc hh
  have hready : HostReadyCfg hostConfigX := ⟨rfl, rfl, rfl⟩
  have hsteps := Adequacy.steps_append (hs₀.trans d).steps (.cons hstep (.refl _))
  refine ⟨m', tr₀ ++ tr₁ ++ [Label.trap rT], .cons (.hostRun hready) hsteps, ?_, ?_,
    Adequacy.step_trap_lockdown hstep⟩
  · intro ev hev
    simp only [List.mem_append, List.mem_singleton] at hev
    rcases hev with (h | h) | h
    · exact hn₀ ev h
    · exact Adequacy.LRun.no_host d ev h
    · cases h
  · intro msg hev
    simp only [List.mem_append, List.mem_singleton] at hev
    rcases hev with (h | h) | h
    · exact ht₀ msg h
    · exact Adequacy.LRun.no_trap d hlive _ h
    · simp only [Label.trap.injEq] at h
      exact hrT msg h.symm

/-- **`Task.failRefWiredRest'` from its rest outside the fragment's later failures**, given the
first node (`FirstK'`): the case `MultiImpFrag r ∧ 0 < k` is `laterFail_ref`. -/
theorem failRefWiredRest'_of_rest''_of_firstK' (h1 : FirstK') (h : Task.failRefWiredRest'') :
    Task.failRefWiredRest' := by
  intro b c r ps k hk hor hpc hr hv hw himp hn hq hfl
  by_cases hm : MultiImpFrag r ∧ 0 < k
  · exact laterFail_ref h1 hk hm.2 hpc hr hm.1 himp hn hq hfl
  · exact h b c r ps k hk hm hor hpc hr hv hw himp hn hq hfl

end Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi

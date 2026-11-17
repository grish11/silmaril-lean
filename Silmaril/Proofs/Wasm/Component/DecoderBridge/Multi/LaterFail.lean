module

public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.LaterCore

/-!
# A later core instantiation that fails quietly

* `nodeQuiet_ready_calls`: in the fragment, a node that is ready with only quiet import calls makes
  no import call at all (each import is wired to a call of `f`), so it is `NodeCalls` with no calls;
* `laterFailStep`: from `LaterInv` at a later core instantiation whose IR node fails quietly (its
  preparation fails, or its start function traps without an import call), the machine runs live to
  a specification trap: the preparation in the shared store fails (`prepareE_gap`), or the start
  run, in the shared store (`run_gap`), traps (`coreTrap`).
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

end Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi

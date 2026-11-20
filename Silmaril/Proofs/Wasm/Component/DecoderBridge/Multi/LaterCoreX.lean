module

public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.NodesX
public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.LaterCore

/-!
# A later core instantiation with its node end (`LaterCoreStepX`)

`Multi.LaterCore.laterCoreStep'` for the IR's node ending at `x` (`NodeEnd`): the same run, its
gap `g` (the shared store before the core instantiation, the module's imports) kept in the
statement, so the shared core store after it is `g.rel` of the IR's store after the start
function, and the core instance the IR's module instance relocated.
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

/-- **A later core instantiation in the shared core store, with its node end.** -/
theorem laterCoreStepX : LaterCoreStepX := by
  intro pre mi cargs ds sc M m p nx L K hmi hok hmod hilen hno hq hu hI hctl hhost
  obtain ⟨hsplit, hit, hbelow, hlow, hrt, hfun⟩ := postDefOk_core hmi hok
  have hle := imports_le hbelow hlow
  have hseg : m.data = [] ∧ m.elems = [] := by
    simp only [splitMod, Bool.and_eq_true, List.isEmpty_iff] at hsplit
    exact ⟨hsplit.1.2, hsplit.2⟩
  obtain ⟨-, hp, ys, hF, hstart⟩ := hq
  obtain ⟨hlog, hans⟩ := coreLog_eq hno.wires hno.wl hF hu
  rw [hmod, hilen] at hp
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
  cases hv : Silmaril.Wasm.Validation.validate? m with
  | none =>
    exfalso
    unfold Core3.prepareE? at hp
    rw [hv] at hp
    cases hp
  | some mt =>
  rw [importTypesE_length hv] at hci
  have hpg := prepareE_gap g htr hseg
  rw [hp] at hpg
  have hpr : (core3 neverFail).prepare? M.store.core m
      ((List.range m.imports.length).map Silmaril.Wasm.Execution.Core.ExternAddr.func) =
      some (g.rel (Store.mapH FirstImp.gL nx.inst.store), g.sh.minst nx.minst, nx.inst.start.map g.sh.fn) := hpg
  -- the typing of the shared store after the preparation
  obtain ⟨hsJ, -, ⟨newJ, hnewJ, hwasmJ⟩, hcfgJ⟩ :=
    Silmaril.Wasm.Component.Engine.Core3.Typed.prepareE?_typed hI.ok hpg
  have hHT : HostTy (g.rel (Store.mapH FirstImp.gL nx.inst.store)) := by
    intro fi hfi h hcode
    rw [hnewJ] at hfi
    rcases List.mem_append.mp hfi with hfi | hfi
    · exact hI.hosts fi hfi h hcode
    · obtain ⟨c, hc⟩ := hwasmJ fi hfi
      rw [hc] at hcode
      cases hcode
  have hfunsJ : ∀ i, i < preLowers pre →
      (g.rel (Store.mapH FirstImp.gL nx.inst.store)).funcs[i]? = some (lowFI lowH) := by
    intro i hi
    have h₀ := hI.tramp i hi
    rw [hnewJ, List.getElem?_append_left (List.getElem?_eq_some_iff.mp h₀).1]
    exact h₀
  -- the exports of the new core instance
  have hexps := instExports_minst g.sh (prepareE?_exports hseg hp)
  -- the program at the core instantiation
  have hX : (List.foldlM (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI)) sc
      (Syntax.Definition.coreInstance (.instantiate mi cargs) :: ds) >>= K) =
      (instantiateCore ⟨0⟩ sc.frame mi cargs >>= fun es =>
        (pushEntry sc.frame (.core .instance_) (.coreInstance es) >>= fun f =>
          pure ({ sc with frame := f } : Scope (core3 neverFail))) >>= fun sc =>
        List.foldlM (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI)) sc ds >>= K) := by
    erw [List.foldlM_cons]
    simp only [instantiateDef, bind_assoc]
  have hM : M = { M with ctl := ⟨none, .prog (instantiateCore ⟨0⟩ sc.frame mi cargs >>= fun es =>
        (pushEntry sc.frame (.core .instance_) (.coreInstance es) >>= fun f =>
          pure ({ sc with frame := f } : Scope (core3 neverFail))) >>= fun sc =>
        List.foldlM (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI)) sc ds >>= K), []⟩ :: [] } := by
    obtain ⟨S, h₀, conts, ctl, pending, results, cancels⟩ := M
    simp only at hctl ⊢
    rw [hctl, ← hX]
    rfl
  have hpush : ∀ (es : List (String × (core3 neverFail).ExternVal))
      (m₂ : Machine.Config (core3 neverFail) Σh),
      RunsQ (DG embL.host) none (pushEntry sc.frame (.core .instance_) (.coreInstance es) >>= fun f =>
        pure ({ sc with frame := f } : Scope (core3 neverFail))) m₂ []
        ({ sc with frame := { sc.frame with coreInstances := sc.frame.coreInstances ++ [es] } } :
          Scope (core3 neverFail)) m₂ := by
    intro es m₂
    simp only [pushEntry, need, orTrap, Frame.push, pure_bind]
    exact .pure _ _
  have hinsts' : ∀ es : List (String × (core3 neverFail).ExternVal),
      ∃ X : List (List (String × Silmaril.Wasm.Execution.Core.ExternAddr)),
        sc.frame.coreInstances ++ [es] = (instsVal (preInsts pre) ++ X :
          List (List (String × Silmaril.Wasm.Execution.Core.ExternAddr))) := by
    intro es
    obtain ⟨X, hX⟩ := hI.insts
    refine ⟨X ++ [show List (String × Silmaril.Wasm.Execution.Core.ExternAddr) from es], ?_⟩
    rw [hX]
    exact List.append_assoc _ _ _
  have hsOk₀ : Silmaril.Wasm.Execution.Core.StoreOk
      (Store.mapH FirstImp.gL (irStore m.imports.length)) := by
    rw [mapH_irStore]
    exact storeOk_lowStore _ _
  have hp₀ := prepareE_mapH FirstImp.gL (irStore m.imports.length) m
    ((List.range m.imports.length).map Silmaril.Wasm.Execution.Core.ExternAddr.func)
  rw [hp] at hp₀
  obtain ⟨-, -, ⟨newI, hnewI, -⟩, -⟩ :=
    Silmaril.Wasm.Component.Engine.Core3.Typed.prepareE?_typed hsOk₀ hp₀
  have hPJ : g.PreOk (Store.mapH FirstImp.gL nx.inst.store).funcs := by
    rw [hnewI]
    exact preOk_extend g hP₀
  rcases hstart with ⟨hnone, rfl, hxs⟩ | ⟨f, c', fvs, hfs, hrun, hst, hxs⟩
  · -- no start function
    have ht : nx.calls = [] := List.forall₂_nil_left_iff.mp hF
    rw [hnone] at hpr
    have hcore' : RunsQ (DG embL.host) none (instantiateCore ⟨0⟩ sc.frame mi cargs) M
        [.tau, .tau] ((core3 neverFail).exports (g.sh.minst nx.minst))
        { M with store := setCoreSt (g.rel (Store.mapH FirstImp.gL nx.inst.store)) M.store } := by
      unfold instantiateCore
      simp only [hmd, need, orTrap]
      refine RunsQ.bind (tr₁ := []) (.pure _ _) ?_
      refine RunsQ.bind (tr₁ := [.tau]) (.get (.pure _ _)) ?_
      rw [hci]
      refine RunsQ.bind (tr₁ := []) (.pure _ _) ?_
      erw [hpr]
      exact RunsQ.bind (tr₁ := [.tau])
        (.modify (f := setCoreSt (E := core3 neverFail) (g.rel (Store.mapH FirstImp.gL nx.inst.store)))
          rfl (.pure _ _))
        (.pure _ _)
    have d := RunsQ.lrun_at (prof := first.prof) (hr := embL.hr)
      (RunsQ.bind (f := fun es =>
          pushEntry sc.frame (.core .instance_) (.coreInstance es) >>= fun f =>
            pure ({ sc with frame := f } : Scope (core3 neverFail))) hcore' (hpush _ _))
      hI.lock
      (fun sc => List.foldlM (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI)) sc ds >>= K)
      (segs := []) (rest := []) (by rw [hM]; simp only [bind_assoc])
    refine ⟨_, _, _, g, d, Adequacy.LRun.no_host d,
      Adequacy.LRun.no_trap d ⟨List.cons_ne_nil _ _, hI.lock⟩, by simp [traceObs, Label.obs?], rfl, ⟨hI.mods, hinsts' _,
        hI.lock, hI.func0, hI.inst, hfunsJ, hsJ, hHT, hI.depth⟩, by rw [hhost, ht]; simp [logOfCalls],
      rfl, rfl, rfl, rfl, hexps, rfl, rfl, rfl, by rw [hxs]; exact hPJ, by rw [hxs]; rfl,
      ⟨[], (List.append_nil _).symm⟩, rfl, rfl⟩
  · -- a start function
    rw [hfs] at hpr
    have hrun' : Param.StartRunI (core3P (profile neverFail)) (CoreModule.imports p.1)
        (nx.inst.store, Silmaril.Wasm.SingleThreaded.Thread.invoke f []) ys c' := hrun
    -- the core instantiation, up to its start call
    have hR : Reaches first.prof embL.hr (DG embL.host) none
        (Instantiate.runStart ⟨0⟩ (g.sh.fn f)) (instantiateCore ⟨0⟩ sc.frame mi cargs) M
        ([] ++ ([.tau] ++ ([] ++ ([.tau] ++ []))))
        { M with store := setCoreSt (g.rel (Store.mapH FirstImp.gL nx.inst.store)) M.store }
        (fun m₂ tr' a m' => RunsQ (DG embL.host) none
          ((fun _ => pure ((core3 neverFail).exports (g.sh.minst nx.minst))) ()) m₂ tr' a m') := by
      unfold instantiateCore
      simp only [hmd, need, orTrap]
      refine Reaches.seq (tr₁ := []) (.pure _ _) ?_
      refine Reaches.seq (tr₁ := [.tau]) (.get (.pure _ _)) ?_
      rw [hci]
      refine Reaches.seq (tr₁ := []) (.pure _ _) ?_
      erw [hpr]
      refine Reaches.seq (tr₁ := [.tau])
        (.modify (f := setCoreSt (E := core3 neverFail) (g.rel (Store.mapH FirstImp.gL nx.inst.store)))
          rfl (.pure _ _)) ?_
      exact Reaches.here _ _
    obtain ⟨K', d₂, hK'⟩ := hR (fun es =>
        (pushEntry sc.frame (.core .instance_) (.coreInstance es) >>= fun f =>
          pure ({ sc with frame := f } : Scope (core3 neverFail))) >>= fun sc =>
        List.foldlM (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI)) sc ds >>= K) [] []
        hI.lock
    rw [← hM] at d₂
    -- the start call, to the core activation
    obtain ⟨ι, hιs, hιok⟩ := hI.inst
    obtain ⟨ι', hadd, hrem, hι₁, hml⟩ := inst_round hιok ⟨M.store.threads.length⟩
    obtain ⟨M₀, thc, Kc, segsc, restc, tr₃, d₃, hob₃, hS⟩ := start_atG (impl := embL.host) first.prof
      { ({ M with store := setCoreSt (g.rel (Store.mapH FirstImp.gL nx.inst.store)) M.store } :
          Machine.Config (core3 neverFail) Σh) with
        ctl := ⟨none, .prog (Instantiate.runStart ⟨0⟩ (g.sh.fn f) >>= K'), []⟩ :: [] }
      (g.sh.fn f) ι ι' rfl hI.lock hιs hadd hrem
    have hB : CallInv M₀ thc := by
      have hth₀ := hS.thread
      subst hth₀
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hS.store]; exact hI.lock
      · rw [hS.store]; exact calloutEntry_gStore₃ _ _ _
      · rw [hS.store]; exact ⟨ι', rfl, hml⟩
      · rw [hS.store]; exact funcs0_append hI.func0 _
    -- the IR's instance: its store, good, and related to the shared store
    obtain ⟨mtI, f', st₀, -, -, hi, -, hst₀⟩ :=
      Silmaril.Wasm.Component.Engine.Core3.Typed.prepareE?_inv hp
    have hi' : Silmaril.Wasm.Execution.Core.instantiateOnce? (irStore m.imports.length) { m with start := none }
        (Silmaril.Wasm.Link.GC.Preparation.imports (List.range m.imports.length)) =
        some (nx.inst.store, f', none) := by
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
    obtain ⟨x, -, hx⟩ := hst₀ f hfs
    have hfa : (show Nat from f) < (Store.mapH FirstImp.gL nx.inst.store).funcs.length := by
      have h1 : (show Nat from f) < nx.inst.store.funcs.length := hmodg.funcs f (List.mem_of_getElem? hx)
      simpa [Store.mapH] using h1
    have hgood' := (storeGood_mapH_iff FirstImp.gL nx.inst.store).mpr hgood
    have hG : GapThr g nx.inst.store (Silmaril.Wasm.SingleThreaded.Thread.invoke f [])
        (Silmaril.Wasm.SingleThreaded.Thread.invoke (g.sh.fn f) []) :=
      ⟨invoke_gap g hPJ f, splitGood_invoke hgood' hfa (fun _ h => by cases h), hPJ⟩
    have hRT : RT (g.rel (Store.mapH FirstImp.gL nx.inst.store))
        (Silmaril.Wasm.SingleThreaded.Thread.invoke (g.sh.fn f) []) :=
      ⟨hsJ, hcfgJ (g.sh.fn f) (by rw [hfs]; rfl), hHT⟩
    have hM₀ : coreCfg M₀ thc Kc segsc restc
        (g.rel (Store.mapH FirstImp.gL nx.inst.store),
          Silmaril.Wasm.SingleThreaded.Thread.invoke (g.sh.fn f) []) = M₀ := by
      have e := coreCfg_self hS.ctl
      have hco : M₀.store.core = g.rel (Store.mapH FirstImp.gL nx.inst.store) := by
        rw [hS.store]; rfl
      rw [hco] at e
      exact e
    -- the start run with its host calls
    obtain ⟨tr₄, B', tR', d₄, hob₄, hst', hG', hB', hhost', hExt, hRT'⟩ := startRun_gapX
      (prof := first.prof) (K := Kc) (segs := segsc) (rest := restc) hno.imps g hinj hrun' hans
      hst hB hG hRT
    rw [hM₀] at d₄
    -- no values
    have hfv : fvs = [] := by
      have := Silmaril.Wasm.Component.Engine.Core3.Typed.returned_typed (o := neverFail) (rs := [])
        ⟨hRT'.store, fun fi hfi h hc => ⟨_, hRT'.hosts fi hfi h hc⟩⟩ hRT'.thread hst'
      simpa using this
    subst hfv
    have d₅ := retStep (th := thc) (K := Kc) (segs := segsc) (rest := restc)
      (y := (g.rel (Store.mapH FirstImp.gL c'.1), tR')) hst' hB'.lock
    -- the epilogue
    obtain ⟨h, xs, cs, rfl⟩ := hExt
    obtain ⟨tr₆, d₆, hob₆⟩ := hS.ret (g.rel (Store.mapH FirstImp.gL c'.1), tR') h xs cs
    -- back in the core instantiation, then the core instance on the frame
    obtain ⟨d₇, -⟩ := hK' (startedCfgG embL.host
      { ({ M with store := setCoreSt (g.rel (Store.mapH FirstImp.gL nx.inst.store)) M.store } :
          Machine.Config (core3 neverFail) Σh) with
        ctl := ⟨none, .prog (Instantiate.runStart ⟨0⟩ (g.sh.fn f) >>= K'), []⟩ :: [] }
      (g.sh.fn f) ι' (g.rel (Store.mapH FirstImp.gL c'.1)) h xs cs) []
      ((core3 neverFail).exports (g.sh.minst nx.minst)) _ (.pure _ _) hI.lock
    have d₈ := RunsQ.lrun_at (prof := first.prof) (hr := embL.hr)
      (hpush ((core3 neverFail).exports (g.sh.minst nx.minst))
        { startedCfgG embL.host
          { ({ M with store := setCoreSt (g.rel (Store.mapH FirstImp.gL nx.inst.store)) M.store } :
              Machine.Config (core3 neverFail) Σh) with
            ctl := ⟨none, .prog (Instantiate.runStart ⟨0⟩ (g.sh.fn f) >>= K'), []⟩ :: [] }
          (g.sh.fn f) ι' (g.rel (Store.mapH FirstImp.gL c'.1)) h xs cs with
          ctl := ⟨none, .prog ((pushEntry sc.frame (.core .instance_)
            (.coreInstance ((core3 neverFail).exports (g.sh.minst nx.minst))) >>= fun f =>
              pure ({ sc with frame := f } : Scope (core3 neverFail))) >>= fun sc =>
            List.foldlM (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI)) sc ds >>= K), []⟩ ::
              [] })
      hI.lock
      (fun sc => List.foldlM (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI)) sc ds >>= K)
      (segs := []) (rest := []) rfl
    have d := d₂.trans (d₃.trans (d₄.trans (d₅.trans (d₆.trans (d₇.trans d₈)))))
    have hfc : (g.rel (Store.mapH FirstImp.gL c'.1)).funcs =
        (g.rel (Store.mapH FirstImp.gL nx.inst.store)).funcs := by
      simp only [rel_funcs, Store.mapH, startRunI_funcs hrun']
    refine ⟨_, _, _, g, d, Adequacy.LRun.no_host d,
      Adequacy.LRun.no_trap d ⟨List.cons_ne_nil _ _, hI.lock⟩, by
        simp only [traceObs] at hob₃ hob₄ hob₆ ⊢
        simp only [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, Label.obs?,
          hob₃, hob₄, hob₆, List.nil_append, List.append_nil], rfl, ⟨hI.mods, hinsts' _,
        hI.lock, funcs0_append hI.func0 _, ⟨ι₁, by rw [← hι₁]; rfl, .inr rfl⟩,
        fun i hi => by rw [show (startedCfgG embL.host _ (g.sh.fn f) ι'
          (g.rel (Store.mapH FirstImp.gL c'.1)) h xs cs).store.core =
          g.rel (Store.mapH FirstImp.gL c'.1) from rfl, hfc]; exact hfunsJ i hi,
        hRT'.store, hRT'.hosts, hI.depth⟩, ?_, rfl, rfl, rfl, rfl, hexps, rfl, rfl, rfl, ?_,
        by rw [hxs]; rfl, ⟨_, rfl⟩, rfl, rfl⟩
    case refine_2 =>
      have hfx : (Store.mapH FirstImp.gL c'.1).funcs = (Store.mapH FirstImp.gL nx.inst.store).funcs := by
        simp only [Store.mapH, startRunI_funcs hrun']
      rw [hxs, hfx]
      exact hPJ
    show h = _
    have hh : h = (M₀.host.1, M₀.host.2 ++ coreLog ys) := hhost'
    rw [hh, hS.host]
    show ((M.host.1, M.host.2 ++ coreLog ys) : Σh) = _
    rw [hhost, hlog]


end Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi

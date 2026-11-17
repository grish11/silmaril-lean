module

public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.RootK

/-!
# The first node with a finishing continuation and the machine invariant

`firstK : FirstK`: `Multi.First.firstNodeRef` with the root's continuation kept
(`Multi.RootK.root_firstK`): the reference machine reaches the definitions after the first core
instantiation at `RefAtDefsK` (whose continuation finishes the instantiation, `KFin`), with the
machine invariant `LaterInv` (the frame's core modules and instances, the store not locked down,
the root import, the component instance fresh or after one start thread, the trampolines at the
start of the core store, which is typed with host functions of core type `fFlat`).
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

/-- The IR's start run keeps the functions of its store. -/
theorem startRunI_funcs {imps : CoreIface} :
    ∀ {c c' : (core3P (profile neverFail)).Config Nat}
      {ys : List (Σ _ : (sigN imps.length).Op, Option Payload)},
      Param.StartRunI (core3P (profile neverFail)) imps c ys c' → c'.1.funcs = c.1.funcs := by
  intro c c' ys h
  induction h with
  | @nil c c' run =>
    obtain ⟨s, t⟩ := c
    obtain ⟨s', t'⟩ := c'
    unfold Engine.CoreEngine.Steps at run
    rw [internalP_eq] at run
    exact funcs_stepsG run
  | @call s s₁ t t₁ h args c'' cs run callout hh r rest' ih =>
    unfold Engine.CoreEngine.Steps at run
    rw [internalP_eq] at run
    have e := funcs_stepsG run
    simp only at e ih ⊢
    exact ih.trans e

/-- The component instance after one start thread. -/
theorem removeThread_ι₁ {ι' : InstState} (h : ({} : InstState).addThread? ⟨0⟩ = some (1, ι')) :
    InstState.removeThread 1 ι' = ι₁ := by
  have e : ({} : InstState).addThread? ⟨0⟩ =
      some (1, { threads := ⟨#[none, some ⟨0⟩], []⟩ }) := rfl
  rw [e] at h
  cases h
  rfl

/-- **The first node with a finishing continuation and the machine invariant.** -/
theorem firstK : FirstK := by
  intro b c r p ps t₀ pre mi cargs post hc hr hf himp hn hu hq hs
  obtain ⟨hfi, hw, -, pre₁, mi₁, cargs₁, post₁, hs₁, hshape, hpostOk⟩ := multiImpFrag_inv hf
  rw [hs] at hs₁
  obtain ⟨rfl, rfl, rfl, rfl⟩ : pre = pre₁ ∧ mi = mi₁ ∧ cargs = cargs₁ ∧ post = post₁ := by
    simp only [Option.some.injEq, Prod.mk.injEq] at hs₁
    exact ⟨hs₁.1, hs₁.2.1, hs₁.2.2.1, hs₁.2.2.2⟩
  have hpostNI := noImport_of_postOk hpostOk
  obtain ⟨pre', post', mi', cargs', m, hs', hpre, hm, hlen, hlow, hrt, hmod, himps, hilen, hwl, hw',
    hnames⟩ := firstImp_setup hc hr hw hfi himp hn
  rw [hs] at hs'
  simp only [Option.some.injEq, Prod.mk.injEq] at hs'
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hs'
  obtain ⟨ys, hEI, hF⟩ := hq
  obtain ⟨hlog, hans⟩ := coreLog_eq hw' hwl hF hu
  change EngineInst (core3P (profile neverFail))
    (Param.instOfI (core3P (profile neverFail)) (Binary.coreModule p.1) (CoreModule.imports p.1)
      (CoreModule.exports p.1)) (CoreModule.imports p.1) ys _ at hEI
  rw [hmod] at hEI
  obtain ⟨-, hsome⟩ := instOfI_cases himps hnames
  obtain ⟨J, hJ, hstart⟩ := hEI
  obtain ⟨mi₂, hp⟩ := hsome J hJ
  rw [hilen] at hp
  -- the root, up to the first core instantiation
  obtain ⟨sc', Kr, hF', hKF, hfm, -, hfi'⟩ := root_firstK hs hpre hshape hpostNI
  obtain ⟨tr₁, -, d₁⟩ := hF' (fun _ => pure .unit) [] [] rfl
  generalize hK : (fun b => Kr b >>= fun _ => pure Ret.unit) = K at d₁
  have hKF' : KFin K := hK ▸ hKF
  let M₁ : Machine.Config (core3 neverFail) Σh := lowCfg hostConfigX (preLowers pre) lowH
  have hcore : M₁.store.core = lowStore m.imports.length lowH := by
    show lowStore (preLowers pre) lowH = _
    rw [hlen]
  have hmd : sc'.frame.coreModule? mi = some m := by
    simp only [Frame.coreModule?, hfm]
    exact hm
  have hci := coreImportsFor_low (o := neverFail) (h := lowH) (md := m) hfi' hlow hrt
  rw [← hcore] at hci
  cases hv : Silmaril.Wasm.Validation.validate? m with
  | none =>
    exfalso
    unfold Core3.prepareE? at hp
    rw [hv] at hp
    cases hp
  | some mt =>
  rw [importTypesE_length hv] at hci
  have hsh := prepareE_mapH (fun _ : Nat => lowH) (irStore m.imports.length) m
    ((List.range m.imports.length).map Silmaril.Wasm.Execution.Core.ExternAddr.func)
  rw [mapH_irStore, ← hcore] at hsh
  have hpr : (core3 neverFail).prepare? M₁.store.core m
      ((List.range m.imports.length).map Silmaril.Wasm.Execution.Core.ExternAddr.func) =
      some (Store.mapH gL J.store, mi₂, J.start) :=
    hsh.trans (by rw [hp]; rfl)
  have hready : HostReadyCfg hostConfigX := ⟨rfl, rfl, rfl⟩
  -- the typing of the core store after the preparation, and its trampolines
  have hsOk₀ : Silmaril.Wasm.Execution.Core.StoreOk
      (Store.mapH gL (irStore m.imports.length)) := by
    rw [mapH_irStore]
    exact storeOk_lowStore _ _
  have hp₀ := prepareE_mapH gL (irStore m.imports.length) m
    ((List.range m.imports.length).map Silmaril.Wasm.Execution.Core.ExternAddr.func)
  rw [hp] at hp₀
  obtain ⟨hsJ, -, ⟨newJ, hnewJ, hwasmJ⟩, -⟩ :=
    Silmaril.Wasm.Component.Engine.Core3.Typed.prepareE?_typed hsOk₀ hp₀
  have hHT : HostTy (Store.mapH gL J.store) := by
    intro fi hfi h hcode
    rw [hnewJ, mapH_irStore] at hfi
    rcases List.mem_append.mp hfi with hfi | hfi
    · simp only [lowStore, List.mem_replicate] at hfi
      rw [hfi.2]
      rfl
    · obtain ⟨c, hc⟩ := hwasmJ fi hfi
      rw [hc] at hcode
      cases hcode
  have htramp : ∀ i, i < preLowers pre →
      (Store.mapH gL J.store).funcs[i]? = some (lowFI lowH) := by
    intro i hi
    rw [hnewJ, mapH_irStore, List.getElem?_append_left (by simp [lowStore]; omega)]
    simp [lowStore, show i < m.imports.length by omega]
  -- the program at the first core instantiation
  have hX : (List.foldlM (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI)) sc'
      (Syntax.Definition.coreInstance (.instantiate mi cargs) :: post) >>= K) =
      (instantiateCore ⟨0⟩ sc'.frame mi cargs >>= fun es =>
        (pushEntry sc'.frame (.core .instance_) (.coreInstance es) >>= fun f =>
          pure ({ sc' with frame := f } : Scope (core3 neverFail))) >>= fun sc =>
        List.foldlM (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI)) sc post >>= K) := by
    erw [List.foldlM_cons]
    simp only [instantiateDef, bind_assoc]
  erw [hX] at d₁
  -- the core instance on the frame, then the definitions after it
  have hpush : ∀ (es : List (String × (core3 neverFail).ExternVal)) (m₂ : Machine.Config (core3 neverFail) Σh),
      RunsQ (DG embL.host) none (pushEntry sc'.frame (.core .instance_) (.coreInstance es) >>= fun f =>
        pure ({ sc' with frame := f } : Scope (core3 neverFail))) m₂ []
        ({ sc' with frame := { sc'.frame with coreInstances := sc'.frame.coreInstances ++ [es] } } :
          Scope (core3 neverFail)) m₂ := by
    intro es m₂
    simp only [pushEntry, need, orTrap, Frame.push, pure_bind]
    exact .pure _ _
  -- the final configuration is at the definitions after the first core instantiation
  have finish : ∀ (tr : List (Label (core3 neverFail) Σh)) (M : Machine.Config (core3 neverFail) Σh)
      (sc : Scope (core3 neverFail)),
      LRun first.prof embL.hr (DG embL.host)
        { hostConfigX with ctl := ⟨none, .prog (instantiateProg r (importArgs hostI) >>=
          fun _ => pure .unit), []⟩ :: [] } tr
        { M with ctl := ⟨none, .prog (List.foldlM (instantiateDef callRecurse ⟨0⟩ []
          (importArgs hostI)) sc post >>= K), []⟩ :: [] } →
      M.store.lockdown = false → M.host = ((), logOfCalls t₀) → LaterInv pre sc M →
      ∃ sc M, RefAtDefsK r post sc (logOfCalls t₀) M ∧ LaterInv pre sc M := by
    intro tr M sc d hl hh hinv
    refine ⟨sc, _, ⟨⟨tr, .cons (.hostRun hready) d.steps, Adequacy.LRun.no_host d,
      fun msg => Adequacy.LRun.no_trap d ⟨List.cons_ne_nil _ _, hl⟩ _⟩, ⟨K, hKF', rfl⟩, hl, hh⟩,
      ?_⟩
    exact ⟨hinv.mods, hinv.insts, hinv.lock, hinv.func0, hinv.inst, hinv.tramp, hinv.ok,
      hinv.hosts⟩
  rcases hstart with ⟨hnone, rfl⟩ | ⟨f, c', fvs, hfs, hrun, hst⟩
  · -- no start function
    have ht₀ : t₀ = [] := by cases hF; rfl
    subst ht₀
    rw [hnone] at hpr
    have hcore' : ∀ M : Machine.Config (core3 neverFail) Σh, M.store = M₁.store →
        RunsQ (DG embL.host) none (instantiateCore ⟨0⟩ sc'.frame mi cargs) M
        [.tau, .tau] ((core3 neverFail).exports mi₂)
        { M with store := setCoreSt (Store.mapH gL J.store) M.store } := by
      intro M hM
      unfold instantiateCore
      simp only [hmd, need, orTrap]
      refine RunsQ.bind (tr₁ := []) (.pure _ _) ?_
      refine RunsQ.bind (tr₁ := [.tau]) (.get (.pure _ _)) ?_
      have hci' := hci
      have hpr' := hpr
      rw [← hM] at hci' hpr'
      rw [hci']
      refine RunsQ.bind (tr₁ := []) (.pure _ _) ?_
      erw [hpr']
      exact RunsQ.bind (tr₁ := [.tau])
        (.modify (f := setCoreSt (E := core3 neverFail) (Store.mapH gL J.store)) rfl (.pure _ _))
        (.pure _ _)
    have d₂ := RunsQ.lrun_at (prof := first.prof) (hr := embL.hr) (RunsQ.bind (f := fun es =>
          pushEntry sc'.frame (.core .instance_) (.coreInstance es) >>= fun f =>
            pure ({ sc' with frame := f } : Scope (core3 neverFail))) (hcore' { M₁ with ctl :=
          ⟨none, .prog (instantiateCore ⟨0⟩ sc'.frame mi cargs >>= fun es =>
          (pushEntry sc'.frame (.core .instance_) (.coreInstance es) >>= fun f =>
            pure ({ sc' with frame := f } : Scope (core3 neverFail))) >>= fun sc =>
          List.foldlM (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI)) sc
            (post : List (Syntax.Definition (core3 neverFail).Module)) >>= K), []⟩ :: [] } rfl)
          (hpush _ _))
        (show M₁.store.lockdown = false from rfl)
        (fun sc => List.foldlM (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI)) sc
          (post : List (Syntax.Definition (core3 neverFail).Module)) >>= K) (segs := []) (rest := [])
        (by simp only [bind_assoc])
    refine finish _ _ _ (d₁.trans d₂) rfl rfl ⟨by simpa using hfm, ⟨[(core3 neverFail).exports mi₂], by simp only [hfi']; rfl⟩, rfl,
      rfl, ⟨{}, rfl, .inl rfl⟩, htramp, hsJ, hHT⟩
  · -- a start function
    rw [hfs] at hpr
    have hrun' : Param.StartRunI (core3P (profile neverFail)) (CoreModule.imports p.1)
        (J.store, Silmaril.Wasm.SingleThreaded.Thread.invoke f []) ys c' := hrun
    -- the core instantiation, up to its start call
    have hR : Reaches first.prof embL.hr (DG embL.host) none
        (Instantiate.runStart ⟨0⟩ f) (instantiateCore ⟨0⟩ sc'.frame mi cargs) M₁
        ([] ++ ([.tau] ++ ([] ++ ([.tau] ++ []))))
        { M₁ with store := setCoreSt (Store.mapH gL J.store) M₁.store }
        (fun m₂ tr' a m' => RunsQ (DG embL.host) none
          ((fun _ => pure ((core3 neverFail).exports mi₂)) ()) m₂ tr' a m') := by
      unfold instantiateCore
      simp only [hmd, need, orTrap]
      refine Reaches.seq (tr₁ := []) (.pure _ _) ?_
      refine Reaches.seq (tr₁ := [.tau]) (.get (.pure _ _)) ?_
      rw [hci]
      refine Reaches.seq (tr₁ := []) (.pure _ _) ?_
      erw [hpr]
      refine Reaches.seq (tr₁ := [.tau])
        (.modify (f := setCoreSt (E := core3 neverFail) (Store.mapH gL J.store)) rfl (.pure _ _)) ?_
      exact Reaches.here _ _
    obtain ⟨K', d₂, hK'⟩ := hR (fun es =>
        (pushEntry sc'.frame (.core .instance_) (.coreInstance es) >>= fun f =>
          pure ({ sc' with frame := f } : Scope (core3 neverFail))) >>= fun sc =>
        List.foldlM (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI)) sc
          (post : List (Syntax.Definition (core3 neverFail).Module)) >>= K) [] [] rfl
    -- the start call, to the core activation
    obtain ⟨ι', hadd, hrem⟩ : ∃ ι', ({} : InstState).addThread? ⟨0⟩ = some (1, ι') ∧
        ι'.removeThread? 1 = some (⟨0⟩, InstState.removeThread 1 ι') := ⟨_, rfl, rfl⟩
    obtain ⟨M₀, thc, Kc, segsc, restc, tr₃, d₃, hS⟩ := start_atG (impl := embL.host) first.prof
      { ({ M₁ with store := setCoreSt (Store.mapH gL J.store) M₁.store } :
          Machine.Config (core3 neverFail) Σh) with
        ctl := ⟨none, .prog (Instantiate.runStart ⟨0⟩ f >>= K'), []⟩ :: [] }
      f {} ι' rfl rfl rfl hadd hrem
    have hml : ι'.mayLeave = true := by
      unfold InstState.addThread? at hadd
      obtain ⟨⟨i, tb⟩, -, he⟩ := Option.map_eq_some_iff.mp hadd
      cases he
      rfl
    have hB : CallInv M₀ thc := by
      have hth₀ := hS.thread
      subst hth₀
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hS.store]; rfl
      · rw [hS.store]; rfl
      · rw [hS.store]; exact ⟨ι', rfl, hml⟩
      · rw [hS.store]; rfl
    -- the typing of the start thread
    have hsOk : Silmaril.Wasm.Execution.Core.StoreOk (Store.mapH gL (irStore m.imports.length)) := by
      rw [mapH_irStore]
      exact storeOk_lowStore _ _
    have hp' := prepareE_mapH gL (irStore m.imports.length) m
      ((List.range m.imports.length).map Silmaril.Wasm.Execution.Core.ExternAddr.func)
    rw [hp, hfs] at hp'
    obtain ⟨hs', -, ⟨new, hnew, hwasm⟩, hcfg⟩ :=
      Silmaril.Wasm.Component.Engine.Core3.Typed.prepareE?_typed hsOk hp'
    have hRT : RT (Store.mapH gL J.store) (Silmaril.Wasm.SingleThreaded.Thread.invoke f []) := by
      refine ⟨hs', hcfg f rfl, fun fi hfi h hcode => ?_⟩
      rw [hnew, mapH_irStore] at hfi
      rcases List.mem_append.mp hfi with hfi | hfi
      · simp only [lowStore, List.mem_replicate] at hfi
        rw [hfi.2]
        rfl
      · obtain ⟨c, hc⟩ := hwasm fi hfi
        rw [hc] at hcode
        cases hcode
    have hM₀ : coreCfg M₀ thc Kc segsc restc
        (Store.mapH gL J.store, Silmaril.Wasm.SingleThreaded.Thread.invoke f []) = M₀ := by
      have e := coreCfg_self hS.ctl
      have hco : M₀.store.core = Store.mapH gL J.store := by rw [hS.store]; rfl
      rw [hco] at e
      exact e
    -- the start run with its host calls
    obtain ⟨tr₄, B', tR', d₄, hst', hB', hhost, hExt, hRT'⟩ := startRun_refX (prof := first.prof)
      (K := Kc) (segs := segsc) (rest := restc) himps hrun' hans hst hB
      (tR := Silmaril.Wasm.SingleThreaded.Thread.invoke f []) rfl hRT
    rw [hM₀] at d₄
    -- no values
    have hfv : fvs = [] := by
      have := Silmaril.Wasm.Component.Engine.Core3.Typed.returned_typed (o := neverFail) (rs := [])
        ⟨hRT'.store, fun fi hfi h hc => ⟨_, hRT'.hosts fi hfi h hc⟩⟩ hRT'.thread hst'
      simpa using this
    subst hfv
    have d₅ := retStep (th := thc) (K := Kc) (segs := segsc) (rest := restc)
      (y := (Store.mapH gL c'.1, tR')) hst' hB'.lock
    -- the epilogue
    obtain ⟨h, xs, cs, rfl⟩ := hExt
    obtain ⟨tr₆, d₆⟩ := hS.ret (Store.mapH gL c'.1, tR') h xs cs
    -- back in the core instantiation, then the core instance on the frame
    obtain ⟨d₇, -⟩ := hK' (startedCfgG embL.host { ({ M₁ with store := setCoreSt (Store.mapH gL J.store) M₁.store } :
          Machine.Config (core3 neverFail) Σh) with
          ctl := ⟨none, .prog (Instantiate.runStart ⟨0⟩ f >>= K'), []⟩ :: [] }
          f ι' (Store.mapH gL c'.1) h xs cs) [] ((core3 neverFail).exports mi₂) _ (.pure _ _) rfl
    have d₈ := RunsQ.lrun_at (prof := first.prof) (hr := embL.hr) (hpush ((core3 neverFail).exports mi₂)
        { startedCfgG embL.host { ({ M₁ with store := setCoreSt (Store.mapH gL J.store) M₁.store } :
          Machine.Config (core3 neverFail) Σh) with
          ctl := ⟨none, .prog (Instantiate.runStart ⟨0⟩ f >>= K'), []⟩ :: [] }
          f ι' (Store.mapH gL c'.1) h xs cs with
          ctl := ⟨none, .prog ((pushEntry sc'.frame (.core .instance_)
            (.coreInstance ((core3 neverFail).exports mi₂)) >>= fun f =>
              pure ({ sc' with frame := f } : Scope (core3 neverFail))) >>= fun sc =>
            List.foldlM (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI)) sc
              (post : List (Syntax.Definition (core3 neverFail).Module)) >>= K), []⟩ :: [] })
      (show _ = false from rfl)
      (fun sc => List.foldlM (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI)) sc
        (post : List (Syntax.Definition (core3 neverFail).Module)) >>= K) (segs := []) (rest := [])
      rfl
    refine finish _ _ _ (d₁.trans (d₂.trans (d₃.trans (d₄.trans (d₅.trans (d₆.trans
      (d₇.trans d₈))))))) rfl ?_ ?_
    case refine_2 =>
      have hfc : (Store.mapH gL c'.1).funcs = (Store.mapH gL J.store).funcs := by
        simp only [Store.mapH, startRunI_funcs hrun']
      refine ⟨by simpa using hfm, ⟨[(core3 neverFail).exports mi₂], by simp only [hfi']; rfl⟩, rfl, rfl,
        ⟨ι₁, by rw [← removeThread_ι₁ hadd]; rfl, .inr rfl⟩, fun i hi => ?_, hRT'.store,
        hRT'.hosts⟩
      show (Store.mapH gL c'.1).funcs[i]? = _
      rw [hfc]
      exact htramp i hi
    show h = _
    have hh : h = (M₀.host.1, M₀.host.2 ++ coreLog ys) := hhost
    rw [hh, hS.host, hlog]
    rfl

end Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi

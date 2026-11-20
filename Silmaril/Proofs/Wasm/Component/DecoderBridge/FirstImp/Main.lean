module

public import Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp.IR
public import Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp.Read
public import Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore.Main

/-!
# The reference half when the first core instantiation, with lowered imports, fails

* `ref_firstImp_trap`: the reference machine (logging host, `hostConfigX`) traps on a component
  of the fragment `FirstImpFrag` whose first instantiated module, prepared against `n` fresh
  host functions of core type `fFlat` (`irStore n`), fails, or reports a start function whose
  run traps;
* `firstImp_fail_ref`: so it traps on every import-wired binary of the fragment importing
  `f: func(u32)` whose IR node `0` fails quietly (`NodeQuiet`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore
open Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.DecoderBridge
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Instantiate
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Component.InstRef Silmaril.Wasm.Component.InstLitmus
  Silmaril.Wasm.Component.InstTestsRef
open Silmaril.Wasm.Component.Reference.Core3Adder (first)
open Silmaril.Wasm.SingleThreaded (GrowOracle Internal status neverFail)

/-! ## Facts about the interface and the stores -/

theorem forIn_count {α σ ε : Type} {F : α → σ → Except ε (ForInStep σ)} (P : σ → Nat → Prop)
    (hF : ∀ x s r k, F x s = .ok r → P s k → ∃ s', r = .yield s' ∧ P s' (k + 1)) :
    ∀ (xs : List α) (s W : σ) (k : Nat), forIn xs s F = .ok W → P s k → P W (k + xs.length)
  | [], s, W, k, h, hs => by
    simp only [List.forIn_nil] at h
    cases h
    exact hs
  | x :: xs, s, W, k, h, hs => by
    simp only [List.forIn_cons] at h
    cases hx : F x s with
    | error e => rw [hx] at h; cases h
    | ok r =>
      rw [hx] at h
      obtain ⟨s', rfl, hs'⟩ := hF x s r k hx hs
      have := forIn_count P hF xs s' W (k + 1) h hs'
      simpa [Nat.add_assoc, Nat.add_comm 1] using this

/-- `coreIface` reads one import per import of the module. -/
theorem coreIface_imports_length {m : Silmaril.Wasm.Module} {n : List (String × String)}
    {i e : CoreIface} (h : coreIface m = .ok (n, i, e)) : i.length = m.imports.length := by
  unfold coreIface at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i v hv
    split at h
    · cases h
    · cases h
      have := forIn_count (fun (s : Array (String × String) × Array (String × CoreFuncTy)) k =>
          s.2.size = k) ?_ _ _ _ 0 hv rfl
      · simpa using this
      · intro x s r k hr hs
        rcases x with ⟨mn, nm, ty⟩
        cases ty with
        | func t =>
          simp only at hr
          split at hr
          · cases hr
          · cases hr
            exact ⟨_, rfl, by simp [hs]⟩
        | _ => cases hr

theorem storeOk_lowStore {H : Type} (h : H) :
    ∀ n, Silmaril.Wasm.Execution.Core.StoreOk (lowStore n h)
  | 0 => (Silmaril.Wasm.Component.Engine.Core3.Typed.empty_ok _).1
  | n + 1 => (Silmaril.Wasm.Component.Engine.Core3.Typed.allocHost_storeOk (storeOk_lowStore h n)
      (allocHost_lowStore n h)).1

theorem importTypesE_length {m : Silmaril.Wasm.Module} {mt : Silmaril.Wasm.Validation.CModuleType}
    (hv : Silmaril.Wasm.Validation.validate? m = some mt) :
    (Core3.importTypesE m).length = m.imports.length := by
  have he := congrArg List.length (Core3.importTypesE_eq hv)
  simp only [List.length_map, List.length_zip] at he
  obtain ⟨xtI, xtE⟩ := mt
  cases Silmaril.Wasm.Validation.validate?_sound hv with
  | mk _ himports => rw [he, ← himports.length_eq]; simp

/-- The trampoline of the fragment: the `canon lower` of `f` in the root instance. -/
abbrev lowH : CanonHost (core3 neverFail) := .lowered ⟨0⟩ fWit {} ⟨0⟩

theorem coreType_lowH (at_ : AddrTypes (core3 neverFail)) :
    (lowH : CanonHost (core3 neverFail)).coreType at_ = Param.v1Type fFlat := by
  simp only [CanonHost.coreType, CanonOpts.abiOptions, CanonOpts.ptrType]
  decide +kernel

theorem importArgs_hostI_func :
    ∀ n v, (importArgs hostI : Exports (core3 neverFail)).lookup n = some v → v = .func ⟨0⟩ := by
  intro n v h
  simp only [importArgs, hostI, List.mapIdx_cons, List.mapIdx_nil, List.lookup_cons,
    List.lookup_nil] at h
  split at h
  · cases h; rfl
  · cases h

/-! ## The reference machine -/

/-- **The reference half for the first core instantiation with lowered imports**: when the
module of the first core instantiation, prepared against `n` fresh host functions of core type
`fFlat`, fails, or reports a start function whose run traps, the reference machine's
instantiation traps. -/
theorem ref_firstImp_trap {r : Core3Component} {pre post : Core3Component} {mi : Nat}
    {cargs : List (String × Nat)} {m : Silmaril.Wasm.Module}
    (hs : firstCore? r = some (pre, mi, cargs, post)) (hpre : preOk 0 0 pre = true)
    (hm : (coreMods pre)[mi]? = some m) (hn : m.imports.length = preLowers pre)
    (hlow : importsLowered cargs (preInsts pre) m = true) (hrt : refTypesOk m = true)
    (hIR : Core3.prepareE? (irStore m.imports.length) m
          ((List.range m.imports.length).map Silmaril.Wasm.Execution.Core.ExternAddr.func) = none ∨
      ∃ s' mi' a c, Core3.prepareE? (irStore m.imports.length) m
          ((List.range m.imports.length).map Silmaril.Wasm.Execution.Core.ExternAddr.func) =
          some (s', mi', some a) ∧
        Relation.ReflTransGen (Internal neverFail)
          (s', Silmaril.Wasm.SingleThreaded.Thread.invoke a []) c ∧
        status neverFail c.1 c.2 = .returned .trap) :
    InstResult.traps ∈ instBehaviours first.prof (Host.ofEmbedder embL) hostConfigX r
      (importArgs hostI) := by
  have hready : HostReadyCfg hostConfigX := ⟨rfl, rfl, rfl⟩
  rcases root_firstX (prof := first.prof) (hr := embL.hr) (dispatch := DG embL.host)
      (fx := .host fWit ⟨0⟩) hs hpre argsOk_hostI importArgs_hostI_func rfl coreType_lowH rfl rfl
      rfl with ⟨tr, mT, ht⟩ | ⟨f, hF, hfm, -, hfi⟩
  · obtain ⟨m', h⟩ := instTraps_of_trapsQS (prof := first.prof) (hr := embL.hr) hready ht
    exact ⟨m', h⟩
  · have hmd : f.coreModule? mi = some m := by
      simp only [Frame.coreModule?, hfm]
      exact hm
    let M₁ : Machine.Config (core3 neverFail) _ := lowCfg hostConfigX (preLowers pre) lowH
    have hcore : M₁.store.core = lowStore m.imports.length lowH := by
      show lowStore (preLowers pre) lowH = _
      rw [hn]
    have hci := coreImportsFor_low (o := neverFail) (h := lowH) (md := m) hfi hlow hrt
    rw [← hcore] at hci
    have trapNone : ∀ xs, coreImportsFor? M₁.store.core m cargs f = some xs →
        (core3 neverFail).prepare? M₁.store.core m xs = none →
        InstResult.traps ∈ instBehaviours first.prof (Host.ofEmbedder embL) hostConfigX r
          (importArgs hostI) := by
      intro xs hc hpr
      obtain ⟨tr, mT, ht⟩ := instantiateCore_noneX (dispatch := DG embL.host) hmd hc hpr
      obtain ⟨K, tr₁, r₁⟩ := hF (fun _ => pure .unit) [] [] rfl
      obtain ⟨q, segs', rr, hrr, r₂, hlive, hu⟩ :=
        ht.lrun (prof := first.prof) (hr := embL.hr) rfl K [] []
      exact ⟨_, instTraps_of_lrun hready (r₁.trans r₂) hlive hu.1 hrr⟩
    cases hv : Silmaril.Wasm.Validation.validate? m with
    | none =>
      refine trapNone _ hci ?_
      show Core3.prepareE? _ m _ = none
      unfold Core3.prepareE?
      rw [hv]
    | some mt =>
      rw [importTypesE_length hv] at hci
      have hsh := prepareE_mapH (fun _ : Nat => lowH) (irStore m.imports.length) m
        ((List.range m.imports.length).map Silmaril.Wasm.Execution.Core.ExternAddr.func)
      rw [mapH_irStore, ← hcore] at hsh
      rcases hIR with hnone | ⟨s', mi', a, c, hp, hrun, hst⟩
      · refine trapNone _ hci ?_
        exact hsh.trans (by rw [hnone]; rfl)
      · have hpr : (core3 neverFail).prepare? M₁.store.core m
            ((List.range m.imports.length).map Silmaril.Wasm.Execution.Core.ExternAddr.func) =
            some (Store.mapH (fun _ : Nat => lowH) s', mi', some a) := by
          exact hsh.trans (by rw [hp]; rfl)
        have hF₂ := instantiateCore_startX (prof := first.prof) (hr := embL.hr)
          (dispatch := DG embL.host) hmd hci hpr
        obtain ⟨K, tr₁, r₁⟩ := (FocusAt.trans hF rfl hF₂) (fun _ => pure .unit) [] [] rfl
        obtain ⟨ι', hadd⟩ : ∃ ι', ({} : InstState).addThread? ⟨0⟩ = some (1, ι') := ⟨_, rfl⟩
        obtain ⟨M₀, thc, Kc, segsc, restc, tr₂, r₂, hc₀, hcore₀, hl₀⟩ :=
          start_coreG (impl := embL.host) first.prof
            { ({ M₁ with
              store := setCoreSt (Store.mapH (fun _ : Nat => lowH) s')
                M₁.store } : Machine.Config (core3 neverFail) _) with
              ctl := [⟨none, .prog (Instantiate.runStart ⟨0⟩ a >>= K), []⟩] }
            _ {} ι' rfl rfl rfl hadd
        have hok : Silmaril.Wasm.Execution.Core.StoreOk
            (Store.mapH (fun _ : Nat => lowH)
              (irStore m.imports.length)) := by
          rw [mapH_irStore]
          exact storeOk_lowStore _ _
        obtain ⟨n, s'', t'', hrunC, hst''⟩ :=
          startTrap_low (fun _ : Nat => lowH) hok hp hrun hst
        obtain ⟨tr₃, mT, r₃, hlive, hu⟩ := lrun_coreTrap (prof := first.prof) (hr := embL.hr)
          (dispatch := DG embL.host) hrunC hst'' M₀ hc₀ hcore₀ hl₀
        exact ⟨_, instTraps_of_lrun hready (r₁.trans (r₂.trans r₃)) hlive hu.1
          (fun _ h => by cases h)⟩

/-! ## From the IR's first node -/

section Bridge

open Silmaril.Wasm.Component.Conformance

/-- **The reference half when node `0` fails, with lowered imports**: on an import-wired binary
of the fragment `FirstImpFrag` importing `f: func(u32)`, a quiet failure of the IR's first core
node makes the reference machine trap. -/
theorem firstImp_fail_ref {b : ByteArray} {c : Comp Binary.CoreMod} {r : RefComponent}
    {ps : List (Binary.CoreMod × List Impl)}
    (hc : Binary.parseComponent b = .ok c) (hr : decodeRef b = .ok r) (hw : HostWired r)
    (hf : FirstImpFrag r) (himp : c.imports = hostI) (hn : c.nodes = coreNodes ps)
    (h0 : 0 < ps.length)
    (hq : NodeQuiet hostI.length (.fail ()) (ps[0]'h0).1 (ps[0]'h0).2) :
    InstResult.traps ∈ instBehaviours first.prof (Host.ofEmbedder embL) hostConfigX r
      (importArgs hostI) := by
  obtain ⟨R, hR, hI, -, hN⟩ :=
    Silmaril.Proofs.Wasm.Component.DecoderBridge.relW_of_decode hc hr (inFrag_of_hostWired hw)
  unfold FirstImpFrag firstImpFrag at hf
  split at hf
  · cases hf
  · rename_i pre mi cargs post hs
    simp only [Bool.and_eq_true] at hf
    obtain ⟨hpre, hf⟩ := hf
    split at hf
    · rename_i m hm
      simp only [impOk, Bool.and_eq_true, decide_eq_true_eq] at hf
      obtain ⟨⟨⟨hlen, hlow⟩, hit⟩, hrt⟩ := hf
      obtain ⟨m', w, names, i, e, hm', hR0, hci, hwl, hwires⟩ :=
        refRead_firstW (firstCore?_eq r hs) hpre hR
      rw [hm] at hm'
      cases hm'
      obtain ⟨p, ps', rfl⟩ : ∃ p ps', ps = p :: ps' := by
        cases ps with
        | nil => cases h0
        | cons p ps' => exact ⟨p, ps', rfl⟩
      obtain ⟨rest, hrest⟩ : ∃ rest, R.nodes = (m, w) :: rest := by
        cases h : R.nodes with
        | nil => rw [h] at hR0; cases hR0
        | cons x rest => rw [h] at hR0; cases hR0; exact ⟨rest, rfl⟩
      rw [hn, hrest] at hN
      cases hN with
      | cons hW _ =>
        obtain ⟨cm, he, hd, hci'⟩ := hW
        cases he
        obtain ⟨ys, hEI, hys⟩ := hq
        have hmod : Binary.coreModule p.1 = m := by
          unfold Binary.coreModule
          rw [hd]
          rfl
        rw [hci] at hci'
        injection hci' with hci'
        simp only [Prod.mk.injEq] at hci'
        obtain ⟨rfl, hi, he'⟩ := hci'
        have hnames := coreIface_exports hci
        have hilen := coreIface_imports_length hci
        have himps : (CoreModule.imports p.1).all (·.2 == fFlat) = true := by
          unfold irTypesOk at hit
          rw [hci] at hit
          rw [← hi]
          exact hit
        have hwl' : (CoreModule.imports p.1).length ≤ p.2.length := by
          rw [hwl, coreIface_names_length hci, hi]
        have hw' : ∀ im ∈ p.2, im = lowF := by
          intro im him
          obtain ⟨k, ft, rfl, hk⟩ := hwires im him
          rw [← hI, himp] at hk
          rcases k with _ | k
          · simp [hostI] at hk
            rw [← hk]
          · simp [hostI] at hk
        change EngineInst (core3P (Silmaril.Wasm.SingleThreaded.profile neverFail))
          (Param.instOfI (core3P (Silmaril.Wasm.SingleThreaded.profile neverFail))
            (Binary.coreModule p.1) (CoreModule.imports p.1) (CoreModule.exports p.1))
          (CoreModule.imports p.1) ys _ at hEI
        rw [hmod] at hEI
        have hnames' : funcExportNames m = (CoreModule.exports p.1).map (·.1) := by
          rw [← hnames, he']
        have hIR := nodeFailImp_cases (o := neverFail) hnames' himps hwl'
          hw' hEI hys
        rw [← hi, hilen] at hIR
        exact ref_firstImp_trap hs hpre hm hlen hlow hrt hIR
    · cases hf

end Bridge

end Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp

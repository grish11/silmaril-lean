module

public import Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp.Path
public import Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp.Rest

/-!
# The first core instantiation with host calls

* `lowF_call`: an import call wired to the lowering `lowF` of `f: func(u32)` that is answered by
  one call of the component's imports is a call `f(u32 b)` for an `i32` argument `b`, and the
  answer `()` of `f` is answered to the core module with no results;
* `coreLog_eq`: so the host log of the IR's import calls (`coreLog`) is the log of the component
  calls (`InstRef.logOfCalls t`);
* `firstImp_setup`: the facts the fragment `FirstImpFrag` gives about the first node;
* `ref_firstImp_start`: when the IR's first node prepares and runs its start function with
  import calls to a returned status, the reference machine's instantiation reaches the core
  activation of the start function at that status, with the host log of the calls;
* `firstImp_failCalls_ref`, `firstImp_ready_ref`: the reference half for a first node that fails,
  or becomes ready, **after host calls** (`NodeCalls`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp

open Silmaril.Games Silmaril.Games.Inst
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
open Silmaril.Wasm.SingleThreaded (GrowOracle Internal status neverFail profile)

local notation "STh" => Silmaril.Wasm.SingleThreaded.Thread

/-! ## The wiring of a host call -/

theorem liftArgs_u32 {xs : List Flat} {ws : List Silmaril.Wasm.Component.Val}
    (h : liftArgs [.u32] xs = some ws) :
    ∃ b : BitVec 32, xs = [⟨.int .i32, b⟩] ∧ ws = [.u32 b] := by
  rcases xs with _ | ⟨⟨ty, b⟩, _ | ⟨y, ys⟩⟩
  · simp [liftArgs, ValTy.liftList, ValTy.lift] at h
  · rcases ty with (_ | _ | _) | (_ | _) <;>
      simp [liftArgs, ValTy.liftList, ValTy.lift] at h
    · exact ⟨b, rfl, h.symm⟩
  · rcases ty with (_ | _ | _) | (_ | _) <;>
      simp [liftArgs, ValTy.liftList, ValTy.lift] at h

/-- **A host call through the lowering of `f`**: an import call answered by one call `x` of the
component's imports, with the answer `()`, is the call `f(u32 b)` of an `i32` argument `b`,
answered with no results. -/
theorem lowF_call {w : List Impl} {n : Nat} (hw : ∀ im ∈ w, im = lowF) {q : (sigN n).Op}
    (hq : q.1.val < w.length) {x : Σ _ : sigU.Op, Option Payload}
    {k : sigU.Ar x.1 → Prog sigU (Option Payload)} {r : Option Payload}
    (hc : implsN 1 w n q = .call x.1 k) (hk : k x.2 = .pure r) (hx : x.2 = some (.vals [])) :
    ∃ b : BitVec 32, q.2 = .flat [⟨.int .i32, b⟩] ∧ x.1 = (0, .vals [.u32 b]) ∧
      r = some (.flat []) := by
  have hget : w[q.1.val]? = some lowF := by
    rw [List.getElem?_eq_getElem hq, hw _ (List.getElem_mem hq)]
  obtain ⟨⟨j, hj⟩, pl⟩ := q
  obtain ⟨xq, xa⟩ := x
  simp only at hget hc hk hx ⊢
  subst hx
  simp only [implsN, implsH, hget, Impl.prog, runChain] at hc
  cases pl with
  | vals vs => simp [Adapter.down] at hc
  | flat xs =>
    cases hl : liftArgs [.u32] xs with
    | none => simp [Adapter.down, hl] at hc
    | some ws =>
      obtain ⟨b, rfl, rfl⟩ := liftArgs_u32 hl
      simp only [Adapter.down, hl, Option.map_some, Target.prog, Nat.zero_lt_one, ↓reduceIte] at hc
      injection hc with h₁ h₂
      subst h₁
      subst h₂
      refine ⟨b, rfl, rfl, ?_⟩
      simp only [Games.Prog.bind] at hk
      injection hk with hk
      rw [← hk]
      rfl

/-- **The host log of the IR's import calls is the log of the component calls.** -/
theorem coreLog_eq {w : List Impl} {n : Nat} (hw : ∀ im ∈ w, im = lowF) (hn : n ≤ w.length) :
    ∀ {ys : List (Σ _ : (sigN n).Op, Option Payload)} {t : List (Σ _ : sigU.Op, Option Payload)},
      List.Forall₂ (fun y x => ∃ k, implsN 1 w n y.1 = .call x.1 k ∧ k x.2 = .pure y.2) ys t →
      (∀ x ∈ t, x.2 = InstTests.unitV) →
      coreLog ys = logOfCalls t ∧ ∀ y ∈ ys, y.2 = some (.flat [])
  | [], [], .nil, _ => ⟨rfl, fun _ h => by cases h⟩
  | y :: ys, x :: t, .cons ⟨k, hc, hk⟩ hrest, hu => by
    obtain ⟨b, hy, hx, hr⟩ := lowF_call hw (by have := y.1.1.isLt; omega) hc hk
      (hu x List.mem_cons_self)
    obtain ⟨h₁, h₂⟩ := coreLog_eq hw hn hrest (fun x' hx' => hu x' (List.mem_cons_of_mem _ hx'))
    refine ⟨?_, ?_⟩
    · have ex : x = ⟨(0, .vals [.u32 b]), some (.vals [])⟩ := by
        obtain ⟨x1, x2⟩ := x
        simp only at hx
        subst hx
        have := hu _ List.mem_cons_self
        simp only [InstTests.unitV] at this
        subst this
        rfl
      subst ex
      simp only [coreLog, logOfCalls, List.filterMap_cons, coreEvent, hy] at h₁ ⊢
      rw [h₁]
      rfl
    · intro y' hy'
      rcases List.mem_cons.mp hy' with rfl | hy'
      · exact hr
      · exact h₂ y' hy'

/-! ## The first node of the fragment -/

section Setup

open Silmaril.Wasm.Component.Conformance

/-- **What the fragment says about the first node**: the first core instantiation of `r` and
its module `m`, whose imports are the trampolines; the IR's first node decodes to `m`, with
imports of core type `fFlat`, one per import of `m`, each wired to `lowF`. -/
theorem firstImp_setup {b : ByteArray} {c : Comp Binary.CoreMod} {r : RefComponent}
    {p : Binary.CoreMod × List Impl} {ps : List (Binary.CoreMod × List Impl)}
    (hc : Binary.parseComponent b = .ok c) (hr : decodeRef b = .ok r) (hw : HostWired r)
    (hf : FirstImpFrag r) (himp : c.imports = hostI) (hn : c.nodes = coreNodes (p :: ps)) :
    ∃ (pre post : Core3Component) (mi : Nat) (cargs : List (String × Nat))
      (m : Silmaril.Wasm.Module),
      firstCore? r = some (pre, mi, cargs, post) ∧ preOk 0 0 pre = true ∧
      (coreMods pre)[mi]? = some m ∧ m.imports.length = preLowers pre ∧
      importsLowered cargs (preInsts pre) m = true ∧ refTypesOk m = true ∧
      Binary.coreModule p.1 = m ∧ (CoreModule.imports p.1).all (·.2 == fFlat) = true ∧
      (CoreModule.imports p.1).length = m.imports.length ∧
      (CoreModule.imports p.1).length ≤ p.2.length ∧ (∀ im ∈ p.2, im = lowF) ∧
      funcExportNames m = (CoreModule.exports p.1).map (·.1) := by
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
      obtain ⟨rest, hrest⟩ : ∃ rest, R.nodes = (m, w) :: rest := by
        cases h : R.nodes with
        | nil => rw [h] at hR0; cases hR0
        | cons x rest => rw [h] at hR0; cases hR0; exact ⟨rest, rfl⟩
      rw [hn, hrest] at hN
      cases hN with
      | cons hW _ =>
        obtain ⟨cm, he, hd, hci'⟩ := hW
        cases he
        have hmod : Binary.coreModule p.1 = m := by
          unfold Binary.coreModule
          rw [hd]
          rfl
        rw [hci] at hci'
        injection hci' with hci'
        simp only [Prod.mk.injEq] at hci'
        obtain ⟨rfl, hi, he'⟩ := hci'
        have hnames := coreIface_exports hci
        refine ⟨pre, post, mi, cargs, m, hs, hpre, hm, hlen, hlow, hrt, hmod, ?_, ?_, ?_, ?_, ?_⟩
        · unfold irTypesOk at hit
          rw [hci] at hit
          rw [← hi]
          exact hit
        · rw [← hi]
          exact coreIface_imports_length hci
        · rw [hwl, coreIface_names_length hci, hi]
        · intro im him
          obtain ⟨k, ft, rfl, hk⟩ := hwires im him
          rw [← hI, himp] at hk
          rcases k with _ | k
          · simp [hostI] at hk
            rw [← hk]
          · simp [hostI] at hk
        · rw [← hnames, he']
    · cases hf

end Setup

/-! ## The reference machine at the start function's return -/

section Ref

theorem coreCfg_self {E : CoreEngine} {σ : Type} {M : Machine.Config E σ} {th : Option ThreadId}
    {t : E.Thread (CanonHost E)} {K : List Flat → Canon.P E σ (Ret E)} {segs : List (Seg E σ)}
    {rest : List (Activation E σ)} (h : M.ctl = ⟨th, .core t K, segs⟩ :: rest) :
    coreCfg M th K segs rest (M.store.core, t) = M := by
  obtain ⟨S, h₀, conts, ctl, pending, results, cancels⟩ := M
  simp only at h
  subst h
  rfl

/-- The initial configuration of the reference machine's instantiation of `r`. -/
abbrev initCfg (r : Core3Component) : Machine.Config (core3 neverFail) (Unit × List HLinked2.HostEvent) :=
  { hostConfigX with ctl := [.ofProg none (StepDefs.runProg (instantiateProg r (importArgs hostI)))] }

/-- **The reference machine at the return of the first start function**: when the IR's first
node prepares against its imports, reports a start function and runs it, with import calls `ys`
answered with no results, to a returned status, the reference machine's instantiation reaches the
core activation of the start function at that status, with the host log `coreLog ys`. -/
theorem ref_firstImp_start {r : Core3Component} {pre post : Core3Component} {mi : Nat}
    {cargs : List (String × Nat)} {m : Silmaril.Wasm.Module}
    (hs : firstCore? r = some (pre, mi, cargs, post)) (hpre : preOk 0 0 pre = true)
    (hm : (coreMods pre)[mi]? = some m) (hn : m.imports.length = preLowers pre)
    (hlow : importsLowered cargs (preInsts pre) m = true) (hrt : refTypesOk m = true)
    {s' : Silmaril.Wasm.Execution.Core.Store Nat} {mi' : Silmaril.Wasm.Execution.Core.ModuleInst}
    {a : Nat}
    (hp : Core3.prepareE? (irStore m.imports.length) m
      ((List.range m.imports.length).map Silmaril.Wasm.Execution.Core.ExternAddr.func) =
        some (s', mi', some a))
    {imps : CoreIface} (himps : imps.all (·.2 == fFlat) = true)
    {ys : List (Σ _ : (sigN imps.length).Op, Option Payload)}
    {c' : (core3P (profile neverFail)).Config Nat}
    (hrun : Param.StartRunI (core3P (profile neverFail)) imps (s', Silmaril.Wasm.SingleThreaded.Thread.invoke a []) ys c')
    (hans : ∀ y ∈ ys, y.2 = some (.flat [])) {rr : Engine.CallResult}
    (hend : (core3P (profile neverFail)).status c'.1 c'.2 = .returned rr) :
    InstResult.traps ∈ instBehaviours first.prof (Host.ofEmbedder embL) hostConfigX r
      (importArgs hostI) ∨
    ∃ (tr : List (Label (core3 neverFail) (Unit × List HLinked2.HostEvent)))
      (M : Machine.Config (core3 neverFail) (Unit × List HLinked2.HostEvent))
      (thc : Option ThreadId) (K : List Flat → Canon.P (core3 neverFail) _ (Ret (core3 neverFail)))
      (segs : List (Seg (core3 neverFail) _)) (rest : List (Activation (core3 neverFail) _))
      (tR : STh),
      LRun first.prof embL.hr (DG embL.host) (initCfg r) tr M ∧
      M.ctl = ⟨thc, .core tR K, segs⟩ :: rest ∧
      (core3 neverFail).status M.store.core tR = .returned rr ∧ M.store.lockdown = false ∧
      M.host = ((), coreLog ys) := by
  have hready : HostReadyCfg hostConfigX := ⟨rfl, rfl, rfl⟩
  rcases root_firstX (prof := first.prof) (hr := embL.hr) (dispatch := DG embL.host)
      (fx := .host fWit ⟨0⟩) hs hpre argsOk_hostI importArgs_hostI_func rfl coreType_lowH rfl rfl
      rfl with ⟨tr, mT, ht⟩ | ⟨f, hF, hfm, -, hfi⟩
  · left
    obtain ⟨m', h⟩ := instTraps_of_trapsQS (prof := first.prof) (hr := embL.hr) hready ht
    exact ⟨m', h⟩
  · right
    have hmd : f.coreModule? mi = some m := by
      simp only [Frame.coreModule?, hfm]
      exact hm
    let M₁ : Machine.Config (core3 neverFail) _ := lowCfg hostConfigX (preLowers pre) lowH
    have hcore : M₁.store.core = lowStore m.imports.length lowH := by
      show lowStore (preLowers pre) lowH = _
      rw [hn]
    have hci := coreImportsFor_low (o := neverFail) (h := lowH) (md := m) hfi hlow hrt
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
          some (Store.mapH gL s', mi', some a) :=
        hsh.trans (by rw [hp]; rfl)
      have hF₂ := instantiateCore_startX (prof := first.prof) (hr := embL.hr)
        (dispatch := DG embL.host) hmd hci hpr
      obtain ⟨K, tr₁, r₁⟩ := (FocusAt.trans hF rfl hF₂) (fun _ => pure .unit) [] [] rfl
      obtain ⟨ι', hadd⟩ : ∃ ι', ({} : InstState).addThread? ⟨0⟩ = some (1, ι') := ⟨_, rfl⟩
      obtain ⟨M₀, thc, Kc, segsc, restc, tr₂, r₂, hc₀, hst₀, hth₀, hh₀⟩ :=
        start_coreX (impl := embL.host) first.prof
          { ({ M₁ with store := setCoreSt (Store.mapH gL s') M₁.store } :
              Machine.Config (core3 neverFail) _) with
            ctl := [⟨none, .prog (Instantiate.runStart ⟨0⟩ a >>= K), []⟩] }
          _ {} ι' rfl rfl rfl hadd
      have hml : ι'.mayLeave = true := by
        unfold InstState.addThread? at hadd
        obtain ⟨⟨i, tb⟩, -, he⟩ := Option.map_eq_some_iff.mp hadd
        cases he
        rfl
      have hB : CallInv M₀ thc := by
        subst hth₀
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hst₀]; rfl
        · rw [hst₀]; rfl
        · rw [hst₀]; exact ⟨ι', rfl, hml⟩
        · rw [hst₀]; rfl
      have hsOk : Silmaril.Wasm.Execution.Core.StoreOk (Store.mapH gL (irStore m.imports.length)) := by
        rw [mapH_irStore]
        exact storeOk_lowStore _ _
      have hp' := prepareE_mapH gL (irStore m.imports.length) m
        ((List.range m.imports.length).map Silmaril.Wasm.Execution.Core.ExternAddr.func)
      rw [hp] at hp'
      obtain ⟨hs', -, ⟨new, hnew, hwasm⟩, hcfg⟩ :=
        Silmaril.Wasm.Component.Engine.Core3.Typed.prepareE?_typed hsOk hp'
      have hRT : RT (Store.mapH gL s') (Silmaril.Wasm.SingleThreaded.Thread.invoke a []) := by
        refine ⟨hs', hcfg a rfl, fun fi hfi h hcode => ?_⟩
        rw [hnew, mapH_irStore] at hfi
        rcases List.mem_append.mp hfi with hfi | hfi
        · simp only [lowStore, List.mem_replicate] at hfi
          rw [hfi.2]
          rfl
        · obtain ⟨c, hc⟩ := hwasm fi hfi
          rw [hc] at hcode
          cases hcode
      have hM₀ : coreCfg M₀ thc Kc segsc restc
          (Store.mapH gL s', Silmaril.Wasm.SingleThreaded.Thread.invoke a []) = M₀ := by
        have e := coreCfg_self hc₀
        have hco : M₀.store.core = Store.mapH gL s' := by rw [hst₀]; rfl
        rw [hco] at e
        exact e
      obtain ⟨tr₃, B', tR', d₃, hstat, hB', hhost⟩ := startRun_ref (prof := first.prof)
        (K := Kc) (segs := segsc) (rest := restc) himps hrun hans hend hB
        (tR := Silmaril.Wasm.SingleThreaded.Thread.invoke a []) rfl hRT
      rw [hM₀] at d₃
      refine ⟨_, _, thc, Kc, segsc, restc, tR', r₁.trans (r₂.trans d₃), rfl, hstat, hB'.lock, ?_⟩
      show B'.host = ((), coreLog ys)
      rw [hhost, hh₀]
      rfl

end Ref

/-! ## The first node after host calls -/

section Bridge

open Silmaril.Wasm.Component.Conformance

theorem instOfI_cases {m : Silmaril.Wasm.Module} {imps exps : CoreIface}
    (himps : imps.all (·.2 == fFlat) = true)
    (hn : funcExportNames m = exps.map (·.1)) :
    (Param.instOfI (core3P (profile neverFail)) m imps exps = none →
      Core3.prepareE? (irStore imps.length) m
        ((List.range imps.length).map Silmaril.Wasm.Execution.Core.ExternAddr.func) = none) ∧
    (∀ J, Param.instOfI (core3P (profile neverFail)) m imps exps = some J →
      ∃ mi', Core3.prepareE? (irStore imps.length) m
        ((List.range imps.length).map Silmaril.Wasm.Execution.Core.ExternAddr.func) =
          some (J.store, mi', J.start)) := by
  have hA := allocHosts_ir (profile neverFail) imps 0 himps
  rw [irStore_zero, Nat.zero_add, range'_zero] at hA
  have hprep : (core3P (profile neverFail)).prepare?
      (irStore imps.length) m ((List.range imps.length).map
        (core3P (profile neverFail)).ofFunc) =
      Core3.prepareE? (irStore imps.length) m
        ((List.range imps.length).map Silmaril.Wasm.Execution.Core.ExternAddr.func) := rfl
  have e : Param.allocHosts (core3P (profile neverFail))
      ((core3P (profile neverFail)).empty Nat) 0 imps =
      (irStore imps.length, List.range imps.length) := hA
  refine ⟨fun hnone => ?_, fun J hJ => ?_⟩
  · unfold Param.instOfI at hnone
    rw [e] at hnone
    dsimp only at hnone
    rw [hprep] at hnone
    cases hp : Core3.prepareE? (irStore imps.length) m
        ((List.range imps.length).map Silmaril.Wasm.Execution.Core.ExternAddr.func) with
    | none => rfl
    | some p =>
      obtain ⟨s', mi, st⟩ := p
      rw [hp] at hnone
      obtain ⟨addrs, ha⟩ := exportAddrs_someX (profile neverFail) hp hn
      simp only [ha] at hnone
      cases hnone
  · unfold Param.instOfI at hJ
    rw [e] at hJ
    dsimp only at hJ
    rw [hprep] at hJ
    cases hp : Core3.prepareE? (irStore imps.length) m
        ((List.range imps.length).map Silmaril.Wasm.Execution.Core.ExternAddr.func) with
    | none => rw [hp] at hJ; cases hJ
    | some p =>
      obtain ⟨s', mi, st⟩ := p
      rw [hp] at hJ
      dsimp only at hJ
      obtain ⟨addrs, -, rfl⟩ := Option.map_eq_some_iff.mp hJ
      exact ⟨mi, rfl⟩

/-- A core activation at a trap traps the instantiation. -/
theorem traps_of_coreTrap {r : Core3Component}
    {tr : List (Label (core3 neverFail) (Unit × List HLinked2.HostEvent))}
    {M : Machine.Config (core3 neverFail) (Unit × List HLinked2.HostEvent)} {thc : Option ThreadId}
    {K : List Flat → Canon.P (core3 neverFail) _ (Ret (core3 neverFail))}
    {segs : List (Seg (core3 neverFail) _)} {rest : List (Activation (core3 neverFail) _)} {tR : STh}
    (d : LRun first.prof embL.hr (DG embL.host) (initCfg r) tr M)
    (hctl : M.ctl = ⟨thc, .core tR K, segs⟩ :: rest)
    (hst : (core3 neverFail).status M.store.core tR = .returned .trap)
    (hl : M.store.lockdown = false) :
    InstResult.traps ∈ instBehaviours first.prof (Host.ofEmbedder embL) hostConfigX r
      (importArgs hostI) := by
  have hready : HostReadyCfg hostConfigX := ⟨rfl, rfl, rfl⟩
  have hu : UniqueStep first.prof embL.hr (DG embL.host) M (.trap .coreTrap) (trapCfg M) := by
    refine UniqueStep.of_core hctl ?_ (.coreTrap hctl hst)
    rw [hst]
    exact ⟨nofun, nofun⟩
  exact ⟨_, instTraps_of_lrun hready d ⟨by rw [hctl]; exact List.cons_ne_nil _ _, hl⟩ hu.1
    (fun _ h => by cases h)⟩

/-- **The reference half when node `0` fails after host calls**: on an import-wired binary of
the fragment `FirstImpFrag` importing `f: func(u32)`, if the IR's first core node fails after
the host calls `t` (each answered `()`), the reference machine traps. -/
theorem firstImp_failCalls_ref {b : ByteArray} {c : Comp Binary.CoreMod} {r : RefComponent}
    {ps : List (Binary.CoreMod × List Impl)} {t : List (Σ _ : sigU.Op, Option Payload)}
    (hc : Binary.parseComponent b = .ok c) (hr : decodeRef b = .ok r) (hw : HostWired r)
    (hf : FirstImpFrag r) (himp : c.imports = hostI) (hn : c.nodes = coreNodes ps)
    (h0 : 0 < ps.length) (hu : ∀ x ∈ t, x.2 = InstTests.unitV)
    (hq : NodeCalls hostI.length (.fail ()) (ps[0]'h0).1 (ps[0]'h0).2 t) :
    InstResult.traps ∈ instBehaviours first.prof (Host.ofEmbedder embL) hostConfigX r
      (importArgs hostI) := by
  obtain ⟨p, ps', rfl⟩ : ∃ p ps', ps = p :: ps' := by
    cases ps with
    | nil => cases h0
    | cons p ps' => exact ⟨p, ps', rfl⟩
  obtain ⟨pre, post, mi, cargs, m, hs, hpre, hm, hlen, hlow, hrt, hmod, himps, hilen, hwl, hw',
    hnames⟩ := firstImp_setup hc hr hw hf himp hn
  obtain ⟨ys, hEI, hF⟩ := hq
  obtain ⟨-, hans⟩ := coreLog_eq hw' hwl hF hu
  change EngineInst (core3P (profile neverFail))
    (Param.instOfI (core3P (profile neverFail)) (Binary.coreModule p.1) (CoreModule.imports p.1)
      (CoreModule.exports p.1)) (CoreModule.imports p.1) ys _ at hEI
  rw [hmod] at hEI
  obtain ⟨hnone, hsome⟩ := instOfI_cases himps hnames
  rcases hEI with ⟨hI, -⟩ | ⟨J, f, c', hJ, hfs, hrun, hst⟩
  · have := hnone hI
    rw [hilen] at this
    exact ref_firstImp_trap hs hpre hm hlen hlow hrt (.inl this)
  · obtain ⟨mi', hp⟩ := hsome J hJ
    rw [hfs, hilen] at hp
    have hrun' : Param.StartRunI (core3P (profile neverFail)) (CoreModule.imports p.1)
        (J.store, Silmaril.Wasm.SingleThreaded.Thread.invoke f []) ys c' := hrun
    rcases ref_firstImp_start hs hpre hm hlen hlow hrt hp himps hrun' hans hst with
      h | ⟨tr, M, thc, K, segs, rest, tR, d, hctl, hst', hl, -⟩
    · exact h
    · exact traps_of_coreTrap d hctl hst' hl

/-- **The reference half when node `0` is ready after host calls**: on an import-wired binary of
the fragment `FirstImpFrag` importing `f: func(u32)`, if the IR's first core node becomes ready
after the host calls `t` (each answered `()`), then the reference machine traps before the first
core instantiation (a definition before it fails its import check), or the module has no start
function and `t = []`, or the machine reaches the core activation of the start function at the
returned values, with the host log `logOfCalls t` (the same calls, in the same order). -/
theorem firstImp_ready_ref {b : ByteArray} {c : Comp Binary.CoreMod} {r : RefComponent}
    {ps : List (Binary.CoreMod × List Impl)} {t : List (Σ _ : sigU.Op, Option Payload)}
    (hc : Binary.parseComponent b = .ok c) (hr : decodeRef b = .ok r) (hw : HostWired r)
    (hf : FirstImpFrag r) (himp : c.imports = hostI) (hn : c.nodes = coreNodes ps)
    (h0 : 0 < ps.length) (hu : ∀ x ∈ t, x.2 = InstTests.unitV)
    (hq : NodeCalls hostI.length .ready (ps[0]'h0).1 (ps[0]'h0).2 t) :
    InstResult.traps ∈ instBehaviours first.prof (Host.ofEmbedder embL) hostConfigX r
        (importArgs hostI) ∨ t = [] ∨
    ∃ (tr : List (Label (core3 neverFail) (Unit × List HLinked2.HostEvent)))
      (M : Machine.Config (core3 neverFail) (Unit × List HLinked2.HostEvent))
      (thc : Option ThreadId) (K : List Flat → Canon.P (core3 neverFail) _ (Ret (core3 neverFail)))
      (segs : List (Seg (core3 neverFail) _)) (rest : List (Activation (core3 neverFail) _))
      (tR : STh) (fvs : List Flat),
      LRun first.prof embL.hr (DG embL.host) (initCfg r) tr M ∧
      M.ctl = ⟨thc, .core tR K, segs⟩ :: rest ∧
      (core3 neverFail).status M.store.core tR = .returned (.values fvs) ∧
      M.store.lockdown = false ∧ M.host = ((), logOfCalls t) := by
  obtain ⟨p, ps', rfl⟩ : ∃ p ps', ps = p :: ps' := by
    cases ps with
    | nil => cases h0
    | cons p ps' => exact ⟨p, ps', rfl⟩
  obtain ⟨pre, post, mi, cargs, m, hs, hpre, hm, hlen, hlow, hrt, hmod, himps, hilen, hwl, hw',
    hnames⟩ := firstImp_setup hc hr hw hf himp hn
  obtain ⟨ys, hEI, hF⟩ := hq
  obtain ⟨hlog, hans⟩ := coreLog_eq hw' hwl hF hu
  change EngineInst (core3P (profile neverFail))
    (Param.instOfI (core3P (profile neverFail)) (Binary.coreModule p.1) (CoreModule.imports p.1)
      (CoreModule.exports p.1)) (CoreModule.imports p.1) ys _ at hEI
  rw [hmod] at hEI
  obtain ⟨-, hsome⟩ := instOfI_cases himps hnames
  obtain ⟨J, hJ, ⟨-, rfl⟩ | ⟨f, c', fvs, hfs, hrun, hst⟩⟩ := hEI
  · right; left
    cases hF
    rfl
  · obtain ⟨mi', hp⟩ := hsome J hJ
    rw [hfs, hilen] at hp
    have hrun' : Param.StartRunI (core3P (profile neverFail)) (CoreModule.imports p.1)
        (J.store, Silmaril.Wasm.SingleThreaded.Thread.invoke f []) ys c' := hrun
    rcases ref_firstImp_start hs hpre hm hlen hlow hrt hp himps hrun' hans hst with
      h | ⟨tr, M, thc, K, segs, rest, tR, d, hctl, hst', hl, hh⟩
    · exact .inl h
    · refine .inr (.inr ⟨tr, M, thc, K, segs, rest, tR, fvs, d, hctl, hst', hl, ?_⟩)
      rw [hh, hlog]

/-- `firstImp_ready_ref`, with the run as a run of the machine's steps (`Machine.Steps`). -/
theorem firstImp_ready_steps {b : ByteArray} {c : Comp Binary.CoreMod} {r : RefComponent}
    {ps : List (Binary.CoreMod × List Impl)} {t : List (Σ _ : sigU.Op, Option Payload)}
    (hc : Binary.parseComponent b = .ok c) (hr : decodeRef b = .ok r) (hw : HostWired r)
    (hf : FirstImpFrag r) (himp : c.imports = hostI) (hn : c.nodes = coreNodes ps)
    (h0 : 0 < ps.length) (hu : ∀ x ∈ t, x.2 = InstTests.unitV)
    (hq : NodeCalls hostI.length .ready (ps[0]'h0).1 (ps[0]'h0).2 t) :
    InstResult.traps ∈ instBehaviours first.prof (Host.ofEmbedder embL) hostConfigX r
        (importArgs hostI) ∨ t = [] ∨
    ∃ (tr : List (Label (core3 neverFail) (Unit × List HLinked2.HostEvent)))
      (M : Machine.Config (core3 neverFail) (Unit × List HLinked2.HostEvent))
      (thc : Option ThreadId) (K : List Flat → Canon.P (core3 neverFail) _ (Ret (core3 neverFail)))
      (segs : List (Seg (core3 neverFail) _)) (rest : List (Activation (core3 neverFail) _))
      (tR : STh) (fvs : List Flat),
      Steps first.prof embL.hr (Host.ofEmbedder embL).dispatch
        { hostConfigX with ctl := [.ofProg none (StepDefs.runProg (instantiateProg r (importArgs hostI)))] }
        tr M ∧
      M.ctl = ⟨thc, .core tR K, segs⟩ :: rest ∧
      (core3 neverFail).status M.store.core tR = .returned (.values fvs) ∧
      M.host = ((), logOfCalls t) := by
  rcases firstImp_ready_ref hc hr hw hf himp hn h0 hu hq with h | h |
    ⟨tr, M, thc, K, segs, rest, tR, fvs, d, hctl, hst, -, hh⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨tr, M, thc, K, segs, rest, tR, fvs, d.steps, hctl, hst, hh⟩)

end Bridge

end Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp

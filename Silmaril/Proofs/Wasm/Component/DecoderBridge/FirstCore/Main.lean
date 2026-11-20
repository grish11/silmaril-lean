module

public import Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore.IR
public import Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore.Read
public import Silmaril.Wasm.Component.InstTestsRef.Defs

/-!
# The reference half when the first core instantiation fails

* `ref_first_trap`: the reference machine (logging host, `hostConfigX`) traps on a component of
  the first-core fragment whose first instantiated module, prepared alone in the empty store,
  fails, or reports a start function whose run traps;
* `firstCore_fail_ref`: so it traps on every import-wired binary of the fragment whose IR node
  `0` fails quietly (`NodeQuiet`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.DecoderBridge
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Instantiate
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Component.InstRef Silmaril.Wasm.Component.InstLitmus
  Silmaril.Wasm.Component.InstTestsRef
open Silmaril.Wasm.Component.Reference.Core3Adder (first)
open Silmaril.Wasm.SingleThreaded (GrowOracle Internal status neverFail)

/-! ## Composition of runs to a hole -/

section Compose

variable {E : CoreEngine} {σ : Type} {prof : ProfileKind} {hr : HostReady σ}
  {dispatch : Call E → Canon.P E σ (Ret E)}

theorem FocusAt.trans {th : Option ThreadId} {β γ α : Type} {X : Canon.P E σ β}
    {Y : Canon.P E σ γ} {p : Canon.P E σ α} {m m₁ m₂ : Machine.Config E σ}
    (h₁ : FocusAt prof hr dispatch th X p m m₁) (hl₁ : m₁.store.lockdown = false)
    (h₂ : FocusAt prof hr dispatch th Y X m₁ m₂) : FocusAt prof hr dispatch th Y p m m₂ := by
  intro f segs rest hl
  obtain ⟨K, tr, r⟩ := h₁ f segs rest hl
  obtain ⟨K', tr', r'⟩ := h₂ K segs rest hl₁
  exact ⟨K', tr ++ tr', r.trans r'⟩

end Compose

/-! ## Core stores of host functions are typed -/

theorem hostAllocs_storeOk {o : GrowOracle} {c c' : (core3 o).Store (CanonHost (core3 o))}
    (h : HostAllocs (core3 o) c c') (hc : Silmaril.Wasm.Execution.Core.StoreOk c) :
    Silmaril.Wasm.Execution.Core.StoreOk c' := by
  induction h with
  | refl => exact hc
  | step ty hh _ ih =>
    exact (Silmaril.Wasm.Component.Engine.Core3.Typed.allocHost_storeOk ih rfl).1

/-! ## The reference machine of the decoded binaries -/

section Ref

open Silmaril.Wasm.Execution.Core (Store)

/-- A placeholder host code (the instance alone has no host functions). -/
def phHost : CanonHost (core3 neverFail) := .embedder "" ⟨[], []⟩

theorem argsOk_hostI : ArgsOk (E := core3 neverFail) (importArgs hostI) hostConfigX := by
  intro n v h
  simp only [importArgs, hostI, List.mapIdx_cons, List.mapIdx_nil, List.lookup_cons,
    List.lookup_nil] at h
  split at h
  · cases h
    exact ⟨⟨0⟩, _, rfl, rfl⟩
  · cases h

theorem importTypes_nil {m : Silmaril.Wasm.Module} (himp : m.imports = []) :
    (core3 neverFail).importTypes m = [] := by
  show Silmaril.Wasm.Component.Engine.Core3.importTypesE m = []
  unfold Silmaril.Wasm.Component.Engine.Core3.importTypesE
  split <;> simp [himp]

/-- **The reference half for the first core instantiation**: when the module of the first core
instantiation, prepared alone in the empty store, fails, or reports a start function whose run
traps, the reference machine's instantiation traps. -/
theorem ref_first_trap {r : Core3Component} {pre post : Core3Component} {mi : Nat}
    {cargs : List (String × Nat)} {m : Silmaril.Wasm.Module}
    (hs : firstCore? r = some (pre, mi, cargs, post)) (hpre : preOk 0 0 pre = true)
    (hm : (coreMods pre)[mi]? = some m) (himp : m.imports = [])
    (hsplit : splitMod m = true)
    (hIR : Silmaril.Wasm.Component.Engine.Core3.prepareE? ({} : Store Nat) m [] = none ∨
      ∃ s' mi' a c, Silmaril.Wasm.Component.Engine.Core3.prepareE? ({} : Store Nat) m [] =
          some (s', mi', some a) ∧
        Relation.ReflTransGen (Internal neverFail)
          (s', Silmaril.Wasm.SingleThreaded.Thread.invoke a []) c ∧
        status neverFail c.1 c.2 = .returned .trap) :
    InstResult.traps ∈ instBehaviours first.prof (Host.ofEmbedder embL) hostConfigX r
      (importArgs hostI) := by
  have hready : HostReadyCfg hostConfigX := ⟨rfl, rfl, rfl⟩
  have hseg : m.data = [] ∧ m.elems = [] := by
    simp only [splitMod, Bool.and_eq_true, List.isEmpty_iff] at hsplit
    exact ⟨hsplit.1.2, hsplit.2⟩
  rcases root_first (prof := first.prof) (hr := embL.hr) (dispatch := DG embL.host) hs hpre
      argsOk_hostI rfl rfl with ⟨tr, mT, ht⟩ | ⟨f, c', hF, hc', hfm⟩
  · obtain ⟨m', h⟩ := instTraps_of_trapsQS (prof := first.prof) (hr := embL.hr) hready ht
    exact ⟨m', h⟩
  · have hmd : f.coreModule? mi = some m := by
      simp only [Frame.coreModule?, hfm]
      exact hm
    have hsh := prepareE_shift (fun _ => phHost) c' hseg
    rcases hIR with hn | ⟨s', mi', a, c, hp, hrun, hst⟩
    · have hpr : (core3 neverFail).prepare?
          ({ hostConfigX with store := firstStore hostConfigX.store c' } :
            Machine.Config (core3 neverFail) _).store.core m [] = none := by
        show Silmaril.Wasm.Component.Engine.Core3.prepareE? c' m [] = none
        rw [hsh, hn]
        rfl
      obtain ⟨tr, mT, ht⟩ := instantiateCore_none (dispatch := DG embL.host) (cargs := cargs) hmd
        (importTypes_nil himp) hpr
      obtain ⟨K, tr₁, r₁⟩ := hF (fun _ => pure .unit) [] [] rfl
      obtain ⟨q, segs', rr, hrr, r₂, hlive, hu⟩ :=
        ht.lrun (prof := first.prof) (hr := embL.hr) rfl K [] []
      exact ⟨_, instTraps_of_lrun hready (r₁.trans r₂) hlive hu.1 hrr⟩
    · have hpr : (core3 neverFail).prepare?
          ({ hostConfigX with store := firstStore hostConfigX.store c' } :
            Machine.Config (core3 neverFail) _).store.core m [] =
            some (reloc c' (Store.mapH (fun _ => phHost) s'),
              (sh c').minst mi', some (c'.funcs.length + a)) := by
        show Silmaril.Wasm.Component.Engine.Core3.prepareE? c' m [] = _
        rw [hsh, hp]
        rfl
      have hF₂ := instantiateCore_start (prof := first.prof) (hr := embL.hr)
        (dispatch := DG embL.host) (cargs := cargs) hmd (importTypes_nil himp) hpr
      obtain ⟨K, tr₁, r₁⟩ := (FocusAt.trans hF rfl hF₂) (fun _ => pure .unit) [] [] rfl
      obtain ⟨ι', hadd⟩ : ∃ ι', ({} : InstState).addThread? ⟨0⟩ = some (1, ι') := ⟨_, rfl⟩
      obtain ⟨M₀, thc, Kc, segsc, restc, tr₂, r₂, hc₀, hcore₀, hl₀⟩ :=
        start_coreG (impl := embL.host) first.prof
          { ({ ({ hostConfigX with store := firstStore hostConfigX.store c' } :
              Machine.Config (core3 neverFail) _) with
            store := setCoreSt (reloc c' (Store.mapH (fun _ => phHost) s'))
              (firstStore hostConfigX.store c') } : Machine.Config (core3 neverFail) _) with
            ctl := [⟨none, .prog (Instantiate.runStart ⟨0⟩ (c'.funcs.length + a) >>= K), []⟩] }
          _ {} ι' rfl rfl rfl hadd
      have hok : Silmaril.Wasm.Execution.Core.StoreOk c' :=
        hostAllocs_storeOk hc' (Silmaril.Wasm.Component.Engine.Core3.Typed.empty_ok _).1
      obtain ⟨n, s'', t'', hrunC, hst''⟩ :=
        startTrap_shift (fun _ => phHost) c' hok himp hsplit hp hrun hst
      obtain ⟨tr₃, mT, r₃, hlive, hu⟩ := lrun_coreTrap (prof := first.prof) (hr := embL.hr)
        (dispatch := DG embL.host) hrunC hst'' M₀ hc₀ hcore₀ hl₀
      exact ⟨_, instTraps_of_lrun hready (r₁.trans (r₂.trans r₃)) hlive hu.1
        (fun _ h => by cases h)⟩

end Ref

/-! ## From the IR's first node -/

section Bridge

open Silmaril.Wasm.Component.Conformance

theorem inFrag_of_hostWired {r : RefComponent} (hw : HostWired r) : InFrag r := by
  unfold HostWired hostWired at hw
  unfold InFrag inFrag
  cases h : refRead r with
  | none => rw [h] at hw; cases hw
  | some R => rfl

/-- **The reference half when node `0` fails**: on an import-wired binary of the first-core
fragment, a quiet failure of the IR's first core node makes the reference machine trap. -/
theorem firstCore_fail_ref {b : ByteArray} {c : Comp Binary.CoreMod} {r : RefComponent}
    {ps : List (Binary.CoreMod × List Impl)}
    (hc : Binary.parseComponent b = .ok c) (hr : decodeRef b = .ok r) (hw : HostWired r)
    (hf : FirstCoreFrag r) (hn : c.nodes = coreNodes ps) (h0 : 0 < ps.length)
    (hq : NodeQuiet hostI.length (.fail ()) (ps[0]'h0).1 (ps[0]'h0).2) :
    InstResult.traps ∈ instBehaviours first.prof (Host.ofEmbedder embL) hostConfigX r
      (importArgs hostI) := by
  obtain ⟨R, hR, -, -, hN⟩ :=
    Silmaril.Proofs.Wasm.Component.DecoderBridge.relW_of_decode hc hr (inFrag_of_hostWired hw)
  unfold FirstCoreFrag firstCoreFrag at hf
  split at hf
  · cases hf
  · rename_i pre mi cargs post hs
    simp only [Bool.and_eq_true] at hf
    obtain ⟨hpre, hf⟩ := hf
    split at hf
    · rename_i m hm
      simp only [Bool.and_eq_true, List.isEmpty_iff] at hf
      obtain ⟨himp, hsplit⟩ := hf
      obtain ⟨m', w, hm', hR0⟩ := refRead_first (firstCore?_eq r hs) hpre hR
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
        obtain ⟨cm, he, hd, hci⟩ := hW
        cases he
        obtain ⟨ys, hEI, -⟩ := hq
        have hmod : Binary.coreModule p.1 = m := by
          unfold Binary.coreModule
          rw [hd]
          rfl
        have himps := coreIface_imports hci himp
        have hnames := coreIface_exports hci
        have key : ∀ (imps : CoreIface) (ys : List (Σ _ : (sigN imps.length).Op, Option Payload)),
            imps = [] → EngineInst (core3P (Silmaril.Wasm.SingleThreaded.profile neverFail))
              (Param.instOfI (core3P (Silmaril.Wasm.SingleThreaded.profile neverFail)) m imps
                (CoreModule.exports p.1)) imps ys (.fail ()) →
            Silmaril.Wasm.Component.Engine.Core3.prepareE?
                ({} : Silmaril.Wasm.Execution.Core.Store Nat) m [] = none ∨
              ∃ s' mi' a c, Silmaril.Wasm.Component.Engine.Core3.prepareE?
                  ({} : Silmaril.Wasm.Execution.Core.Store Nat) m [] = some (s', mi', some a) ∧
                Relation.ReflTransGen (Internal neverFail)
                  (s', Silmaril.Wasm.SingleThreaded.Thread.invoke a []) c ∧
                status neverFail c.1 c.2 = .returned .trap := by
          intro imps ys h hE
          subst h
          exact nodeFail_cases hnames.symm hE
        change EngineInst (core3P (Silmaril.Wasm.SingleThreaded.profile neverFail))
          (Param.instOfI (core3P (Silmaril.Wasm.SingleThreaded.profile neverFail))
            (Binary.coreModule p.1) (CoreModule.imports p.1) (CoreModule.exports p.1))
          (CoreModule.imports p.1) ys _ at hEI
        rw [hmod] at hEI
        exact ref_first_trap hs hpre hm himp hsplit (key _ ys himps hEI)
    · cases hf

end Bridge

end Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore

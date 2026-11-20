module

public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.Inst

/-!
# The instantiation on `MultiImpFrag` is unique

`NodesRefL` (`Multi.Nodes`) gives the reference instantiation of a binary of the fragment as a
live run of unique steps (`LRun`) from the instantiation host event to a configuration with the
host in control. So it is the only finishing run:

* `instantiates_eq_of_lrun`: any `Instantiates` from `hostConfigX` whose instantiation program
  runs by such a live run ends at its end, with the observation of that run;
* `instantiates_unique`: on the fragment, with the IR's node calls `ts`, **every** reference
  instantiation ends at the configuration of `nodesRefL`, with its instance and exports, and its
  host log `logOfCalls ts.flatten`.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi

open Silmaril.Games Silmaril.Games.Inst
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore
open Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.DecoderBridge
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Instantiate
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Component.InstRef Silmaril.Wasm.Component.InstLitmus
  Silmaril.Wasm.Component.InstTestsRef
open Silmaril.Wasm.Component.Conformance
open Silmaril.Wasm.Component.Reference.Core3Adder (first)
open Silmaril.Wasm.SingleThreaded (neverFail)

local notation "Σh" => Unit × List HLinked2.HostEvent

/-- From a configuration with the host in control, a run without host events is empty. -/
theorem steps_nil_of_ctl_nil {M M' : Machine.Config (core3 neverFail) Σh}
    {tr : List (Label (core3 neverFail) Σh)} (hc : M.ctl = [])
    (h : Steps first.prof embL.hr (DG embL.host) M tr M') (hn : ∀ ev, Label.host ev ∉ tr) :
    tr = [] ∧ M' = M := by
  cases h with
  | refl => exact ⟨rfl, rfl⟩
  | cons s _ =>
    obtain ⟨ev, rfl⟩ := Step.host_of_ctl_nil hc s
    exact absurd List.mem_cons_self (hn ev)

/-- **A finishing live run of the instantiation program is the only finishing run.** -/
theorem instantiates_eq_of_lrun {r : RefComponent} {tr : List (Label (core3 neverFail) Σh)}
    {M' : Machine.Config (core3 neverFail) Σh}
    (d : LRun first.prof embL.hr (DG embL.host) (instCfg r) tr M') (hc : M'.ctl = [])
    {M₂ : Machine.Config (core3 neverFail) Σh} {inst : InstId} {es : List (String × FuncId)}
    (h : Instantiates first.prof embL.hr (Host.ofEmbedder embL).dispatch hostConfigX r
      (importArgs hostI) M₂ inst es) :
    M₂ = M' ∧ (traceObs tr).findSome? decodeInstantiated? = some (inst, es) := by
  obtain ⟨tr', hs, hn, hc₂, -, hobs⟩ := h
  cases hs with
  | cons s₀ hs =>
    cases s₀
    rcases d.inv hs with hlv | ⟨tr'', htr, hs'⟩
    · exact absurd hc₂ hlv.1
    · subst htr
      obtain ⟨rfl, rfl⟩ := steps_nil_of_ctl_nil hc hs'
        (fun ev hev => hn ev (List.mem_append_right _ hev))
      rw [List.append_nil] at hobs
      exact ⟨rfl, hobs⟩

/-- **The instantiation on the fragment is unique**: with the IR's node calls `ts`, there is a
configuration `M'`, instance and exports such that every reference instantiation ends there, with
them, and the host log is `logOfCalls ts.flatten`. -/
theorem instantiates_unique {b : ByteArray} {c : Comp Binary.CoreMod} {r : RefComponent}
    {ps : List (Binary.CoreMod × List Impl)} {ts : List (List (Σ _ : sigU.Op, Option Payload))}
    (hpc : Binary.parseComponent b = .ok c) (hr : decodeRef b = .ok r) (hf : MultiImpFrag r)
    (himp : c.imports = hostI) (hnodes : c.nodes = coreNodes ps)
    (hu : ∀ x ∈ ts.flatten, x.2 = InstTests.unitV)
    (hNC : List.Forall₂ (fun q tj => NodeCalls hostI.length .ready q.1 q.2 tj) ps ts) :
    ∃ M' inst es,
      Instantiates first.prof embL.hr (Host.ofEmbedder embL).dispatch hostConfigX r
        (importArgs hostI) M' inst es ∧
      M'.host = ((), logOfCalls ts.flatten) ∧
      ∀ M₂ inst₂ es₂, Instantiates first.prof embL.hr (Host.ofEmbedder embL).dispatch hostConfigX
          r (importArgs hostI) M₂ inst₂ es₂ → M₂ = M' ∧ inst₂ = inst ∧ es₂ = es := by
  obtain ⟨tr, M', inst, es, d, hn, hctl, hlock, hobs, hhost⟩ :=
    nodesRefL b c r ps ts hpc hr hf himp hnodes hu hNC
  have hready : HostReadyCfg hostConfigX := ⟨rfl, rfl, rfl⟩
  refine ⟨M', inst, es, ⟨tr, .cons (.hostRun hready) d.steps, hn, hctl, hlock, hobs⟩, hhost, ?_⟩
  intro M₂ inst₂ es₂ h
  obtain ⟨rfl, h'⟩ := instantiates_eq_of_lrun d hctl h
  rw [hobs] at h'
  cases h'
  exact ⟨rfl, rfl, rfl⟩

end Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi

module

public import Silmaril.Wasm.Component.DecoderBridge.Sim.Defs
public import Silmaril.Wasm.Component.DecoderBridge.Wire.Thms
public import Silmaril.Wasm.Component.InstWired.Thms

/-!
# The behavioural bridge on import-wired binaries: the IR half

`failAdequacyWired_of`: the IR instantiation of an import-wired binary that fails before any
host call fails at a node `k` whose engine run fails quietly, the nodes before it ready
quietly (`InstWired.nodesInst_of_denI`, `NodesInst.fail_nil`, `coreNodeI_engine_nil`), so the
reference half `Task.failRefWired` gives the trap.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Conformance Silmaril.Wasm.Component.DecoderBridge
open Silmaril.Wasm.Component.InstLitmus
open Silmaril.Wasm.SingleThreaded (profile neverFail)

theorem scoped_of_scopedB {e : Nat} {im : Impl} (h : scopedB e im = true) : im.Scoped e := by
  unfold scopedB at h
  unfold Impl.Scoped
  split at h <;> simp_all

theorem hostWired_inv {r : RefComponent} (h : HostWired r) :
    ∃ R, refRead r = some R ∧ rstWired R = true := by
  unfold HostWired hostWired at h
  cases hR : refRead r with
  | none => rw [hR] at h; cases h
  | some R => rw [hR] at h; exact ⟨R, rfl, by simpa using h⟩

theorem inFrag_of_hostWired {r : RefComponent} (h : HostWired r) : InFrag r := by
  obtain ⟨R, hR, -⟩ := hostWired_inv h
  simp [InFrag, inFrag, hR]

theorem coreNodes_of_nodeW : ∀ {ns : List (Node Binary.CoreMod)}
    {Rn : List (Silmaril.Wasm.Module × List Impl)}, List.Forall₂ NodeW ns Rn →
    ∃ ps : List (Binary.CoreMod × List Impl), ns = coreNodes ps ∧
      ps.map Prod.snd = Rn.map Prod.snd
  | [], [], .nil => ⟨[], rfl, rfl⟩
  | _, _, .cons (a := n) (b := p) ⟨cm, hn, _, _⟩ h => by
    obtain ⟨ps, rfl, he⟩ := coreNodes_of_nodeW h
    exact ⟨(cm, p.2) :: ps, by rw [hn]; rfl, by simp [he]⟩

/-- The IR reading of an import-wired binary: core nodes wired to the imports. -/
theorem wired_of_decode {b : ByteArray} {c : Comp Binary.CoreMod} {r : RefComponent}
    (hc : Binary.parseComponent b = .ok c) (hr : decodeRef b = .ok r) (hw : HostWired r) :
    ∃ ps : List (Binary.CoreMod × List Impl), c.nodes = coreNodes ps ∧
      ImportWired c.imports.length ps := by
  obtain ⟨R, hR, hwR⟩ := hostWired_inv hw
  obtain ⟨R', hR', hIR, -, hN⟩ := relW_of_decode hc hr (inFrag_of_hostWired hw)
  rw [hR] at hR'
  cases hR'
  obtain ⟨ps, hps, hsnd⟩ := coreNodes_of_nodeW hN
  refine ⟨ps, hps, fun p hp' im him => ?_⟩
  have hmem : p.2 ∈ R.nodes.map Prod.snd := hsnd ▸ List.mem_map_of_mem hp'
  obtain ⟨q, hq, hqe⟩ := List.mem_map.1 hmem
  have := (List.all_eq_true.1 hwR) q hq
  rw [hqe] at this
  rw [hIR]
  exact scoped_of_scopedB ((List.all_eq_true.1 this) im him)

/-- **The instantiation part of a start play of an import-wired binary, node by node.** -/
theorem nodesInst_of_startPlay {b : ByteArray} {c : Comp Binary.CoreMod} {r : RefComponent}
    (hc : Binary.parseComponent b = .ok c) (hr : decodeRef b = .ok r) (hw : HostWired r)
    {t : List (Σ _ : sigU.Op, Option Payload)} {rest : List (Move sigU sigUI)}
    (hp : instPlay (F := sigU) t .ready ++ rest ∈ c.denI (Binary.coreModSemI (profile neverFail))) :
    ∃ ps : List (Binary.CoreMod × List Impl), c.nodes = coreNodes ps ∧
      NodesInst (Binary.coreModSemI (profile neverFail)) c.imports.length ps t .ready := by
  obtain ⟨ps, hps, hiw⟩ := wired_of_decode hc hr hw
  refine ⟨ps, hps, ?_⟩
  obtain ⟨I, ns, xs⟩ := c
  have hps' : ns = coreNodes ps := hps
  subst hps'
  exact nodesInst_of_denI hiw (Strategy.of_prefix _ hp (List.prefix_append _ _))

/-- **The IR half of the failure goal on import-wired binaries.** -/
theorem failAdequacyWired_of (h : Task.failRefWired) : Task.failAdequacyWired := by
  intro b c r hc hr hv hw hI hp
  obtain ⟨R, hR, hwR⟩ := hostWired_inv hw
  obtain ⟨R', hR', hIR, -, hN⟩ := relW_of_decode hc hr (inFrag_of_hostWired hw)
  rw [hR] at hR'
  cases hR'
  obtain ⟨ps, hps, hsnd⟩ := coreNodes_of_nodeW hN
  have hiw : ImportWired c.imports.length ps := by
    intro p hp' im him
    have hmem : p.2 ∈ R.nodes.map Prod.snd := hsnd ▸ List.mem_map_of_mem hp'
    obtain ⟨q, hq, hqe⟩ := List.mem_map.1 hmem
    have := (List.all_eq_true.1 hwR) q hq
    rw [hqe] at this
    rw [hIR]
    exact scoped_of_scopedB ((List.all_eq_true.1 this) im him)
  obtain ⟨I, ns, xs⟩ := c
  have hps' : ns = coreNodes ps := hps
  have hI' : I = hostI := hI
  have hiw' : ImportWired I.length ps := hiw
  subst hps' hI'
  have hNI := nodesInst_of_denI hiw' hp
  obtain ⟨k, hk, hbefore, hat⟩ := hNI.fail_nil
  refine h b _ r ps k hk hc hr hv hw rfl rfl (fun j hj => ?_) ?_
  · exact coreNodeI_engine_nil (hbefore j hj)
  · exact coreNodeI_engine_nil hat

end Silmaril.Proofs.Wasm.Component.DecoderBridge

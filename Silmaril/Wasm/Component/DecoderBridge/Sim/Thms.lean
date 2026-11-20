module

public import Silmaril.Wasm.Component.DecoderBridge.Sim.Defs
public import Silmaril.Wasm.Component.DecoderBridge.Sem.Thms
import Silmaril.Proofs.Wasm.Component.DecoderBridge.Sim

/-!
# The behavioural bridge on import-wired binaries: theorems

Proofs in `Silmaril.Proofs.Wasm.Component.DecoderBridge.Sim`.

* `failAdequacyWired_of` (proved): **the reference half `Task.failRefWired` implies the
  failure goal `Task.failAdequacyWired`** on every import-wired binary. The IR half is proved
  in general: an IR instantiation of an import-wired binary that fails before any host call
  fails at one core node `k`, the nodes before it ready, and each of these is a core engine run
  of its decoded module with no host call (`NodeQuiet`): `relW_of_decode` (the IR nodes are the
  REF reading's instantiations, wired as it names), then `InstWired.nodesInst_of_denI`,
  `NodesInst.fail_nil` and `coreNodeI_engine_nil`;
* `nodesInst_of_startPlay` (proved): the instantiation part of the IR play of
  `Task.startAdequacy` on an import-wired binary is node by node: the IR reading's nodes are
  core nodes `ps` and `NodesInst (Binary.coreModSemI (profile neverFail)) 1 ps t .ready`, each
  node's own instantiation play contributing its host calls to `t`, in order. The export call
  after `ready` is not decomposed;
* `starts_hostWired`, `trap_hostWired` (kernel, `decide +kernel`): both test binaries are
  import-wired;
* `trap_of_wired`: the reference half of `InstTestsRef.trap_agree` from `Task.failRefWired`,
  through `failAdequacyWired_of` (the conclusion is also proved unconditionally, by executing
  the reference machine: `InstTestsRef.trap_agree`).

**Not proved.** `Task.failRefWired` (the simulation of the reference machine's instantiation by
core engine runs), `Task.failAdequacy` outside import-wired binaries, and `Task.startAdequacy`.
-/

public section

namespace Silmaril.Wasm.Component.DecoderBridge

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Conformance
open Silmaril.Wasm.Component.InstRef Silmaril.Wasm.Component.InstLitmus
open Silmaril.Wasm.Component.InstTests Silmaril.Wasm.Component.InstTestsRef
open Silmaril.Wasm.Component.Reference.Core3Adder (first)

/-- **The reference half implies the failure goal on import-wired binaries.** -/
theorem failAdequacyWired_of (h : Task.failRefWired) : Task.failAdequacyWired :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.failAdequacyWired_of h

/-- **The instantiation part of a start play of an import-wired binary, node by node.** -/
theorem nodesInst_of_startPlay {b : ByteArray} {c : Comp Binary.CoreMod} {r : RefComponent}
    (hc : Binary.parseComponent b = .ok c) (hr : decodeRef b = .ok r) (hw : HostWired r)
    {t : List (Σ _ : sigU.Op, Option Payload)} {rest : List (Move sigU sigUI)}
    (hp : instPlay (F := sigU) t .ready ++ rest ∈
      c.denI (Binary.coreModSemI (Silmaril.Wasm.SingleThreaded.profile
        Silmaril.Wasm.SingleThreaded.neverFail))) :
    ∃ ps : List (Binary.CoreMod × List Impl), c.nodes = coreNodes ps ∧
      NodesInst (Binary.coreModSemI (Silmaril.Wasm.SingleThreaded.profile
        Silmaril.Wasm.SingleThreaded.neverFail)) c.imports.length ps t .ready :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.nodesInst_of_startPlay hc hr hw hp

/-- `starts.wasm` is import-wired. -/
theorem starts_hostWired : HostWired startsRef := by decide +kernel

/-- `trap.wasm` is import-wired. -/
theorem trap_hostWired : HostWired trapRef := by decide +kernel

/-- **`trap.wasm` from the reference half**, through `failAdequacyWired_of`. -/
theorem trap_of_wired (h : Task.failRefWired) :
    InstResult.traps ∈
      instBehaviours first.prof (Host.ofEmbedder embL) hostConfigX trapRef (importArgs hostI) :=
  failAdequacyWired_of h trapBytes trapComp trapRef parse_trap decodeRef_trap trap_valid
    trap_hostWired rfl (trap_inst _)

end Silmaril.Wasm.Component.DecoderBridge

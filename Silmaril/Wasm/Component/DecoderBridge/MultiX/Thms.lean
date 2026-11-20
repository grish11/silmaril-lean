module

public import Silmaril.Wasm.Component.DecoderBridge.MultiX.Defs
public import Silmaril.Wasm.Component.DecoderBridge.Multi.Thms
import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.ExportX
import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.CallLift
import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.RunShared
import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.ExportIR

/-!
# The instantiation on `MultiImpFrag` with its invariant: theorems

Proofs in `Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi` (`FirstKX`, `LaterCoreX`,
`NodesRefX`, `ComposeX`, `ExportX`, `CallLift`, `RunShared`, `ExportIR`).

* **`nodesRefX`** (proved): in the split fragment `MultiImpFrag`, the reference machine finishes
  the instantiation with the host log of the IR's node calls, in a configuration satisfying
  `NodesInv` (the final frame related to the reading, each node's core instance the gap image of
  its IR store after its start function);
* `nodesRef_of_X`: `Task.nodesRef` is its projection;
* `startAdequacyFrag_of_X`: **`Task.startAdequacy` on the fragment from `Task.exportRefX`** (the
  export call from the invariant);
* **`callLift`** (proved, `Multi.CallLift`): `Task.callLift`, the session call of an option-less
  lift of `func() -> u32` from a host-ready configuration (nesting depth `0`, which `NodesInv`
  records: the instantiation's invariant tracks depth `1` inside the host's program);
* `startAdequacyFrag_of_parts`, `starts_of_parts`: **the start goal and the `starts.wasm`
  instance from `Task.exportIR`, `Task.coreRunShared` and `Task.callLift`** (the export call from
  the invariant at the play's node ends, `Multi.exportRef_at`); `startAdequacyFrag_of_IR`: the
  start goal from the first two;
* **`coreRunShared`** (proved, `Multi.RunShared`): `Task.coreRunShared`, the node's run of an
  exported function in the shared core store: the node's store after its start run is split
  (`Linking.Split`), the run is relocated along the gap (`steps_gap`) and into the store extended by
  the later nodes' objects (`step_sim`, fresh structures and arrays renamed past them), and is an
  interpreter run there (the shared store typed, the callee's type read off the IR run's first
  step); `startAdequacyFrag_of_exportIR`, `starts_ref_of_ir`: the start goal and the reference
  half of `starts.wasm` from its IR run, given `Task.exportIR`;
* **`exportIR`** (proved, `Multi.ExportIR`): `Task.exportIR`. The play is taken apart node by node
  with one export call (`InstSem.denI_ex_node`: the environment invariant `EnvInvE` carried
  through `extI`; an import call is forwarded, so makes a call below, which the play has not); the
  owning node's engine instance runs its start function, then the export from the store it leaves
  (`InstSem.engineI_ex_inv`), and the export's run makes no import call (`exportRun_nil`: a typed
  run's import call has one `i32` argument, which `lowF` makes a call of `f`); the reading's core
  instances are laid out as the IR's environment (`refRead_layout`, `node_of_layout`), so the
  reading's export `e` is the IR's;
* **`startAdequacyFrag`**: `Task.startAdequacyFrag`, unconditionally;
  **`startAdequacyChecked_of_multiImpFrag`**: so the corrected start goal
  `Task.startAdequacyChecked` holds at every component of the fragment (which passes `RootChecked`,
  `Multi.Thms.rootChecked_of_multiImpFrag`); **`starts_ref_of_ir'`**: the
  reference half of `starts.wasm` from its IR run, unconditionally (the kernel cross-check
  `InstTestsRef.starts_agree` stays);
* `starts_of_X`: the reference half of `InstTestsRef.starts_agree`, derived from the IR's run of
  `starts.wasm` through `Task.exportRefX`. (The conclusion is also proved unconditionally by
  executing the reference machine, `InstTestsRef.starts_agree`.)

This is the split fragment only (function-only imports wired to `canon lower`ed component
imports, no shared memories or tables, option-less `canon lift` on flat primitive types), not
general shared memory, table or canonical ABI adequacy.
-/

public section

namespace Silmaril.Wasm.Component.DecoderBridge

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Conformance
open Silmaril.Wasm.Component.InstRef Silmaril.Wasm.Component.InstLitmus
open Silmaril.Wasm.Component.InstTests Silmaril.Wasm.Component.InstTestsRef
open Silmaril.Wasm.Component.Reference.Core3Adder (first)
open Silmaril.Wasm.SingleThreaded (profile neverFail)

/-- **The instantiation on the fragment, with node ends and the invariant `NodesInv`.** -/
theorem nodesRefX : Task.nodesRefX :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.nodesRefX

/-- `Task.nodesRef` is the projection of `Task.nodesRefX`. -/
theorem nodesRef_of_X (h : Task.nodesRefX) : Task.nodesRef :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.nodesRef_of_X h

/-- **The start goal on the fragment from the export call with the invariant.** -/
theorem startAdequacyFrag_of_X (hd : Task.exportRefX) : Task.startAdequacyFrag :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.startAdequacyFrag_of_X hd

/-- **`starts.wasm` from the IR's run, given the export call with the invariant.** -/
theorem starts_of_X (hd : Task.exportRefX) :
    (([some [toRefVal (.u32 42)]] : List (Option (List Value.Val))),
        ((), logOfCalls startsTrace)) ∈
      sessRunFrom first.prof (Host.ofEmbedder embL) hostConfigX startsRef (importArgs hostI)
        [("get", [])] :=
  starts_of_frag (startAdequacyFrag_of_X hd)

/-- **The start goal on the fragment from the three pieces of the export call**: the IR's export
phase (which chooses the node ends), the node's run in the shared core store and the session call
through `canon lift`. -/
theorem startAdequacyFrag_of_parts (hA : Task.exportIR) (hB : Task.coreRunShared)
    (hC : Task.callLift) : Task.startAdequacyFrag :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.startAdequacyFrag_of_IR hA hB hC

/-- **`starts.wasm` from the IR's run, given the three pieces of the export call.** -/
theorem starts_of_parts (hA : Task.exportIR) (hB : Task.coreRunShared) (hC : Task.callLift) :
    (([some [toRefVal (.u32 42)]] : List (Option (List Value.Val))),
        ((), logOfCalls startsTrace)) ∈
      sessRunFrom first.prof (Host.ofEmbedder embL) hostConfigX startsRef (importArgs hostI)
        [("get", [])] :=
  starts_of_frag (startAdequacyFrag_of_parts hA hB hC)

/-- **The session call through `canon lift`** (from a host-ready configuration: no host code
running, no lockdown, nesting depth `0`). -/
theorem callLift : Task.callLift :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.callLift

/-- **The start goal on the fragment from the IR's export phase and the node's run in the shared
core store.** -/
theorem startAdequacyFrag_of_IR (hA : Task.exportIR) (hB : Task.coreRunShared) :
    Task.startAdequacyFrag :=
  startAdequacyFrag_of_parts hA hB callLift

/-- **The node's run in the shared core store** (`Multi.RunShared`): from the split store the
node's start function leaves (`RunInv`, `nodeEnd_own`), along the gap (`steps_gap`) and into the
store extended by later nodes' objects (`Linking.Split.step_sim`), then as an interpreter run of
the typed shared store. -/
theorem coreRunShared : Task.coreRunShared :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.coreRunShared

/-- **The start goal on the fragment from the IR's export phase** (the remaining open piece). -/
theorem startAdequacyFrag_of_exportIR (hA : Task.exportIR) : Task.startAdequacyFrag :=
  startAdequacyFrag_of_IR hA coreRunShared

/-- **The reference half of `starts.wasm` from its IR run** (`InstTests.starts_inst`), through the
start goal on the fragment, given the IR's export phase. (The conclusion is also proved
unconditionally by executing the reference machine, `InstTestsRef.starts_agree`.) -/
theorem starts_ref_of_ir (hA : Task.exportIR) :
    (([some [toRefVal (.u32 42)]] : List (Option (List Value.Val))),
        ((), logOfCalls startsTrace)) ∈
      sessRunFrom first.prof (Host.ofEmbedder embL) hostConfigX startsRef (importArgs hostI)
        [("get", [])] :=
  starts_of_frag (startAdequacyFrag_of_exportIR hA)

/-- **The IR's export phase** (`Multi.ExportIR`): the play's node ends and, at them, the first
export is the option-less lift of a node's export, which runs host-free from the store the node's
start function left to one `i32`. -/
theorem exportIR : Task.exportIR :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.exportIR

/-- **`Task.startAdequacy` on the fragment `MultiImpFrag`.** -/
theorem startAdequacyFrag : Task.startAdequacyFrag :=
  startAdequacyFrag_of_exportIR exportIR

/-- **The corrected start goal on the fragment, proved**: `Task.startAdequacyChecked` at every
component of `MultiImpFrag`. The fragment lies inside the corrected goal's domain (`InFrag` and
`RootChecked`, `Multi.Thms.rootChecked_of_multiImpFrag`), so `Task.startAdequacyFrag` is exactly the
corrected goal restricted to it (`Multi.Thms.startAdequacyFrag_of_checked`); here that restriction
is discharged by `startAdequacyFrag`. -/
theorem startAdequacyChecked_of_multiImpFrag (b : ByteArray) (c : Comp Binary.CoreMod)
    (r : RefComponent) (t : List (Σ _ : sigU.Op, Option Payload)) (n : String)
    (ws : List Silmaril.Wasm.Component.Val)
    (hc : Binary.parseComponent b = .ok c) (hr : decodeRef b = .ok r)
    (hv : ∃ ct, Valid Features.p2 r ct) (_ : InFrag r) (_ : RootChecked r) (hf : MultiImpFrag r)
    (himp : c.imports = hostI) (hex : (c.exports.map (·.name)).head? = some n)
    (hu : ∀ x ∈ t, x.2 = InstTests.unitV)
    (hp : instPlay (F := sigU) t .ready ++
      [askEx (0, .vals []), ansEx (0, .vals []) (some (.vals ws))] ∈
        c.denI (Binary.coreModSemI (profile neverFail))) :
    (([some (ws.map toRefVal)] : List (Option (List Value.Val))), ((), logOfCalls t)) ∈
      sessRunFrom first.prof (Host.ofEmbedder embL) hostConfigX r (importArgs hostI) [(n, [])] :=
  startAdequacyFrag b c r t n ws hc hr hv hf himp hex hu hp

/-- **The reference half of `starts.wasm` from its IR run** (`InstTests.starts_inst`), through the
start goal on the fragment. (Also proved by executing the reference machine,
`InstTestsRef.starts_agree`, which stays as a kernel cross-check.) -/
theorem starts_ref_of_ir' :
    (([some [toRefVal (.u32 42)]] : List (Option (List Value.Val))),
        ((), logOfCalls startsTrace)) ∈
      sessRunFrom first.prof (Host.ofEmbedder embL) hostConfigX startsRef (importArgs hostI)
        [("get", [])] :=
  starts_ref_of_ir exportIR

end Silmaril.Wasm.Component.DecoderBridge

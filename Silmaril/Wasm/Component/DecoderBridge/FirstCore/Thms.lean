module

public import Silmaril.Wasm.Component.DecoderBridge.FirstCore.Defs
public import Silmaril.Wasm.Component.DecoderBridge.Sim.Thms
import Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore.Trap

/-!
# The reference half when the first core instantiation fails: theorems

Proofs in `Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore`.

* `firstCore_fail_ref` (proved): **on every import-wired binary of the first-core fragment
  (`FirstCoreFrag`), a quiet failure of the IR's core node `0` makes the reference machine's
  instantiation trap** (logging host `embL`, `hostConfigX`, root arguments `importArgs hostI`).
  This is the case `k = 0` of `Task.failRefWired`, for every decoded module in the fragment:
  the node fails because preparation of the module alone fails, or because its start function
  traps without calling an import. The proof runs the reference machine symbolically:
  - the definitions before the first core instantiation (`preOk`) trap with a specification
    trap (a missing or ill-typed import) or run silently, allocating host functions in the core
    store (`Proofs.….FirstCore.Prefix`, `Root`; over any engine);
  - the reference preparation of the module in that core store is the IR's preparation alone,
    mapped to the machine's host type and relocated past it (`CoreSim.prepareE_shift`, from
    `Reference.HostMap` and `Reference.CoreShift`); a failure traps `coreTrap`;
  - otherwise the start call reaches the core activation of the shifted start function
    (`Path.start_coreG`, over any engine and host state), and the IR's relational run of the
    start function to a trap, relocated (`Reference.ShiftStep.steps_shift`, split fragment),
    is matched by the interpreter run of the concrete engine `core3 neverFail` in the machine
    (`CoreRun.runCI_complete` along typing, `lrun_coreTrap`), which traps `coreTrap`;
* `failRefWired_of_rest` (proved): `Task.failRefWiredRest → Task.failRefWired`;
  `failAdequacyWired_of_rest`: hence `Task.failRefWiredRest → Task.failAdequacyWired`;
* `trap_firstCoreFrag`, `starts_not_firstCoreFrag` (kernel, `decide +kernel`): `trap.wasm` is in
  the fragment, `starts.wasm` is not (its first instantiated module imports `f`);
* `trap_of_firstCore` (proved, no hypothesis): the reference half of `InstTestsRef.trap_agree`
  derived from the IR's run of `trap.wasm` (`trapCM_nodeQuiet`) by `firstCore_fail_ref`, not by
  executing the reference machine (`InstTestsRef.trap_ref` executes it).

**Not proved.** `Task.failRefWiredRest`: a failure of node `k ≥ 1` (the ready start runs of
earlier nodes in the shared store are not simulated), modules with imports (a start function
calling a lowered import), memories, tables, tags, data or element segments, and the
definitions `preOk` excludes before the first core instantiation (aliases, `canon lift`,
exports, nested components, …). `Task.startAdequacy` (`starts.wasm`) is untouched.
-/

public section

namespace Silmaril.Wasm.Component.DecoderBridge

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Conformance
open Silmaril.Wasm.Component.InstRef Silmaril.Wasm.Component.InstLitmus
open Silmaril.Wasm.Component.InstTests Silmaril.Wasm.Component.InstTestsRef
open Silmaril.Wasm.Component.Reference.Core3Adder (first)
open Silmaril.Wasm.SingleThreaded (profile neverFail)

/-- **The reference machine traps when the IR's first core node fails**, on every import-wired
binary of the first-core fragment. -/
theorem firstCore_fail_ref {b : ByteArray} {c : Comp Binary.CoreMod} {r : RefComponent}
    {ps : List (Binary.CoreMod × List Impl)}
    (hc : Binary.parseComponent b = .ok c) (hr : decodeRef b = .ok r) (hw : HostWired r)
    (hf : FirstCoreFrag r) (hn : c.nodes = coreNodes ps) (h0 : 0 < ps.length)
    (hq : NodeQuiet hostI.length (.fail ()) (ps[0]'h0).1 (ps[0]'h0).2) :
    InstResult.traps ∈ instBehaviours first.prof (Host.ofEmbedder embL) hostConfigX r
      (importArgs hostI) :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore.firstCore_fail_ref hc hr hw hf hn h0 hq

/-- **`Task.failRefWired` from its remaining cases.** -/
theorem failRefWired_of_rest (h : Task.failRefWiredRest) : Task.failRefWired :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore.failRefWired_of_rest h

/-- The failure goal on import-wired binaries from the remaining cases. -/
theorem failAdequacyWired_of_rest (h : Task.failRefWiredRest) : Task.failAdequacyWired :=
  failAdequacyWired_of (failRefWired_of_rest h)

/-- `trap.wasm` is in the first-core fragment. -/
theorem trap_firstCoreFrag : FirstCoreFrag trapRef := by decide +kernel

/-- `starts.wasm` is not (its first instantiated module, `call1`, imports `f`). -/
theorem starts_not_firstCoreFrag : ¬ FirstCoreFrag startsRef := by decide +kernel

/-- The first core node of `trap.wasm` fails quietly. -/
theorem trapCM_nodeQuiet : NodeQuiet hostI.length (.fail ()) trapCM [] :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore.trapCM_nodeQuiet

/-- **`trap.wasm` from the IR's run, unconditionally**: `firstCore_fail_ref` at the failure of
its first core node. -/
theorem trap_of_firstCore :
    InstResult.traps ∈
      instBehaviours first.prof (Host.ofEmbedder embL) hostConfigX trapRef (importArgs hostI) :=
  firstCore_fail_ref (ps := [(trapCM, []), (call2CM, lowF)]) parse_trap decodeRef_trap
    trap_hostWired trap_firstCoreFrag rfl (by decide) trapCM_nodeQuiet

end Silmaril.Wasm.Component.DecoderBridge

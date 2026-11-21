module

public import Silmaril.Wasm.Component.DecoderBridge.FirstImp.Defs
public import Silmaril.Wasm.Component.DecoderBridge.FirstCore.Thms
import Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp.Calls

/-!
# The reference half when the first core instantiation, with lowered imports, fails: theorems

Proofs in `Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp`.

* `firstImp_fail_ref` (proved): **on every import-wired binary of the fragment `FirstImpFrag`
  importing `f: func(u32)`, a quiet failure of the IR's core node `0` makes the reference
  machine's instantiation trap** (logging host `embL`, `hostConfigX`, root arguments
  `importArgs hostI`). The first instantiated module may import functions: exactly the
  `canon lower` trampolines of `f` defined before it, in order, at core type `(func (param i32))`.
  The proof:
  - the definitions before the first core instantiation trap with a specification trap, or run
    silently to the core store of `n` trampolines (`lowStore n`, all with the host code of the
    lowering of `f`), the core functions `0, …, n - 1` and the inline core instances read by
    `preInsts` (`Proofs.….FirstImp.Prefix`, `Root`);
  - the module's imports resolve to the trampolines `0, …, n - 1` (`Core.coreImportsFor_low`:
    the names by `importsLowered`, the types by `refTypesOk`);
  - the IR's store of imports `irStore n` (host code `i` for import `i`) renames to `lowStore n`
    (`Sim.mapH_irStore`), and preparation and host-free runs commute with renaming host code
    (`Sim.prepareE_mapH`, `HostMap.Steps.mapH`): the reference preparation is the IR's, and the
    IR's run of the start function to a trap is matched by the interpreter run of the concrete
    engine in the machine (`Sim.startTrap_low`), which traps `coreTrap`;
  - a quiet failure of the node has **no import call** (`IR.nodeFailImp_cases`): the start
    thread is typed (`prepareE?_typed`, `reachable_typed`), so an import call has one `i32`
    argument (`callout_args_typed`), which lifts to a `u32`, so the wiring `lower` calls `f`
    instead of answering at once (`IR.implsN_lower_call`);
* `firstCore'_fail_ref` (proved): the same for the relaxed fragment
  `FirstCoreFrag' = FirstCoreFrag ∨ FirstImpFrag`;
* `failRefWiredRest_of_rest'` (proved): `Task.failRefWiredRest' → Task.failRefWiredRest`; hence
  `failRefWired_of_rest'`, `failAdequacyWired_of_rest'`;
* `starts_firstImpFrag`, `trap_not_firstImpFrag` (kernel, `decide +kernel`): `starts.wasm` is in
  the fragment (its first module, `call1`, imports `env.f`, the lowering of `f`); `trap.wasm` is
  not (a `canon lower` precedes its first module, which has no imports), but it is in
  `FirstCoreFrag'` through `FirstCoreFrag`.

**Host calls** (`NodeCalls`: each import call of the node's engine run answered by its wiring
with one call of the component's imports, the calls being `t`, each answered `()`):

* `firstImp_failCalls_ref` (proved): **a first node that fails after the host calls `t` makes the
  reference machine trap** (the start function may call `f` any number of times before it
  traps);
* `firstImp_ready_ref` (proved): **a first node that becomes ready after the host calls `t`**:
  the reference machine traps before the first core instantiation (a definition before it fails
  its import check: not excluded by the hypotheses), or the module has no start function and
  `t = []`, or the machine reaches the core activation of the start function at returned values,
  with the host state `((), logOfCalls t)`: the logging host saw the same calls, in the same
  order, with the same `u32` arguments. The proof runs each segment of the IR's start run in the
  machine (`Proofs.….FirstImp.Start.call_ref`): the core activation runs to the callout of the
  trampoline (`runCI_complete` along typing), the `canon lower` callout program lifts the `i32`
  argument to `u32`, calls `f` through the logging host and resumes the activation with no
  results (`Callout.hostCall_lrunX`, the `Reference.CalloutRun` path restated over any engine and
  function type), and the resumed thread is the IR's (`HostCode.resume_mapHG`).

**What a quiet failure excludes.** The failure goal (`Task.failAdequacy`) is about an IR
instantiation that fails *before any host call*. In the fragment, a start function that calls an
import reaches the host (`f`), so the failures `Task.failRefWired` covers are those before the
first import call; failures after host calls are `firstImp_failCalls_ref`.

**Not proved (the start goal).** `Task.startAdequacy` is untouched. `starts.wasm` instantiates
three core modules (`call1`, `call2`, `glob`), so it is not in a single-instantiation fragment:
`firstImp_ready_ref` covers its first node only, up to the return of `call1`'s start function.
`DecoderBridge.Multi` decomposes the start goal on the fragment `MultiImpFrag` and proves the IR
half (`NodeCalls` of each node from the IR's instantiation play) and the first node with the
start function's epilogue, and the later nodes in the shared core store (`call2`'s import resolves
to the same trampoline, behind `call1`'s functions; `Task.nodesRef`); the export phase
(`canon lift` of `get`) is open there (`Task.exportRef`).

**Not proved.** `Task.failRefWiredRest'`: a failure of node `k ≥ 1`, and the binaries outside
`FirstCoreFrag'` (other import shapes, the definitions `preOk` excludes, memories, tables, …).
-/

public section

namespace Silmaril.Wasm.Component.DecoderBridge

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Conformance
open Silmaril.Wasm.Component.InstRef Silmaril.Wasm.Component.InstLitmus
open Silmaril.Wasm.Component.InstTests Silmaril.Wasm.Component.InstTestsRef
open Silmaril.Wasm.Component.Reference.Core3Adder (first)

/-- **The reference machine traps when the IR's first core node fails**, on every import-wired
binary of the fragment with lowered imports. -/
theorem firstImp_fail_ref {b : ByteArray} {c : Comp Binary.CoreMod} {r : RefComponent}
    {ps : List (Binary.CoreMod × List Impl)}
    (hc : Binary.parseComponent b = .ok c) (hr : decodeRef b = .ok r) (hw : HostWired r)
    (hf : FirstImpFrag r) (himp : c.imports = hostI) (hn : c.nodes = coreNodes ps)
    (h0 : 0 < ps.length)
    (hq : NodeQuiet hostI.length (.fail ()) (ps[0]'h0).1 (ps[0]'h0).2) :
    InstResult.traps ∈ instBehaviours first.prof (Host.ofEmbedder embL) hostConfigX r
      (importArgs hostI) :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp.firstImp_fail_ref hc hr hw hf himp hn h0 hq

/-- **The reference machine traps when the IR's first core node fails**, on every import-wired
binary of the relaxed first-core fragment. -/
theorem firstCore'_fail_ref {b : ByteArray} {c : Comp Binary.CoreMod} {r : RefComponent}
    {ps : List (Binary.CoreMod × List Impl)}
    (hc : Binary.parseComponent b = .ok c) (hr : decodeRef b = .ok r) (hw : HostWired r)
    (hf : FirstCoreFrag' r) (himp : c.imports = hostI) (hn : c.nodes = coreNodes ps)
    (h0 : 0 < ps.length)
    (hq : NodeQuiet hostI.length (.fail ()) (ps[0]'h0).1 (ps[0]'h0).2) :
    InstResult.traps ∈ instBehaviours first.prof (Host.ofEmbedder embL) hostConfigX r
      (importArgs hostI) :=
  hf.elim (fun hf => firstCore_fail_ref hc hr hw hf hn h0 hq)
    (fun hf => firstImp_fail_ref hc hr hw hf himp hn h0 hq)

/-- **`Task.failRefWiredRest` from its remaining cases.** -/
theorem failRefWiredRest_of_rest' (h : Task.failRefWiredRest') : Task.failRefWiredRest :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp.failRefWiredRest_of_rest' h

/-- `Task.failRefWired` from the remaining cases of the relaxed fragment. -/
theorem failRefWired_of_rest' (h : Task.failRefWiredRest') : Task.failRefWired :=
  failRefWired_of_rest (failRefWiredRest_of_rest' h)

/-- The failure goal on import-wired binaries from the remaining cases of the relaxed fragment. -/
theorem failAdequacyWired_of_rest' (h : Task.failRefWiredRest') : Task.failAdequacyWired :=
  failAdequacyWired_of (failRefWired_of_rest' h)

/-- `starts.wasm` is in the fragment with lowered imports. -/
theorem starts_firstImpFrag : FirstImpFrag startsRef := by decide +kernel

/-- `trap.wasm` is not (a `canon lower` precedes its first module, which has no imports). -/
theorem trap_not_firstImpFrag : ¬ FirstImpFrag trapRef := by decide +kernel

/-- Both test binaries are in the relaxed first-core fragment. -/
theorem starts_firstCoreFrag' : FirstCoreFrag' startsRef := .inr starts_firstImpFrag

/-- `trap.wasm` is in the relaxed first-core fragment. -/
theorem trap_firstCoreFrag' : FirstCoreFrag' trapRef := .inl trap_firstCoreFrag

open Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Machine.StepDefs in
/-- **The reference machine traps when the IR's first core node fails after host calls**, on
every import-wired binary of the fragment with lowered imports. -/
theorem firstImp_failCalls_ref {b : ByteArray} {c : Comp Binary.CoreMod} {r : RefComponent}
    {ps : List (Binary.CoreMod × List Impl)} {t : List (Σ _ : sigU.Op, Option Payload)}
    (hc : Binary.parseComponent b = .ok c) (hr : decodeRef b = .ok r) (hw : HostWired r)
    (hf : FirstImpFrag r) (himp : c.imports = hostI) (hn : c.nodes = coreNodes ps)
    (h0 : 0 < ps.length) (hu : ∀ x ∈ t, x.2 = InstTests.unitV)
    (hq : NodeCalls hostI.length (.fail ()) (ps[0]'h0).1 (ps[0]'h0).2 t) :
    InstResult.traps ∈ instBehaviours first.prof (Host.ofEmbedder embL) hostConfigX r
      (importArgs hostI) :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp.firstImp_failCalls_ref hc hr hw hf himp hn
    h0 hu hq

open Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Machine.StepDefs in
open Silmaril.Wasm.SingleThreaded (neverFail) in
/-- **The reference machine when the IR's first core node is ready after host calls `t`**: it
traps before the first core instantiation, or `t = []` (no start function), or it reaches the
core activation of the start function at returned values with the host log `logOfCalls t`. -/
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
      (tR : Silmaril.Wasm.SingleThreaded.Thread) (fvs : List Flat),
      Steps first.prof embL.hr (Host.ofEmbedder embL).dispatch
        { hostConfigX with ctl := [.ofProg none (StepDefs.runProg (instantiateProg r (importArgs hostI)))] }
        tr M ∧
      M.ctl = ⟨thc, .core tR K, segs⟩ :: rest ∧
      (core3 neverFail).status M.store.core tR = .returned (.values fvs) ∧
      M.host = ((), logOfCalls t) :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp.firstImp_ready_steps hc hr hw hf himp hn h0
    hu hq

end Silmaril.Wasm.Component.DecoderBridge

module

public import Silmaril.Wasm.Component.DecoderBridge.Multi.Defs
public import Silmaril.Wasm.Component.DecoderBridge.Sim.Thms
import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.Compose
import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.Checked
import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.IR
import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.First
import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.Inst
import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.LaterFail

/-!
# Several core instantiations with lowered imports: theorems

Proofs in `Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi`.

* `startAdequacyFrag_of_nodes` (proved): **`Task.startAdequacy` on the fragment `MultiImpFrag`
  from** `Task.nodeCallsIR` (a), the instantiation `Task.nodesRef` ((b) and (c)) and
  `Task.exportRef` (d);
* `nodeCallsIR`, `firstNodeRef`, **`nodesRef`**: (a), (b) and the instantiation, proved;
* `startAdequacyFrag_of_d`: the goal on the fragment from (d) alone;
* `rootChecked_of_multiImpFrag`: every component of the fragment passes the reference machine's
  root checks (`RootChecked`, `Sem.Defs`), so `startAdequacyFrag_of_checked`: the goal on the
  fragment is an instance of the corrected start goal `Task.startAdequacyChecked`;
* `starts_multiImpFrag` (kernel, `decide +kernel`): `starts.wasm` is in the fragment;
* `starts_of_frag`, `starts_of_d`: the reference half of `InstTestsRef.starts_agree`, derived
  from the IR's run of `starts.wasm` (`starts_inst`) through the start goal on the fragment,
  resp. through (d). The conclusion is also proved unconditionally by executing the reference
  machine (`InstTestsRef.starts_agree`).
-/

public section

namespace Silmaril.Wasm.Component.DecoderBridge

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Conformance
open Silmaril.Wasm.Component.InstRef Silmaril.Wasm.Component.InstLitmus
open Silmaril.Wasm.Component.InstTests Silmaril.Wasm.Component.InstTestsRef
open Silmaril.Wasm.Component.Reference.Core3Adder (first)

/-- **Piece (a), the IR's node calls**: in the fragment, a ready node-by-node instantiation with
the calls `t`, each answered `()`, is the nodes' `NodeCalls` with the calls `ts`, `t = ts.flatten`. -/
theorem nodeCallsIR : Task.nodeCallsIR :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.nodeCallsIR

/-- **Piece (b), the first node with its start epilogue**: if the IR's first node is ready after
the calls `t₀`, the reference machine runs the definitions up to and including the first core
instantiation (root checks, trampolines, preparation, the start function with its host calls and
its epilogue), with the host log `logOfCalls t₀`. -/
theorem firstNodeRef : Task.firstNodeRef :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.firstNodeRef

/-- **Pieces (b) and (c), the instantiation**: in the fragment, if the IR's nodes are ready after
the calls `ts`, the reference machine finishes the instantiation with the host log
`logOfCalls ts.flatten`, the later core instantiations running in the shared core store. -/
theorem nodesRef : Task.nodesRef :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.nodesRef

/-- **The start goal on the fragment, from (a), the instantiation (`Task.nodesRef`) and (d).** -/
theorem startAdequacyFrag_of_nodes (ha : Task.nodeCallsIR) (hn : Task.nodesRef)
    (hd : Task.exportRef) : Task.startAdequacyFrag :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.startAdequacyFrag_of_nodes ha hn hd

/-- **A later node failing in the fragment**: `Task.failRefWiredRest'` from its rest
`Task.failRefWiredRest''`, the case of a node `k ≥ 1` of a binary of `MultiImpFrag` (quiet ready
nodes before it, then a quiet failure) being proved: the reference instantiation traps. -/
theorem failRefWiredRest'_of_rest'' (h : Task.failRefWiredRest'') : Task.failRefWiredRest' :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.failRefWiredRest'_of_rest''_of_firstK'
    Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.firstK' h

/-- **The start goal on the fragment from the export call (d).** -/
theorem startAdequacyFrag_of_d (hd : Task.exportRef) : Task.startAdequacyFrag :=
  startAdequacyFrag_of_nodes nodeCallsIR nodesRef hd

/-- **The fragment passes the root checks** (the root import is `f: func(x: u32)`, parameter name
included). -/
theorem rootChecked_of_multiImpFrag {r : RefComponent} (h : MultiImpFrag r) : RootChecked r :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.rootChecked_of_multiImpFrag h

/-- **The start goal on the fragment from the corrected start goal.** -/
theorem startAdequacyFrag_of_checked (h : Task.startAdequacyChecked) : Task.startAdequacyFrag :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.startAdequacyFrag_of_checked h

/-- `starts.wasm` is in the fragment. -/
theorem starts_multiImpFrag : MultiImpFrag startsRef := by decide +kernel

/-- **`starts.wasm` from the IR's run, through the start goal on the fragment.** -/
theorem starts_of_frag (h : Task.startAdequacyFrag) :
    (([some [toRefVal (.u32 42)]] : List (Option (List Value.Val))),
        ((), logOfCalls startsTrace)) ∈
      sessRunFrom first.prof (Host.ofEmbedder embL) hostConfigX startsRef (importArgs hostI)
        [("get", [])] :=
  h startsBytes startsComp startsRef startsTrace "get" [.u32 42] parse_starts decodeRef_starts
    starts_valid starts_multiImpFrag rfl rfl (by simp [startsTrace]) (starts_inst _)

/-- **`starts.wasm` from the IR's run, given the export call (d).** -/
theorem starts_of_d (hd : Task.exportRef) :
    (([some [toRefVal (.u32 42)]] : List (Option (List Value.Val))),
        ((), logOfCalls startsTrace)) ∈
      sessRunFrom first.prof (Host.ofEmbedder embL) hostConfigX startsRef (importArgs hostI)
        [("get", [])] :=
  starts_of_frag (startAdequacyFrag_of_d hd)

end Silmaril.Wasm.Component.DecoderBridge

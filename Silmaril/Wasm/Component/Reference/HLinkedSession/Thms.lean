module

public import Silmaril.Wasm.Component.Reference.HLinkedSession.Defs
public import Silmaril.Wasm.Component.Reference.LinkedSession.Thms
import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession.IR

/-!
# Linked components whose importer also has host imports: theorems

**Scope.** `HLinked2` (`Defs`): the import-free exporter A answers the wired imports of the
importer B, and B's remaining imports are host imports of the parent, passed through. This
module is groundwork for session adequacy with host imports. It is **not** an HLinked2 adequacy
theorem: only the specification to IR direction is proved in general.

## Proved

* **Translations** (`HLinked2.toComp_imports`, `HLinked2.den_sig`): the IR's lower interface is
  the host imports, so `l.toComp.den C : Strategy (sigN l.host.length) _`. A `Linked2` is the
  case without host imports (`Linked2.toH_toComp`, and `Linked2.toH_toRef` under
  `WireTy.length`).
* **#697's fixture is an instance** (`LinkedSession.linkedH_toRef : linkedH.toRef = linkedHRef`).
  Its closed reference facts are restated for `linkedH` (`linkedH_valid`,
  `linkedH_instantiates'`, `linkedH_noCallout'`, `linkedH_ping_callout'`, `linkedH_session'`,
  `linkedH_silent_session'`, `linkedH_silent_cannotBlock'`). `ping` makes exactly one host
  callout. Under a host that never answers, `ping` traps with `cannotBlockSync`. These are
  facts of the fixture over `core3 neverFail` with the oracle `first`, not general theorems.
* **Specification to IR, every `HLinked2`** (`HLinked2.sess_specToIR`, every profile `P`, given
  the exporter's and the importer's `Good`). A specification session (`HLinked2.SessSpec`) from
  the instances' stores is a play of `l.toComp.den (impSem P)` (`HLinked2.sessMoves`). The host
  calls of each round are visible import moves of `sigN l.host.length`, while the wired calls
  to A stay hidden. Traps continue: an exporter trap inside an import call, or a trap of B
  itself, answers `none` and the session goes on from the stores reached.
  Proofs: `Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession.{Games, IR}`.
* **Relocation of the exporter's nested instantiation** (proof level only:
  `Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession.InstReloc`).

## Not proved (what remains)

* **Reference to specification and specification to reference.** The resumable sessions of
  `l.toRef` under `answerHostS P (logG g)` (`HLinked2.sessObs`) are not related to
  `HLinked2.SessSpec` with `HostRun g` on the host calls. The `Linked2` proofs (#705, #712) rest
  on the instantiation of an import-free parent (`InstLink*`) and on the linked call machinery
  (`LinkCall*`, `LinkedSessionRef`, `LinkedSessionFwd`). Both are specific to the `Linked2`
  layout: no host functions before the parent's component functions, and only exporter
  trampolines in the importer's core store. With host imports, the parent's component functions
  are shifted by `host.length`, and B's store also holds `canon lower` trampolines of host
  functions, which dispatch to `hostCalloutProg` (`CalloutRun`) instead of a nested lift.
  Generalising that machinery over the layout is the next step. Its first relocation lemma is
  proved at proof level: `Proofs.….HLinkedSession.InstReloc.instantiateCall_simpleO`, the
  exporter's nested instantiation in a store that already holds `o` component functions, with
  export `i` at function `o + i` (`instantiateCall_simple'` is `o = 0`). The next lemmas, in
  order, are these:
  - the parent's definitions run (`toRefL_run` with `importsDefs_runG` for the host prefix,
    `instantiateCall_simpleO` at `o = host.length`, and `instantiateCall_simpleI'` with
    `fid n = if n < wire.length then host.length + wire[n] else n - wire.length`);
  - the root call with imports and the uniqueness of the instantiation (`rootCallL_run`,
    `instBehavioursL_toRef`, from `hostConfig host`);
  - `coreFactsL_of_inst` for that `fid`;
  - the forward linked call with host trampolines (`LinkedSessionFwd` with
    `CalloutRun.runs_callout` at host trampolines);
  - its backward counterpart (`LinkedSessionRef`).
* **IR to specification**, the read-back of #724 with host moves visible.
* **The general synchronous silent-host theorem**: for every `HLinked2`, an export call whose
  importer calls a host import under a host that never answers traps with `cannotBlockSync`.
  It needs the forward linked call above. Only the fixture fact is proved. Under synchronous
  lowering the blocked host is a trap. An asynchronous lower or lift (a genuine pending
  observation) is out of scope and comes later.
* **Bridge to the divergence-aware semantics**: `Linked2.compSession` (#728) is defined from
  `Linked2.SessSpec`. It is not yet proved equal to `Comp.denUD (core3SemD P)` (#750) with the
  canonical-ABI adapters, and the same holds for any `HLinked2` analogue.
* n-ary and nested components wait on the H2 owner's host hiding and `ext` laws (#207). The
  parser from bytes to these components, and F6, are pending.
-/

public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine

local notation "IVal" => Silmaril.Wasm.Component.Val

namespace HLinked2

/-! ## The translations -/

/-- The imports of the IR are the host imports (proved). -/
@[simp] theorem toComp_imports (l : HLinked2) : l.toComp.imports = l.host := rfl

/-- **The host imports are the lower interface of the IR** (proved). -/
theorem den_sig (l : HLinked2) : l.toComp.imports.sig = sigN l.host.length := rfl

end HLinked2

/-- **A `Linked2` is an `HLinked2` without host imports**: the IR (proved). -/
theorem Linked2.toH_toComp (l : Linked2) : l.toH.toComp = l.toComp := by
  simp [Linked2.toH, HLinked2.toComp, Linked2.toComp, HLinked2.wireArgs, HLinked2.hostArgs]

/-- **A `Linked2` is an `HLinked2` without host imports**: the reference translation, for a
wiring with one entry per import (proved). -/
theorem Linked2.toH_toRef (l : Linked2) (h : l.wire.length = l.imp.imports.length) :
    l.toH.toRef = l.toRef := by
  have hargs : (l.toH.imp.imports.mapIdx fun n p => (p.1, (⟨.func, l.toH.importFid n⟩ :
      Syntax.SortIdx Syntax.Sort_))) =
      l.imp.imports.mapIdx fun k p => (p.1, ⟨.func, k⟩) := by
    refine List.ext_getElem (by simp [Linked2.toH]) fun n h₁ _ => ?_
    have hn : n < l.wire.length := by rw [h]; simpa [Linked2.toH] using h₁
    simp [HLinked2.importFid, Linked2.toH, hn]
  unfold HLinked2.toRef Linked2.toRef
  rw [hargs]
  simp [Linked2.toH, SimpleI.importsDefs]

namespace LinkedSession

/-! ## #697's host-import fixture -/

/-- **#697's `linkedHRef` is the reference translation of `linkedH`** (proved). -/
theorem linkedH_toRef : linkedH.toRef = linkedHRef := rfl

/-- The host imports of `linkedH` are `hostIface` (proved). -/
theorem linkedH_host : linkedH.host = hostIface := rfl

/-- The validator accepts `linkedH.toRef` (proved, #697's `linkedHRef_valid`). -/
theorem linkedH_valid : ∃ ct, check? Features.p2 linkedH.toRef = .ok ct := linkedHRef_valid

/-- `linkedH.toRef` instantiates on the reference machine (proved, #697). -/
theorem linkedH_instantiates' : ∃ m inst es, InstResult.instance m inst es ∈
    instBehaviours first.prof (Host.ofEmbedder embCount) (hostConfig linkedH.host 0) linkedH.toRef
      (importArgs linkedH.host) :=
  linkedH_instantiates

/-- **No host callout for `poke` and `peek`** (proved, #697): with the counting host, the
session `poke, peek` answers `trap, 1` and the host state stays `0`. -/
theorem linkedH_noCallout' :
    ([none, some [toRefVal (.u32 1)]], 0) ∈ sessRunBehaviours first.prof
      (Host.ofEmbedder embCount) 0 linkedH.toRef linkedH.host [("poke", []), ("peek", [])] :=
  linkedH_noCallout

/-- **`ping` makes exactly one host callout** (proved, #697): it returns and the counting host
ends in state `1`. -/
theorem linkedH_ping_callout' :
    ([some []], 1) ∈ sessRunBehaviours first.prof (Host.ofEmbedder embCount) 0 linkedH.toRef
      linkedH.host [("ping", [])] :=
  linkedH_ping_callout

/-- The session `poke, peek, ping` of `linkedH` with the counting host (proved, #697). -/
theorem linkedH_session' :
    ([none, some [toRefVal (.u32 1)], some []], 1) ∈ sessRunBehaviours first.prof
      (Host.ofEmbedder embCount) 0 linkedH.toRef linkedH.host
        [("poke", []), ("peek", []), ("ping", [])] :=
  linkedH_session

/-- **A host that never answers** (proved, #697): the session `poke, peek, ping` answers
`trap, 1, trap`. The trap of `ping` is a trap of the synchronous fragment, not a pending call. -/
theorem linkedH_silent_session' :
    ([none, some [toRefVal (.u32 1)], none], 0) ∈ sessRunBehaviours first.prof
      (Host.ofEmbedder embSilent) 0 linkedH.toRef linkedH.host
        [("poke", []), ("peek", []), ("ping", [])] :=
  linkedH_silent_session

/-- **The trap of `ping` under the silent host is `cannotBlockSync`** (proved, #697; fixture
only). -/
theorem linkedH_silent_cannotBlock' :
    callTraps embSilent first 400 linkedH.toRef linkedH.host 0 "ping" [] =
      some [.cannotBlockSync] :=
  linkedH_silent_cannotBlock

end LinkedSession

/-! ## Specification to IR -/

/-- **Specification sessions of a linked component with host imports are IR plays** (proved,
every profile): a `HLinked2.SessSpec` session from the stores of the exporter's and the
importer's instances is a play of `l.toComp.den (impSem P)`, each call with its host calls as
visible import moves. -/
theorem HLinked2.sess_specToIR {P : Profile} {l : HLinked2} (he : l.exp.Good) (hi : l.imp.Good)
    {Ie : Silmaril.Wasm.Game.ScalarInstance} (hIe : l.exp.mod.IsInst Ie)
    {Ii : Silmaril.Wasm.Game.ScalarInstance} (hIi : l.imp.mod.IsInst Ii)
    {calls : List (Fin l.imp.exports.length × List IVal)} {outs : List (Option (List IVal))}
    {hs : List (List (Σ _ : (sigN l.host.length).Op, Option Payload))}
    {u' π' : Silmaril.Wasm.Execution.Core.Store Nat}
    (h : HLinked2.SessSpec P l Ie Ii Ii.store Ie.store calls outs hs u' π') :
    l.sessMoves calls outs hs ∈ l.toComp.den (impSem P) :=
  Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession.hlinked2_sess_specToIR he hi hIe hIi h

/-- A specification session has one outcome and one list of host calls per call (proved). -/
theorem HLinked2.SessSpec.length {P : Profile} {l : HLinked2}
    {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {u π u' π' : Silmaril.Wasm.Execution.Core.Store Nat}
    {calls : List (Fin l.imp.exports.length × List IVal)} {outs : List (Option (List IVal))}
    {hs : List (List (Σ _ : (sigN l.host.length).Op, Option Payload))}
    (h : HLinked2.SessSpec P l Ie Ii u π calls outs hs u' π') :
    calls.length = outs.length ∧ calls.length = hs.length :=
  Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession.sessSpecH_length h

end Silmaril.Wasm.Component.Reference

module

public import Silmaril.Wasm.Component.Reference.HLinkedSession.Defs
public import Silmaril.Wasm.Component.Reference.LinkedSession.Thms
import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession.IR
import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession.Inst
import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession.SilentCall
import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession.Host
import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession.Sess

/-!
# Linked components whose importer also has host imports: theorems

**Scope.** `HLinked2` (`Defs`): the import-free exporter A answers the wired imports of the
importer B, and B's remaining imports are host imports of the parent, passed through. This
module is groundwork for session adequacy with host imports. It is **not** an HLinked2 adequacy
theorem: the instantiation, the specification to IR direction, the specification to reference
direction (for a typed host) and the silent-host traps are proved in general; the converse
directions are not.

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
* **Instantiation, every `HLinked2`** (`HLinked2.instantiates`, every profile, any host, under
  `HLinked2.Adequate`). From the host functions of `l.host` (`hostConfig`, import `k` bound to
  host function `k`), the only result of instantiating `l.toRef` is an instance with root
  instance `0` and the export map `HLinked2.exportMap`: export `i` of the importer is component
  function `host.length + exp.exports.length + i`. A `Linked2` is the case without host
  imports (`Linked2.Adequate.toH`). Proof:
  `Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession.Inst`. The layout it establishes:
  the host functions are component functions `0, …, k - 1`, the exporter's lifted functions
  follow (`InstReloc.instantiateCall_simpleO` at `o = k`), and import `n` of the importer is
  bound to `HLinked2.fid n` (`k + wire[n]` for a wired import, `n - wire.length` for a host
  import). The importer's core facts in the shared store are `coreFactsL_of_inst` at the
  lowered callees `l.fid` (`coreFactsH_of_inst`); the configuration reached is `afterLinkH`
  (`instBehavioursH_inst`).
* **A host that never answers, every `HLinked2`** (`HLinked2.silent_cannotBlock`,
  `HLinked2.silent_session`, every profile, under `HLinked2.Adequate`). For the first call after
  instantiation: a typed call whose specification round (a well-formed `SessRound` of the
  importer's instance from its store, its import calls an `ExpRunH` segment of the exporter
  from its store) makes a host call traps with reason `cannotBlockSync` under `silentHost`,
  with no host event and no other trap before; its one-call session answers `none`
  (`silentObs`). The run: the invocation and the prefix of the importer's lift; the importer's
  core activation with its returned nested calls to the exporter, up to the callout of the
  first host call; the callout program, whose host function takes the arguments and does not
  resolve the subtask, so that `canon_lower` waits on it and the thread blocks; and the
  synchronous lift loop, which finds no ready thread in the importer's instance. Proofs:
  `Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession.{Stat, Round, Silent, SilentCall}`,
  over the forward invariants of `LinkedSessionFwd` restated at the host-first layout
  (`HStat`, `LInv`/`LReady`/`ReadyL` at the renaming `gL P l.toW`, with `l.toW` wiring import
  `n` to `l.fid n`; `hstat_init`, `readyH_init` at `afterLinkH`).
* **The forward host-call segment** (`Proofs.….HLinkedSession.Host`, not restated here): at
  the callout of a host import under `answerHostS P g`, a well-typed answer of `g` runs the
  machine quietly to the importer's core activation resumed with the lowered answer, one more
  subtask and caller record in the store and the new host state (`hostCall_fwd`); no answer, or
  arguments that do not lift, trap with a specification trap (`hostCall_noAnswer`,
  `hostCall_noLift`); the importer's part resumed alongside keeps `LInv`
  (`LInv.resumeHost_fwdH`). **A host answer that is not well typed is not a trap**: it is the
  `internal` fault `lower_flat: value does not match type`, which `Calls` does not count as a
  trap. For example a host import `func() -> u32` answered `[]` (`HostAnswersS` with
  `R = some (.vals [])`) traps in the specification but faults on the reference machine, so the
  specification to reference direction needs a typed host.

* **Specification to reference, every `HLinked2`, typed host** (`HLinked2.sess_specToRef`,
  every profile, under `HLinked2.Adequate` and `HLinked2.HostTyped g`). A specification session
  from the instances' stores whose host calls (`hs`, all rounds) are answered by the logging
  host of `g` from `(s₀, [])` to `st'` (`HostRun (logG g)`) is a session observation of `l.toRef`
  under `answerHostS P (logG g)` with the final host state and log `st'`. Each round is
  `Proofs.….HLinkedSession.linkCall_fwdH` (not restated here): from the configuration between
  calls (`ReadyL` at `l.toW`), the round with every host call answered is a call ending between
  calls with `ReadyL` again, or a trapped call with `LReady` at the trapped core store and the
  host state of the trap, from which the session resumes (`resumeCfg`). Along a round the
  configurations are `extG` extensions of the call's frame (a host callout appends a subtask and
  a caller record, no task or thread; `extN_extG`, `extG_hostCall`), and the trapping runs carry
  the host state (`TrapsAtSH`, `TrapEndH`, `nest_atTSH`, `CallAtLKTS.trapGH` and `blockH`).
  Proofs: `Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession.{TrapH, Call, Sess}`.
  **The typed-host hypothesis is needed** (see the host-call segment above): with a host import
  `func() -> u32` and `g` answering `[]`, the specification session answers a trap (`HostRun`
  holds with the answer `some (.vals [])`), while the reference call faults `internal`
  (`flatMismatch`) and so has no session outcome.
* **A host that never answers, any call of a session** (`HLinked2.silent_specToRef`,
  `HLinked2.silent_cannotBlock_sess`, `HLinked2.silent_session_sess`, under
  `HLinked2.Adequate`). A specification session whose host calls are all answered by a trap
  (`HostRun silentG`) is a session observation under `silentHost` (`silentObs`), the host state
  unchanged; after it, a typed call whose round makes a host call traps `cannotBlockSync` with
  no host event and no other trap after its invocation, and the session extended by that call
  answers a trap for it. This generalises `HLinked2.silent_cannotBlock` (the first call after
  instantiation).

## Not proved (what remains)

* **Reference to specification.** The resumable sessions of `l.toRef` under
  `answerHostS P (logG g)` (`HLinked2.sessObs`) are not shown to be specification sessions: the
  backward counterpart of `linkCall_fwdH` (`LinkedSessionRef` at the host-first layout) is
  missing.
* **IR to specification**, the read-back of #724 with host moves visible.
* Under synchronous lowering the blocked host is a trap. An asynchronous lower or lift (a
  genuine pending observation) is out of scope and comes later.
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

/-! ## Instantiation -/

/-- **A `Linked2` with adequate parts is an `HLinked2` with adequate parts** (proved). -/
theorem Linked2.Adequate.toH {l : Linked2} (hl : l.Adequate) : l.toH.Adequate :=
  ⟨hl.expGood, hl.expInst, hl.impGood, hl.impInst, hl.impArity, hl.impFloatFree,
    ⟨by simp [HLinked2.Shape, Linked2.toH, hl.wireTy.length], hl.wireTy.ty⟩, hl.namesOk,
    hl.wireNodup, hl.splitOk⟩

/-- **`l.toRef` instantiates, uniquely, for adequate parts** (proved, every profile, any host):
from the host functions of `l.host`, import `k` bound to host function `k`, there is a
configuration `m`, the host in control in the initial host state, such that the instance at
`m` with root instance `0` and the export map `l.exportMap` is a result of instantiating
`l.toRef`, and the only one. -/
theorem HLinked2.instantiates (P : Profile) (prof : ProfileKind) {l : HLinked2}
    (hl : l.Adequate) {σ : Type} (h : Host (core3P P) σ) (h₀ : σ) :
    ∃ m : Machine.Config (core3P P) σ, m.ctl = [] ∧ m.host = h₀ ∧
      InstResult.instance m ⟨0⟩ l.exportMap ∈
        instBehaviours prof h (LinkedSession.hostConfig l.host h₀) l.toRef (importArgs l.host) ∧
      ∀ r ∈ instBehaviours prof h (LinkedSession.hostConfig l.host h₀) l.toRef
          (importArgs l.host),
        r = .instance m ⟨0⟩ l.exportMap :=
  Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession.hlinked2_instantiates P prof hl h h₀

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

/-! ## A host that never answers -/

/-- **Under a host that never answers, a call whose round makes a host call traps
`cannotBlockSync`** (proved, every profile and component choice profile, adequate parts): let
`d` be a well-formed round of the importer's instance from its store (the typed call of export
`d.j` on `d.vs`), whose component import calls are an `ExpRunH` segment of the exporter from its
store and contain a host call. From the instance `m` of `l.toRef` under `silentHost`, the
invocation of the importer's export runs, with no host event and no trap on the way, to the trap
`cannotBlockSync`, which locks the store down: the importer's thread waits on the unresolved
host call, and the synchronous lift loop finds no ready thread (REF `trap_if(not candidates)`). -/
theorem HLinked2.silent_cannotBlock (P : Profile) (prof : ProfileKind) {l : HLinked2}
    (hl : l.Adequate) {σ : Type} (h₀ : σ) {Ie Ii : Silmaril.Wasm.Game.ScalarInstance}
    (hIe : l.exp.mod.IsInst Ie) (hIi : l.imp.mod.IsInst Ii) (d : Linked2.SessRound l.toL2 Ii)
    (hok : d.Ok) {u₁ π₁ : Silmaril.Wasm.Execution.Core.Store Nat}
    (hpath : Ii.Path P (.idle Ii.store) d.instMoves (.idle u₁))
    (hexp : HLinked2.ExpRunH P l Ie Ie.store d.dss.flatten π₁)
    (hh : l.hostCalls d.dss.flatten ≠ []) :
    ∃ m : Machine.Config (core3P P) σ, m.ctl = [] ∧ m.host = h₀ ∧
      InstResult.instance m ⟨0⟩ l.exportMap ∈ instBehaviours prof (HLinked2.silentHost P)
        (LinkedSession.hostConfig l.host h₀) l.toRef (importArgs l.host) ∧
      ∃ (tr : List (Label (core3P P) σ)) (m' : Machine.Config (core3P P) σ),
        Steps prof (HLinked2.silentHost P).hr (HLinked2.silentHost P).dispatch m
          (.host (.invoke ⟨0⟩ ⟨l.host.length + l.exp.exports.length + d.j⟩
            (d.vs.map toRefVal)) :: (tr ++ [.trap .cannotBlockSync])) m' ∧
        (∀ ev, Label.host ev ∉ tr) ∧ (∀ r, Label.trap r ∉ tr) ∧ m'.store.lockdown = true :=
  Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession.hlinked2_silent_cannotBlock P prof hl
    h₀ hIe hIi d hok hpath hexp hh

/-- **Under a host that never answers, the session of such a call answers a trap** (proved):
`([none], s) ∈ HLinked2.silentObs` for some final host state `s`. -/
theorem HLinked2.silent_session (P : Profile) (prof : ProfileKind) {l : HLinked2}
    (hl : l.Adequate) {σ : Type} (h₀ : σ) {Ie Ii : Silmaril.Wasm.Game.ScalarInstance}
    (hIe : l.exp.mod.IsInst Ie) (hIi : l.imp.mod.IsInst Ii) (d : Linked2.SessRound l.toL2 Ii)
    (hok : d.Ok) {u₁ π₁ : Silmaril.Wasm.Execution.Core.Store Nat}
    (hpath : Ii.Path P (.idle Ii.store) d.instMoves (.idle u₁))
    (hexp : HLinked2.ExpRunH P l Ie Ie.store d.dss.flatten π₁)
    (hh : l.hostCalls d.dss.flatten ≠ []) :
    ∃ s : σ, ([none], s) ∈ HLinked2.silentObs P prof l h₀ [(d.j, d.vs)] :=
  Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession.hlinked2_silent_session P prof hl h₀
    hIe hIi d hok hpath hexp hh

/-! ## Specification to reference -/

/-- **Specification sessions with a typed host are reference sessions, with the host state and
log** (proved, every profile and component choice profile, adequate parts, `HostTyped g`): the
reference images of the outcomes of every `HLinked2.SessSpec` session from the instances' stores,
whose host calls are answered by the logging host of `g` from the initial state `s₀` and the
empty log to `st'`, are a session observation of `l.toRef` with the final host state and log
`st'`. -/
theorem HLinked2.sess_specToRef (P : Profile) (prof : ProfileKind) {l : HLinked2}
    (hl : l.Adequate) {σ : Type}
    (g : σ → HostFuncId → List Silmaril.Wasm.Component.Value.Val →
      Option (List Silmaril.Wasm.Component.Value.Val × σ))
    (hT : l.HostTyped g) (s₀ : σ) {Ie Ii : Silmaril.Wasm.Game.ScalarInstance}
    (hIe : l.exp.mod.IsInst Ie) (hIi : l.imp.mod.IsInst Ii)
    {calls : List (Fin l.imp.exports.length × List IVal)} {outs : List (Option (List IVal))}
    {hs : List (List (Σ _ : (sigN l.host.length).Op, Option Payload))}
    {u' π' : Silmaril.Wasm.Execution.Core.Store Nat}
    (h : HLinked2.SessSpec P l Ie Ii Ii.store Ie.store calls outs hs u' π')
    {st' : σ × List HLinked2.HostEvent} (hr : HostRun (HLinked2.logG g) (s₀, []) hs.flatten st') :
    (refOuts outs, st') ∈ HLinked2.sessObs P prof l g s₀ calls :=
  Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession.hlinked2_sess_specToRef P prof hl g hT
    s₀ hIe hIi h hr

/-- **Under a host that never answers, specification sessions whose host calls are all answered
by a trap are reference sessions** (proved, adequate parts), the host state unchanged. -/
theorem HLinked2.silent_specToRef (P : Profile) (prof : ProfileKind) {l : HLinked2}
    (hl : l.Adequate) {σ : Type} (h₀ : σ) {Ie Ii : Silmaril.Wasm.Game.ScalarInstance}
    (hIe : l.exp.mod.IsInst Ie) (hIi : l.imp.mod.IsInst Ii)
    {calls : List (Fin l.imp.exports.length × List IVal)} {outs : List (Option (List IVal))}
    {hs : List (List (Σ _ : (sigN l.host.length).Op, Option Payload))}
    {u' π' : Silmaril.Wasm.Execution.Core.Store Nat}
    (h : HLinked2.SessSpec P l Ie Ii Ii.store Ie.store calls outs hs u' π')
    (hr : HostRun HLinked2.silentG h₀ hs.flatten h₀) :
    (refOuts outs, h₀) ∈ HLinked2.silentObs P prof l h₀ calls :=
  Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession.hlinked2_silent_specToRef P prof hl h₀
    hIe hIi h hr

/-- **Under a host that never answers, any call of a session whose round makes a host call
traps `cannotBlockSync`** (proved, adequate parts): after a specification session `calls` from
the instances' stores whose host calls are all answered by a trap, ending at the importer's and
the exporter's stores `u`, `π`, let `d` be a well-formed round of the importer's instance from
`u` whose import calls are an `ExpRunH` segment of the exporter from `π` and contain a host call.
The session of `calls` under `silentHost` reaches a configuration `m₁` in the initial host state,
from which the invocation of the importer's export `d.j` (top-level call `calls.length`) runs,
with no host event and no trap on the way, to the trap `cannotBlockSync`, which locks the store
down. -/
theorem HLinked2.silent_cannotBlock_sess (P : Profile) (prof : ProfileKind) {l : HLinked2}
    (hl : l.Adequate) {σ : Type} (h₀ : σ) {Ie Ii : Silmaril.Wasm.Game.ScalarInstance}
    (hIe : l.exp.mod.IsInst Ie) (hIi : l.imp.mod.IsInst Ii)
    {calls : List (Fin l.imp.exports.length × List IVal)} {outs : List (Option (List IVal))}
    {hs : List (List (Σ _ : (sigN l.host.length).Op, Option Payload))}
    {u π : Silmaril.Wasm.Execution.Core.Store Nat}
    (h : HLinked2.SessSpec P l Ie Ii Ii.store Ie.store calls outs hs u π)
    (hr : HostRun HLinked2.silentG h₀ hs.flatten h₀) (d : Linked2.SessRound l.toL2 Ii)
    (hok : d.Ok) {u₁ π₁ : Silmaril.Wasm.Execution.Core.Store Nat}
    (hpath : Ii.Path P (.idle u) d.instMoves (.idle u₁))
    (hexp : HLinked2.ExpRunH P l Ie π d.dss.flatten π₁)
    (hh : l.hostCalls d.dss.flatten ≠ []) :
    ∃ m : Machine.Config (core3P P) σ,
      InstResult.instance m ⟨0⟩ l.exportMap ∈ instBehaviours prof (HLinked2.silentHost P)
        (LinkedSession.hostConfig l.host h₀) l.toRef (importArgs l.host) ∧
      ∃ m₁ : Machine.Config (core3P P) σ,
        LinkedSession.SessRun prof (HLinked2.silentHost P) m 0
          (calls.map fun q => (⟨l.host.length + l.exp.exports.length + q.1⟩, q.2.map toRefVal))
          (refOuts outs) m₁ ∧ m₁.host = h₀ ∧
        ∃ (tr : List (Label (core3P P) σ)) (m' : Machine.Config (core3P P) σ),
          Steps prof (HLinked2.silentHost P).hr (HLinked2.silentHost P).dispatch m₁
            (.host (.invoke ⟨calls.length⟩ ⟨l.host.length + l.exp.exports.length + d.j⟩
              (d.vs.map toRefVal)) :: (tr ++ [.trap .cannotBlockSync])) m' ∧
          (∀ ev, Label.host ev ∉ tr) ∧ (∀ r, Label.trap r ∉ tr) ∧ m'.store.lockdown = true :=
  Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession.hlinked2_silent_cannotBlock_sess P prof
    hl h₀ hIe hIi h hr d hok hpath hexp hh

/-- **Under a host that never answers, the session extended by such a call answers a trap for
it** (proved): `(refOuts outs ++ [none], s) ∈ HLinked2.silentObs` for some final host state. -/
theorem HLinked2.silent_session_sess (P : Profile) (prof : ProfileKind) {l : HLinked2}
    (hl : l.Adequate) {σ : Type} (h₀ : σ) {Ie Ii : Silmaril.Wasm.Game.ScalarInstance}
    (hIe : l.exp.mod.IsInst Ie) (hIi : l.imp.mod.IsInst Ii)
    {calls : List (Fin l.imp.exports.length × List IVal)} {outs : List (Option (List IVal))}
    {hs : List (List (Σ _ : (sigN l.host.length).Op, Option Payload))}
    {u π : Silmaril.Wasm.Execution.Core.Store Nat}
    (h : HLinked2.SessSpec P l Ie Ii Ii.store Ie.store calls outs hs u π)
    (hr : HostRun HLinked2.silentG h₀ hs.flatten h₀) (d : Linked2.SessRound l.toL2 Ii)
    (hok : d.Ok) {u₁ π₁ : Silmaril.Wasm.Execution.Core.Store Nat}
    (hpath : Ii.Path P (.idle u) d.instMoves (.idle u₁))
    (hexp : HLinked2.ExpRunH P l Ie π d.dss.flatten π₁)
    (hh : l.hostCalls d.dss.flatten ≠ []) :
    ∃ s : σ, (refOuts outs ++ [none], s) ∈
      HLinked2.silentObs P prof l h₀ (calls ++ [(d.j, d.vs)]) :=
  Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession.hlinked2_silent_session_sess P prof hl
    h₀ hIe hIi h hr d hok hpath hexp hh

end Silmaril.Wasm.Component.Reference

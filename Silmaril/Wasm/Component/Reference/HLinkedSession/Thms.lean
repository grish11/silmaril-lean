module

public import Silmaril.Wasm.Component.Reference.HLinkedSession.Defs
public import Silmaril.Wasm.Component.Reference.LinkedSession.Thms
import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession.IR
import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession.Inst

/-!
# Linked components whose importer also has host imports: theorems

**Scope.** `HLinked2` (`Defs`): the import-free exporter A answers the wired imports of the
importer B, and B's remaining imports are host imports of the parent, passed through. This
module is groundwork for session adequacy with host imports. It is **not** an HLinked2 adequacy
theorem: the instantiation and the specification to IR direction are proved in general.

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

## Not proved (what remains)

* **Reference to specification and specification to reference.** The resumable sessions of
  `l.toRef` under `answerHostS P (logG g)` (`HLinked2.sessObs`) are not related to
  `HLinked2.SessSpec` with `HostRun g` on the host calls. The instantiation of `l.toRef` is
  proved (`HLinked2.instantiates`, above). The `Linked2` session proofs (#705, #712) also rest
  on the linked call machinery (`LinkCall*`, `LinkedSessionRef`, `LinkedSessionFwd`), which is
  specific to the `Linked2` layout: no host functions before the parent's component functions,
  and only exporter trampolines in the importer's core store. With host imports, the parent's
  component functions are shifted by `host.length`, and B's store also holds `canon lower`
  trampolines of host functions, which dispatch to `hostCalloutProg` (`CalloutRun`) instead of
  a nested lift. The next lemmas, in order, are these:
  - the forward linked call with host trampolines (`LinkedSessionFwd` with
    `CalloutRun.runs_callout` at host trampolines). Its invariants (`LStat`, `ReadyL`, `gL`)
    assume the component functions are the exporter's then the importer's lifted functions, and
    every trampoline of the importer lowers an exporter function: they have to be restated over
    `afterLinkH` (the host functions first, trampolines of `l.fid`), with a host segment per
    host call answered by `answerHostS P (logG g)`;
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

end Silmaril.Wasm.Component.Reference

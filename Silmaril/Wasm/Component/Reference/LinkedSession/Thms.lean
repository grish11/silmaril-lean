module

public import Silmaril.Wasm.Component.Reference.LinkedSession.Defs
public import Silmaril.Wasm.Component.RefValid.Defs
import Silmaril.Proofs.Wasm.Component.Reference.LinkedSession.Main

/-!
# A bounded linked fixture for resumable sessions: theorems

Operational facts of the concrete two-module fixture `linkedC` (module A with the global `g`,
its `set` writing `g := 1` and then trapping, and its `get`; module B calling them from `poke`
and `peek`) and of its variant `linkedHRef` with the host import `h` called by `ping`. This is a
**concrete reference fixture, not a general linked adequacy theorem**: the general composition
adequacy waits on the composition closure of `DStrategy` (asked on #207).

All facts are about the reference machine over `core3 neverFail` with the first-alternative
oracle `first` (component choice profile `first.prof`); each is a closed computation of the
copied validator and drivers (`decide +kernel`), read back as a reference behaviour through
the soundness of the drivers (`callTop_sound`, `instantiateRun_mem`). Session outcomes use the
resumable session (`resumeCfg`: a trap aborts the current export call, the Core store
persists, and the next export call runs from it).

* **Validity and instantiation** (`linkedC_valid`, `linkedHRef_valid`, `linkedC_instantiates`,
  `linkedH_instantiates`): the validator accepts both components, and both instantiate on the
  reference machine.
* **`poke` traps** (`linkedC_poke_traps`): the session of the single call `poke` has the
  outcome `trap`. The trap is a core trap (`linkedC_poke_coreTrap`: the only trap label of the
  run is `coreTrap`); B's core code (`call 0`, `call 1`) cannot trap and the lift and lower of
  `func()` do not trap, so it is A's `unreachable`, reached through B's `canon lower` of `set`
  and A's `canon lift`, and it aborts the whole export call.
* **Store persistence across the callee trap** (`linkedC_session`): the session `poke, peek` has
  the outcomes `[trap, some [1]]`: A's write `g := 1` before its trap persists into the next
  export call, while `peek` on a fresh instance answers `0` (`linkedC_peek_fresh`).
* **The internal call is not a host callout**: with the counting host `countG`, the session
  `poke, peek` of `linkedHRef` ends in host state `0` (`linkedH_noCallout`), and `ping` makes
  exactly one host callout (`linkedH_ping_callout`, host state `1`; `linkedH_session` for the
  three calls in a row).
* **A host that never answers** (`embSilent`, which takes the call and never resolves it):
  `ping` traps and the session `poke, peek, ping` has outcomes `[trap, some [1], trap]`
  (`linkedH_silent_session`). The trap is REF's `cannotBlockSync` (`linkedH_silent_cannotBlock`;
  `canon_lift`'s synchronous loop, `trap_if(not candidates)`): a synchronous export cannot wait
  for the host. So the host's silence is a real observation, but on this synchronous fixture it
  is a trap, not a pending (host-divergent) call; a pending observation needs an asynchronous
  lift or lower, outside the `SimpleI` fragment.

Not claimed: other profiles (`core3P P` for every `P`, as `witness_session` has for `Simple`) and
the uniqueness of these outcomes; the IR side (the play `poke · trap · peek · 1` in
`linkedC.toComp.den (impSem P)`), which needs `Linked2.ExpRun` to allow an exporter trap that is
not the last import call (its `trap` constructor ends the run) with the trapped store threaded
on, and the importer rounds whose import call answers `none`; the parser from bytes to these
components, and F6.

Proofs: `Silmaril.Proofs.Wasm.Component.Reference.LinkedSession.Main`.
-/

public section

namespace Silmaril.Wasm.Component.Reference.LinkedSession

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine

/-! ## Validity and instantiation -/

/-- The validator accepts `linkedC` (proved). -/
theorem linkedC_valid : ∃ ct, check? Features.p2 linkedC.toRef = .ok ct :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSession.linkedC_valid

/-- The validator accepts `linkedHRef` (proved). -/
theorem linkedHRef_valid : ∃ ct, check? Features.p2 linkedHRef = .ok ct :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSession.linkedHRef_valid

/-- **`linkedC` instantiates on the reference machine** from the empty store (proved). -/
theorem linkedC_instantiates : ∃ m inst es, InstResult.instance m inst es ∈
    instBehaviours first.prof (Host.ofEmbedder embCount) (initConfig 0) linkedC.toRef [] :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSession.inst_of_sessRun
    Silmaril.Proofs.Wasm.Component.Reference.LinkedSession.linkedC_peek_run

/-- **`linkedHRef` instantiates on the reference machine** from the store of the host function
`h` (proved). -/
theorem linkedH_instantiates : ∃ m inst es, InstResult.instance m inst es ∈
    instBehaviours first.prof (Host.ofEmbedder embCount) (hostConfig hostIface 0) linkedHRef
      (importArgs hostIface) :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSession.inst_of_sessRun
    Silmaril.Proofs.Wasm.Component.Reference.LinkedSession.linkedH_ping_run

/-! ## The callee trap and store persistence -/

/-- **`poke` traps** (proved): the export call `poke` ends in a trap. -/
theorem linkedC_poke_traps :
    [none] ∈ sessBehaviours first.prof (Host.ofEmbedder embCount) 0 linkedC.toRef
      [("poke", [])] :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSession.sessBehaviours_of_run
    Silmaril.Proofs.Wasm.Component.Reference.LinkedSession.linkedC_poke_run

/-- **The trap of `poke` is a core trap** (proved): the only trap label of the run of `poke` is
`coreTrap`. -/
theorem linkedC_poke_coreTrap :
    callTraps embCount first 400 linkedC.toRef [] 0 "poke" [] = some [.coreTrap] :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSession.linkedC_poke_traps

/-- **Store persistence across the callee trap** (proved): in the resumable session, `poke`
traps and the following `peek` answers `1`. -/
theorem linkedC_session :
    [none, some [toRefVal (.u32 1)]] ∈ sessBehaviours first.prof (Host.ofEmbedder embCount) 0
      linkedC.toRef [("poke", []), ("peek", [])] :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSession.sessBehaviours_of_run
    Silmaril.Proofs.Wasm.Component.Reference.LinkedSession.linkedC_pokePeek_run

/-- `peek` on a fresh instance answers `0` (proved). -/
theorem linkedC_peek_fresh :
    [some [toRefVal (.u32 0)]] ∈ sessBehaviours first.prof (Host.ofEmbedder embCount) 0
      linkedC.toRef [("peek", [])] :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSession.sessBehaviours_of_run
    Silmaril.Proofs.Wasm.Component.Reference.LinkedSession.linkedC_peek_run

/-! ## Host callouts -/

/-- **No host callout for `poke` and `peek`** (proved): with the counting host, the session
`poke, peek` of `linkedHRef` answers `trap, 1` and ends in host state `0`. -/
theorem linkedH_noCallout :
    ([none, some [toRefVal (.u32 1)]], 0) ∈ sessRunBehaviours first.prof
      (Host.ofEmbedder embCount) 0 linkedHRef hostIface [("poke", []), ("peek", [])] :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSession.linkedH_pokePeek_run

/-- **`ping` makes exactly one host callout** (proved): it returns, and the counting host ends
in state `1`. -/
theorem linkedH_ping_callout :
    ([some []], 1) ∈ sessRunBehaviours first.prof (Host.ofEmbedder embCount) 0 linkedHRef
      hostIface [("ping", [])] :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSession.linkedH_ping_run

/-- The session `poke, peek, ping` of `linkedHRef` with the counting host (proved). -/
theorem linkedH_session :
    ([none, some [toRefVal (.u32 1)], some []], 1) ∈ sessRunBehaviours first.prof
      (Host.ofEmbedder embCount) 0 linkedHRef hostIface [("poke", []), ("peek", []), ("ping", [])] :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSession.linkedH_all_run

/-- **A host that never answers** (proved): the session `poke, peek, ping` answers
`trap, 1, trap`. -/
theorem linkedH_silent_session :
    ([none, some [toRefVal (.u32 1)], none], 0) ∈ sessRunBehaviours first.prof
      (Host.ofEmbedder embSilent) 0 linkedHRef hostIface [("poke", []), ("peek", []), ("ping", [])] :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSession.linkedH_silent_run

/-- **The trap of `ping` under the silent host is `cannotBlockSync`** (proved). -/
theorem linkedH_silent_cannotBlock :
    callTraps embSilent first 400 linkedHRef hostIface 0 "ping" [] = some [.cannotBlockSync] :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSession.linkedH_silent_ping_traps

end Silmaril.Wasm.Component.Reference.LinkedSession

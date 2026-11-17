module

public import Silmaril.Wasm.Component.Reference.LinkedGImp.Defs
import Silmaril.Proofs.Wasm.Component.Reference.LinkedGRef.NestExt
import Silmaril.Proofs.Wasm.Component.Reference.LinkedGImp.Call

/-!
# An import call answered by an abstract exporter: theorems

**Scope.** Every profile `P`; the reference machine over `core3P P` (under `linkHost impl`, any
host state type and host functions); an exporter given by reference data `d` meeting R1
(`Frame`), R2 (`Fwd`) and R6 (`Bounded`) at a placement `pl`; an importer at the invariant
`LInvG` of `LinkedGImp`.

**Proved (proof-internal, in `Proofs.….LinkedGRef.NestExt`): the return half of a nested call
from an extended store.** `nest_atX` is `nest_atG` with

* the return half (and the trap of the result lift) starting from **any** store `S'` that keeps
  the callee's records at their indices (`CalleeAt`: the arenas of the callee's store are
  prefixes of those of `S'`, its instance state unchanged, `S'` not locked down) and **any**
  continuation slots `C'`; the records are looked up by index (`runs_returnI`, `runs_exitI`,
  `runs_callUnit_loopI`), and the caller resumes at `retStoreG S' …` (`S'` with the call's
  records written at their indices and the callee's thread table reset), with the slots `C'`;
* the callee's store (`nstoreCoreG …`), thread (`⟨M.store.threads.length⟩`) and instance
  (`instOfThread?`) exposed.

`nest_atG_of_X` proves `nest_atG`'s statement from `nest_atX` (at `S' = { M₁.store with core :=
y.1 }`, `C' = M₁.conts`), so the fixed-frame return is an instance. The read-back is `LRun.inv`
of the runs of `nest_atX` and `trapsAtSH_back` of its trap.

**Proved (proof-internal, in `Proofs.….LinkedGImp.Call`): one import call of the importer
answered by the exporter.** For an importer at `LInvG d pl … s M.store F y x` whose part stops at
a callout to import `k`, wired to the `canon lower` (instance `ii`) of the lifted export `w` of
the exporter, the export instance's thread table reusable (`ThreadsOk`):

* `call_ret`: for a step `e.Step P s ⟨(w, .vals ws), some (.vals us)⟩ s'` on the lifted
  arguments, the machine runs without host events or `internal` traps to the importer's core
  activation resumed with the lowering of `us`, at a store `S''` and slots `C'` with
  `LInvG d pl … s' S'' F' …` again (from `nest_atX`, R1, R2, R6 and `LInvG.resume_fwd`); `S''`
  only grows the arenas of `M.store`, keeps every instance outside the exporter's block and the
  rest of the component store (`CallExt`), and keeps the thread tables of the export instances
  reusable. These are the store facts from which the next call's hypotheses are re-established
  (the importer's thread and task records by the prefixes, `ii`'s state when `ii` is outside the
  block); that re-establishment is not stated here;
* `call_trap`: for a trapping step (`R = none`), the machine traps (lockdown) without host
  events or `internal` traps, the exporter's relation holding `s'` at the trapped core store.

**On strengthening R2's `Ends` (the remaining mismatch recorded in `LinkedGImp.Thms`).** Not
needed for these runs, and no counterexample exists along them: `call_ret` and `call_trap` use
R2's `Ends` exactly as stated (`ExpSpec.RefAdeqB` suffices). The continuation slots `C'` that
`Ends` leaves free are never read on the path of a nested call or its return: the machine reads
`conts` only in `resumeThread` and `block`/`blockSwitch`, and the nested call's `resumeThread`
reads the slot its own `newThread` has just written (`Config.cont?_setCont_self`), so `C'` is
carried unchanged to the caller's resumed frame. `Ends`'s `StoreExt` gives `CalleeAt`: R2
appends records after the callee's, keeps the export instances and changes no other field, so
the callee's records stay at their indices and the return reads them there.

**Not claimed** (what remains):

* **`LinkedG.linkCall_fwd`/`linkCall_inv` as one session round**: the importer's export call
  from the host (`invokeProg`, the importer's `canon lift`) to its resolution, iterating
  `call_ret` along the importer's part (`LInvG.reach_fwd` between calls), with the importer's
  machine invariants (`CallAtLKTS`/`ReadyL` of `Linked2`) restated for `LInvG` at an arbitrary
  placement, and the arguments that do not lift (`nest_trap_argsG`).
* **The read-back of one call** (`linkCall_inv`'s step) from R3. R3's middle case lets a run
  pass through `Ends`' trapped branch (a locked-down configuration) with a non-empty control
  chain and continue; the read-back of the importer then needs either a machine lemma that a
  locked-down store stays locked with its core store fixed along such runs, or `Ends`' trapped
  branch to require an empty control chain (which a `Simple` exporter meets, its trapped
  configuration being `trapCfg _`). Neither is proved here.
* `LinkedG.sess_specToRef`, `sess_refToSpec`, `sessObs_eq` with `Linked2` as an instance,
  `LinkedG.toExp_refAdeq` and `LinkedN.sessAdequacy_full`: they rest on the previous items.
-/

module

public import Silmaril.Wasm.Component.Reference.LinkedGInv.Defs
import Silmaril.Proofs.Wasm.Component.Reference.LinkedGInv.Sess

/-!
# The read-back of a linked call through an abstract exporter: theorems

**Scope.** Every profile `P` and component choice profile; the reference machine over `core3P P`
under `linkHost impl` (any host state type and host functions); a `LinkedG` whose exporter is
given by reference data `d` at a placement `pl`, meeting R1 (`Frame`), R3 as corrected in `Defs`
(`BwdF`), R5 (`Resume`) and R6 (`Bounded`); the importer at an instance index `ii` outside the
exporter's block, with the static facts `StatB` of `LinkedGRound`.

**Proved (public, below).**

* `ExpSpec.RefData.BwdF.bwdT`, `ExpSpec.RefAdeqF.refAdeqS`: the corrected trapped case implies
  the corrected R3 of `LinkedGRound`, so `RefAdeqF` implies `RefAdeqS` of `LinkedGInit`.
* `Simple.expSpec_refAdeqF`: a simple exporter meets `RefAdeqF`, under the hypotheses of
  `Simple.expSpec_refAdeqS` (its trapped runs end in `trapCfg` of its core activation, inside its
  part).

**Proved (proof-internal, in `Proofs.….LinkedGInv`): the read-back of linked calls and sessions
from between calls.**

* `first_stop`, `tick_back` (`Imp`): a run to a configuration that is not live passes, without
  host events, through a first such configuration; a tick from a configuration ready for the host
  with no waiting thread returns to it;
* `linvG_reach_back`, `linvG_callout_back` (`Imp`): `LInvG` backward (`reach_link_back`, R1);
* `call_backB` (`Step`): **one import call read back** through R3 (`BwdF`) and the return half of
  `nest_atX` (`trapsAtSH_back` for results that do not lift): a returning step of the exporter on
  the lifted arguments resumes the importer with `LInvG`, its frame and `CallExt`; otherwise the
  run ends locked down at a trapped step, the parts related at the trapped core store;
* `phase_backB` (`Phase`): **the importer's core activation read back** (`lsegs_inv` and
  `lseg_path` of `Linked2` against `LInvG`): every host-free run to a configuration that is not
  live is a round of the importer's instance whose component import calls (`ImpRel`) are an
  `ExpRun` of the exporter, ending at the importer's exit from its core activation or locked down
  with the round answering a trap (arguments that do not lift: `nest_trap_args_backG`);
* `linkCall_invB` (`Call`): **every terminating top-level call of a typed export call from a
  configuration between calls (`ReadyB`, no waiting thread) is a `LinkedG.SessSpec` round**: a
  resolved call answers the round's results with `ReadyB` at its end (and no new waiting thread),
  a trapped call answers a trap with `ReadyB` at its `resumeCfg`; cancelled and deadlocked
  outcomes do not occur;
* `sessL_invB`, `sessL_iffB` (`Sess`): every resumable session of typed calls from such a
  configuration is the reference image of a `LinkedG.SessSpec` session from its stores, and with
  `sessL_fwdB` of `LinkedGRound` the session outcomes from it are exactly those images.

**Deviations from the plan of `LinkedGInit`.**

* **R3's trapped case is too weak for the read-back** (`Defs`): it gives no footprint discipline
  at the trapped core store (so the importer's store cannot be related to it) and allows a
  locked-down end with a non-empty control chain. The read-back uses `BwdF`; a simple exporter
  meets it.
* **Waiting threads**: `ReadyB` does not record the store's waiting threads, and `Calls` allows
  ticks after the call resolved; a tick resumes the ready waiting threads. The read-back assumes
  no waiting thread between calls and shows that a call keeps it so.

**Not claimed** (what remains):

* **`LinkedG.sess_refToSpecB` from instantiation**, hence `LinkedG.sessObs_eqB` and
  `LinkedG.sessAdequacy_fullB`. `LinkedG.sessObs` quantifies over **every** instantiation run of
  `lg.toRef`, while R4 (`RefData.InitS`) gives **one** run of the exporter's nested
  instantiation, and the parent's stages (`instG_run`) are proved as existential `Reach`es. The
  read-back needs an R4 read-back (every host-free run of the nested instantiation reaches an
  `InitAt` end, or the instantiation result is unique) with the parent's stages inverted, and
  `InitAt` keeping the waiting threads (it says nothing of them, so even `readyB_init`'s
  configuration is not known to have none).
* **`Linked2` as an instance** of those, which rests on them.
-/

public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)

/-- **The corrected trapped case implies the corrected R3** (proved). -/
theorem ExpSpec.RefData.BwdF.bwdT {P : Profile} {e : ExpSpec} {d : e.RefData P} (h : d.BwdF) :
    d.BwdT :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGInv.bwdF_bwdT h

/-- **`RefAdeqF` implies `RefAdeqS`** (proved). -/
theorem ExpSpec.RefAdeqF.refAdeqS {P : Profile} {e : ExpSpec} (h : e.RefAdeqF P) :
    e.RefAdeqS P :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGInv.refAdeqF_refAdeqS h

/-- **A simple exporter meets `RefAdeqF`** (proved, every profile), under the hypotheses of
`Simple.expSpec_refAdeqS`. -/
theorem Simple.expSpec_refAdeqF (P : Profile) {c : Simple} (hc : c.Good) (hi : c.Inst)
    {I : Silmaril.Wasm.Game.ScalarInstance} (hI : c.mod.IsInst I)
    (hS : Linked2.ModSplitOk c.mod.mod) (hN : ∀ x ∈ c.exports, ∀ n, x.name ≠ tag "t" n) :
    (Simple.expSpec c I).RefAdeqF P :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGInv.simple_refAdeqF P hc hi hI hS hN

end Silmaril.Wasm.Component.Reference

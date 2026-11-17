module

public import Silmaril.Wasm.Component.Reference.HLinkedSessionDiv.Defs
import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionDiv.Inv

/-!
# Diverging calls of linked sessions with host imports: theorems

**Scope.** `HLinked2` (`HLinkedSession.Defs`): the import-free exporter A answers the wired
imports of the importer B, and B's remaining imports are host imports of the parent, passed
through. Every profile `P` and component choice profile `prof`; the reference component is
`l.toRef` on `core3P P` under the logging host `answerHostS P (logG g)` from `(s₀, [])`, the
observations of the finite adequacy (`HLinked2.sessObs`, #758–#782).

**Hypotheses.** `HLinked2.Adequate` and a typed host `HLinked2.HostTyped g`, the hypotheses of
`HLinked2.sess_specToRef`. The typed host is needed for the session prefix and for the divergent
call's own host calls: an ill-typed host answer is an `internal` fault of the reference machine,
not a trap, and the specification would continue past it (`HLinkedSession.Thms`). The typing
hypotheses on the calls are not needed: `DivRound.Ok` checks the arguments.

## Proved

* **Specification divergence is reference divergence, with the host log**
  (`HLinked2.divSpecToRef`): `HLinked2.DivSpecToRef P prof l g`, i.e.
  `HLinked2.sessDivs P l g s₀ calls j vs ⊆ HLinked2.refDivs P prof l g s₀ calls j vs`. After a
  specification session whose host calls are answered by `logG g` from `(s₀, [])`, a round of
  export `j` on `vs` that makes some host calls, each answered by `logG g`, and then diverges
  internally (B host-free, A inside a wired call, or wired chatter) is, on the reference machine,
  a resumable session with the same outcomes followed by a top-level call that diverges quietly
  in the same host state and log (`CallQuietDiverges`): after the invocation and a finite run
  without host events, the machine runs forever without host events, returning to that host state
  and log at unboundedly late points.

How (`Proofs.….HLinkedSessionDiv.{Round, Call, Main}`): the session prefix is #782's forward run
(`sessH_fwd`, `resumeCfg` after a trapped call). The round's prefix is a prefix variant of
`rounds_fwdH` (`roundsPre_fwdH`): each wired call is a nested `canon lower`/`canon lift` into A
(`nest_retG`, now also nonempty), each host call is the host's answer (`HostHandles`, as
`handles_answer` gives it for `answerImplS`), which moves the host state along the `HostRun`; an
import call answered by a trap dooms B's thread, after which no source applies. Then:

* **(i)** B's infinite host-free run is an infinite core run of the shared thread (`link_inf` at
  `gL P l.toW`), one machine step per core step, the host state fixed;
* **(ii)** the nested call into A runs quietly to A's activation in the same host state
  (`nest_atTSH`), and A's infinite run is an infinite core run there;
* **(iii)** every served wired call is a nonempty quiet run back to B's core activation in the same
  host state (no host call: `expRunT_toH`), concatenated by `quietDiverges_of_segs`.

* **Reference divergence is specification divergence, with the host log**
  (`HLinked2.divRefToSpec`): `HLinked2.DivRefToSpec P prof l g`, i.e. `refDivs ⊆ sessDivs` for
  typed calls. Hence **the two agree** (`HLinked2.sessDivs_eq_refDivs`), and
  **`HLinked2.RefSessEquivD.iff_sessDivs`**: the reference-defined equivalence with quiet
  divergence and the host log (`RefSessEquivD`) is the session equivalence `RefSessEquivH`
  together with the same specification divergences under every typed host.

How (`Proofs.….HLinkedSessionDiv.{Trace, Back, Classify, Inv}`): the session prefix is inverted
by `sessH_inv` (which ends between calls, `ReadyL`); the configuration reached is host-safe for
the logging host (`HLinked2.logSession_cfgSafe`, `HostWrite`). The divergent call is the
invocation and an explicit infinite run on which the host state `st` occurs unboundedly late
(`callQuiet_irun`). Its rounds are classified along that run (`ldiv_roundH`): B host-free, A in a
wired call, or one served import call (a nested call of A, or a host call answered by the host)
to a later position. By `HLinked2.logSteps_mono` the log only grows along the run, strictly at
each answered host call: infinitely many host calls would make the log of every later round
longer than that of `st`, which follows them on the run; after the last one, a configuration in
`st` lies between two rounds in the same host state, so `st` is it (`ldiv_classifyH`).

## Not claimed (what remains)

* **Host divergence** (`HLinked2.hostDivs`: the round blocked on a pending host call that the host
  never answers) is defined and kept separate from `sessDivs`. Under synchronous lowering it is a
  trap of the reference machine, not a divergence: for a host that never answers this is
  `HLinked2.silent_cannotBlock_sess` (a round with a host call traps `cannotBlockSync`). A host
  that answers some calls and leaves others pending (a mixed `answerImplS`/`silentImpl`), and
  hence the general statement for `hostDivs`, is not covered. Asynchronous lowering or lifting,
  where the call would stay pending, is out of scope.
* **Infinitely many host calls** are an infinite play of the host interface, not a divergence; they
  are in neither set. `HLinked2` infinite plays, and divergence against the IR
  (`l.toComp.denUD`), are later steps of the ledger row.
-/

public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component.Runtime (HostFuncId)

/-- **Specification divergence of a linked session with host imports is reference divergence,
with the host log** (proved, every profile and component choice profile, under
`HLinked2.Adequate` and a typed host): every internal divergence of the specification after a
session and the divergent call's own host calls (`sessDivs`: B diverges host-free, A diverges
inside a wired call, or wired chatter) is a quiet divergence of the reference machine in the same
host state and log (`refDivs`). -/
theorem HLinked2.divSpecToRef (P : Profile) (prof : ProfileKind) {l : HLinked2}
    (hl : l.Adequate) {σ : Type}
    (g : σ → HostFuncId → List Silmaril.Wasm.Component.Value.Val →
      Option (List Silmaril.Wasm.Component.Value.Val × σ))
    (hT : l.HostTyped g) : HLinked2.DivSpecToRef P prof l g :=
  Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionDiv.hlinked2_divSpecToRef P prof hl g hT

/-- **Reference divergence of a linked session with host imports is specification divergence,
with the host log** (proved, every profile and component choice profile, under
`HLinked2.Adequate` and a typed host, typed calls): every quiet divergence of the reference
machine after a session (`refDivs`) is an internal divergence of the specification after the same
session and host log (`sessDivs`). -/
theorem HLinked2.divRefToSpec (P : Profile) (prof : ProfileKind) {l : HLinked2}
    (hl : l.Adequate) {σ : Type}
    (g : σ → HostFuncId → List Silmaril.Wasm.Component.Value.Val →
      Option (List Silmaril.Wasm.Component.Value.Val × σ))
    (hT : l.HostTyped g) : HLinked2.DivRefToSpec P prof l g :=
  Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionDiv.hlinked2_divRefToSpec P prof hl g hT

/-- **The diverging session calls of a linked component with host imports, with the host log,
are those of the reference machine** (proved, typed calls, typed host). -/
theorem HLinked2.sessDivs_eq_refDivs (P : Profile) (prof : ProfileKind) {l : HLinked2}
    (hl : l.Adequate) {σ : Type}
    (g : σ → HostFuncId → List Silmaril.Wasm.Component.Value.Val →
      Option (List Silmaril.Wasm.Component.Value.Val × σ))
    (hT : l.HostTyped g) (s₀ : σ) (calls : List (Fin l.imp.exports.length × List Silmaril.Wasm.Component.Val))
    (j : Fin l.imp.exports.length) (vs : List Silmaril.Wasm.Component.Val) (ht : SimpleI.TypedCalls l.imp calls)
    (hvs : ValTy.checkList l.imp.exports[j].ty.params vs = true) :
    HLinked2.sessDivs P l g s₀ calls j vs = HLinked2.refDivs P prof l g s₀ calls j vs :=
  Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionDiv.hlinked2_sessDivs_eq_refDivs P prof
    hl g hT s₀ calls j vs ht hvs

/-- **`RefSessEquivD` with the divergence clause on the specification** (proved): for adequate
linked components with host imports, the reference-defined equivalence with quiet divergence and
the host log is `RefSessEquivH` together with the same specification divergences under every
typed host. -/
theorem HLinked2.RefSessEquivD.iff_sessDivs {P : Profile} {prof : ProfileKind} {l l' : HLinked2}
    (hl : l.Adequate) (hl' : l'.Adequate) :
    HLinked2.RefSessEquivD P prof l l' ↔ ∃ h : HLinked2.RefSessEquivH P prof l l',
      ∀ (calls : List (Fin l.imp.exports.length × List Silmaril.Wasm.Component.Val)) (j : Fin l.imp.exports.length)
        (vs : List Silmaril.Wasm.Component.Val), SimpleI.TypedCalls l.imp calls →
        ValTy.checkList l.imp.exports[j].ty.params vs = true →
        ∀ {σ : Type} (g : σ → HostFuncId → List Silmaril.Wasm.Component.Value.Val →
          Option (List Silmaril.Wasm.Component.Value.Val × σ)), l.HostTyped g →
          ∀ s₀ : σ, HLinked2.sessDivs P l g s₀ calls j vs =
            HLinked2.sessDivs P l' g s₀
              (Linked2.castCalls (l := l.toL2) (l' := l'.toL2) h.len calls)
              (Fin.cast h.len j) vs :=
  Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionDiv.hlinked2_refSessEquivD_iff hl hl'

end Silmaril.Wasm.Component.Reference

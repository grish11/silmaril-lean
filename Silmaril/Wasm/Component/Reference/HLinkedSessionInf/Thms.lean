module

public import Silmaril.Wasm.Component.Reference.HLinkedSessionInf.Defs
import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionInf.Main

/-!
# Infinite plays of linked sessions with host imports: theorems

**Scope.** `HLinked2` (`HLinkedSession.Defs`): the import-free exporter A answers the wired
imports of the importer B, and B's remaining imports are host imports of the parent, passed
through. Every profile `P` and component choice profile `prof`; the reference component is
`l.toRef` on `core3P P` under the logging host `answerHostS P (logG g)` from `(s₀, [])`, the
resumable session (`resumeCfg` after a trap, the store persists, no poisoning).

**Hypotheses.** `HLinked2.Adequate` and a typed host `HLinked2.HostTyped g` (as for
`HLinked2.sess_specToRef` and `HLinked2.divSpecToRef`), typed calls for the reference-to-
specification directions. No determinism: every statement holds at every profile `P`.

## Proved

* **Infinitely many terminating calls** (`HLinked2.refSessProd_iff`): a productive execution of
  the reference machine (`HLinked2.RefSessProd`: one explicit stream of reference configurations,
  with the host-state stream `hst`) is exactly an infinite specification session
  (`HLinked2.SpecSessProd`: one stream of stores of A and B, each call a one-round
  `HLinked2.SessSpec`, its host calls a `HostRun` of the logging host from `hst k` to
  `hst (k + 1)`) from the instances' stores with `hst 0 = (s₀, [])`. Forward one call at a time
  (`sessH_fwd` on a one-call session, `ReadyL` between calls, `resumeCfg` after a trap, dependent
  choice), backward one call at a time along the given stream (`sessH_inv`).
* **A call with infinitely many host calls** (`HLinked2.sessHProds_eq_refHProds`): the host-chatter
  plays of the reference machine (`HLinked2.refHProds`: after the session, the invocation and one
  explicit infinite run of internal steps whose logs are, unboundedly late, the call's log followed
  by unboundedly long prefixes of `ev`) are those of the specification (`HLinked2.sessHProds`:
  after a `SessSpec` session, an `HLinked2.RoundInf` of the logging host whose round logs are,
  unboundedly late, the call's log followed by unboundedly long prefixes of `ev`).
  Forward: each served import call is a run without host events between core activations
  (`roundsPre_fwdH` one call at a time), the runs are made into one explicit infinite run
  (`segs_compress`, `irun_of_segs`); the round's host state changes infinitely often because its
  logs are unbounded and only grow. Backward: the rounds of the call are classified along the
  explicit run (`ldiv_roundH`): B diverging host-free or A diverging inside a wired call would fix
  the host state from some position on, against the unbounded log, so every round is a served
  import call (dependent choice); the logs of the rounds are prefixes of later logs of the run and
  extend earlier ones (`HLinked2.logSteps_mono`), hence of the form required.
* **The full equivalence on the specification** (`HLinked2.RefSessEquivFull.iff_spec`): the
  reference-defined `HLinked2.RefSessEquivFull` (terminating outcomes with the host log, quiet
  divergences, productive executions with their host-state streams, host-chatter plays) is
  `HLinked2.RefSessEquivH` together with the same specification divergences
  (`HLinked2.sessDivs`), host-chatter plays (`HLinked2.sessHProds`) and infinite sessions
  (`HLinked2.SpecSessProd`), under every typed host.

## Not claimed (what remains)

* **A canonical session object and the injection.** No `HLinked2.compSession` through the H2
  owner's `threadS` is defined here, and there is no `compSession_inj_full`. Two points are open:
  the store-retaining triple must have the host calls as visible lower moves and host chatter as
  its productive streams; and the session object answers host calls with any payload, while
  `RefSessEquivFull` quantifies over typed hosts only, so the injection needs either a session
  object restricted to typed host answers or a proof that ill-typed answers are handled alike.
* **Nondeterministic profiles for the session object**: the statements here hold at every profile
  because they relate one reference run to one specification run; an injection into a
  `threadS` object needs store determinism of the triple (at `profile o`, as for `Linked2`), and
  König's lemma beyond it.
* Host divergence (`HLinked2.hostDivs`) for a host that answers some calls and blocks on others,
  divergence against the IR (`l.toComp.denUD`), and asynchronous lowering or lifting.
-/

public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component.Runtime (HostFuncId)
open Silmaril.Games.Abstract (streamTake)

local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "RVal" => Silmaril.Wasm.Component.Value.Val

/-- **Productive executions are infinite specification sessions** (proved, every profile and
component choice profile, `HLinked2.Adequate`, typed host, typed calls): a productive execution of
the reference machine with the host-state stream `hst` is an infinite specification session from
the instances' stores whose host calls the logging host answers along `hst`, from
`hst 0 = (s₀, [])`, and conversely. -/
theorem HLinked2.refSessProd_iff (P : Profile) (prof : ProfileKind) {l : HLinked2}
    (hl : l.Adequate) {σ : Type} (g : σ → HostFuncId → List RVal → Option (List RVal × σ))
    (hT : l.HostTyped g) (s₀ : σ) (a : ℕ → Fin l.imp.exports.length × List IVal)
    (out : ℕ → Option (List IVal))
    (ht : ∀ k, ValTy.checkList l.imp.exports[(a k).1].ty.params (a k).2 = true)
    (hst : ℕ → σ × List HLinked2.HostEvent) :
    HLinked2.RefSessProd P prof l g s₀ a out hst ↔
      hst 0 = (s₀, []) ∧ ∃ Ie Ii : Silmaril.Wasm.Game.ScalarInstance,
        l.exp.mod.IsInst Ie ∧ l.imp.mod.IsInst Ii ∧
        HLinked2.SpecSessProd P l Ie Ii (HLinked2.logG g) a out hst :=
  Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionInf.hlinked2_refSessProd_iff P prof hl
    g hT s₀ a out ht hst

/-- **The host-chatter plays of a linked component with host imports are those of the reference
machine** (proved, every profile and component choice profile, `HLinked2.Adequate`, typed host,
typed calls): after a session, a call making infinitely many host calls, with the session's
outcomes, the host state and log at the call and the call's host events. -/
theorem HLinked2.sessHProds_eq_refHProds (P : Profile) (prof : ProfileKind) {l : HLinked2}
    (hl : l.Adequate) {σ : Type} (g : σ → HostFuncId → List RVal → Option (List RVal × σ))
    (hT : l.HostTyped g) (s₀ : σ) (calls : List (Fin l.imp.exports.length × List IVal))
    (j : Fin l.imp.exports.length) (vs : List IVal) (ht : SimpleI.TypedCalls l.imp calls)
    (hvs : ValTy.checkList l.imp.exports[j].ty.params vs = true) :
    HLinked2.sessHProds P l g s₀ calls j vs = HLinked2.refHProds P prof l g s₀ calls j vs :=
  Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionInf.hlinked2_sessHProds_eq_refHProds P
    prof hl g hT s₀ calls j vs ht hvs

/-- **The full equivalence with its clauses on the specification** (proved, every profile and
component choice profile): for adequate linked components with host imports, the
reference-defined `RefSessEquivFull` is `RefSessEquivH` with, under every typed host, the same
specification divergences and host-chatter plays after typed sessions, and the same infinite
specification sessions of typed streams of calls with their host-state streams. -/
theorem HLinked2.RefSessEquivFull.iff_spec {P : Profile} {prof : ProfileKind} {l l' : HLinked2}
    (hl : l.Adequate) (hl' : l'.Adequate) :
    HLinked2.RefSessEquivFull P prof l l' ↔ ∃ h : HLinked2.RefSessEquivH P prof l l',
      (∀ (calls : List (Fin l.imp.exports.length × List IVal)) (j : Fin l.imp.exports.length)
        (vs : List IVal), SimpleI.TypedCalls l.imp calls →
        ValTy.checkList l.imp.exports[j].ty.params vs = true →
        ∀ {σ : Type} (g : σ → HostFuncId → List RVal → Option (List RVal × σ)), l.HostTyped g →
          ∀ s₀ : σ, HLinked2.sessDivs P l g s₀ calls j vs =
              HLinked2.sessDivs P l' g s₀
                (Linked2.castCalls (l := l.toL2) (l' := l'.toL2) h.len calls)
                (Fin.cast h.len j) vs ∧
            HLinked2.sessHProds P l g s₀ calls j vs =
              HLinked2.sessHProds P l' g s₀
                (Linked2.castCalls (l := l.toL2) (l' := l'.toL2) h.len calls)
                (Fin.cast h.len j) vs) ∧
      ∀ (a : ℕ → Fin l.imp.exports.length × List IVal) (out : ℕ → Option (List IVal)),
        (∀ k, ValTy.checkList l.imp.exports[(a k).1].ty.params (a k).2 = true) →
        ∀ {σ : Type} (g : σ → HostFuncId → List RVal → Option (List RVal × σ)), l.HostTyped g →
          ∀ (s₀ : σ) (hst : ℕ → σ × List HLinked2.HostEvent),
            ((hst 0 = (s₀, []) ∧ ∃ Ie Ii : Silmaril.Wasm.Game.ScalarInstance,
                l.exp.mod.IsInst Ie ∧ l.imp.mod.IsInst Ii ∧
                HLinked2.SpecSessProd P l Ie Ii (HLinked2.logG g) a out hst) ↔
              (hst 0 = (s₀, []) ∧ ∃ Ie Ii : Silmaril.Wasm.Game.ScalarInstance,
                l'.exp.mod.IsInst Ie ∧ l'.imp.mod.IsInst Ii ∧
                HLinked2.SpecSessProd P l' Ie Ii (HLinked2.logG g)
                  (Linked2.castStream (l := l.toL2) (l' := l'.toL2) h.len a) out hst)) :=
  Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionInf.hlinked2_refSessEquivFull_iff hl hl'

end Silmaril.Wasm.Component.Reference

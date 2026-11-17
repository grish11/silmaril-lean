module

public import Silmaril.Wasm.Component.Reference.HLinkedSession.Defs
public import Silmaril.Wasm.Component.Reference.LinkedSessionDiv.Defs
public import Silmaril.Wasm.Component.Reference.LinkedSessionEquiv.Defs

/-!
# Diverging calls of linked sessions with host imports: definitions

**Scope.** `HLinked2` (`HLinkedSession.Defs`): the import-free exporter A (`l.exp`) answers the
wired imports of the importer B (`l.imp`), and B's remaining imports are host imports of the
parent, passed through. The sessions are those of the finite adequacy (#758–#782):
`HLinked2.SessSpec` on the specification and the resumable sessions of `l.toRef` under the
logging host `answerHostS P (logG g)` on the reference machine (`sessObs`). This is the
`HLinked2` counterpart of `Linked2`'s `LinkedSessionDiv` (#730), with the host calls observable.

## What a divergent call observes

With host imports a top-level call that never answers can be in one of three situations, and
the definitions below keep them apart.

* **Internal divergence after a call log.** The call makes finitely many host calls, each
  answered by the host and logged, and then runs forever without the host. Its observation is
  the session's outcomes together with the host state *and log* at the point from which it runs
  host-free; this is the log of the whole session and of the divergent call's own host calls.
  These are `sessDivs` and `refDivs`.
* **Host divergence.** The call makes a host call that the host never answers: the host
  relation diverges on a pending host call. This is a property of the host, not of the
  component, and it is observed by the call's log up to the pending call, and by which host import
  is pending on which arguments (`HLinked2.HostPend`, `HLinked2.hostDivs`). **Synchronous lowering
  turns a blocked host into a trap**: every `canon lower`/`canon lift` of the `SimpleI` fragment is
  synchronous, so on the reference machine an unresolved host call leaves no ready thread in the
  importer's instance, and the synchronous lift loop traps `cannotBlockSync` (REF
  `trap_if(not candidates)`; `HLinked2.silent_cannotBlock_sess` under `silentHost`). Host
  divergence is therefore not a divergence of the reference machine, and it is not in
  `refDivs`. Asynchronous lowering or lifting, where the call would stay pending, is out of
  scope.
* **Infinitely many host calls** (host chatter: B calls the host forever, every call answered).
  The host interface sees infinitely many moves: this is an infinite play, not a divergence, and
  it is in neither set. On the reference machine it is a `CallDiverges` whose host log grows
  without bound, so it is excluded from `refDivs` by the definition below.

## The reference machine

`QuietDiverges prof hr dispatch st m`: from `m`, an infinite sequence of nonempty runs without
host events, each from and to a configuration in host state `st`. `CallQuietDiverges`: the
host's invocation of a top-level call, a finite run without host events, then `QuietDiverges`.
For the logging host `logG g` the log in the host state only grows, strictly at every answered
host call (proved: `HLinked2.logSteps_mono`, `HostWrite.Thms`), so a run that is in host state
`st` at unboundedly late points answers no host call after reaching `st`: this is internal
divergence after the log `st.2`. The definition uses
only reference-machine runs and host states, not the specification, the IR or finite prefixes.

`HLinked2.RefSessDiv P prof l g s₀ calls outs j vs st`: after instantiating `l.toRef` under the
logging host from `(s₀, [])`, the resumable session of `calls` (a trapped call resumes from
`resumeCfg`; the store persists, there is no poisoning) has the outcomes `outs`, and the next
top-level call, export `j` on `vs`, diverges quietly in host state `st`. `HLinked2.refDivs` is
the set of such `(outs, st)`.

## The specification

After a `SessSpec` session whose host calls are answered by `logG g` from `(s₀, [])` to `st`,
reaching the importer's store `u` and the exporter's `π`, the round of the next call
(`HLinked2.RoundDiv`) is a well-formed prefix (`Linked2.DivRound l.toL2`, from `.idle u` to
`.running f s t`), its component import calls an `ExpRunH` segment of the exporter (wired calls
answered by A, from `π` to `π₁`) whose host calls are answered by `logG g` from `st` to `st'`,
and then one of the three internal sources of `Linked2` (at `l.toL2`, whose `ExpRunT` answers
wired calls only):

* **(i)** B diverges host-free (`Linked2.DivB`);
* **(ii)** A diverges inside a wired import call (`Linked2.DivA`);
* **(iii)** wired chatter (`Linked2.Chatter`): infinitely many import calls of B, each answered
  by A (none of them a host call).

`HLinked2.sessDivs P l g s₀ calls j vs` is the set of `(outs, st')`. Host divergence is the same
prefix ending at a host callout on arguments that lift, the host not answering
(`HLinked2.RoundHostDiv`, `HLinked2.hostDivs`).

## Status

`HLinked2.DivSpecToRef P prof l g` (`sessDivs ⊆ refDivs`) and its converse
`HLinked2.DivRefToSpec P prof l g` are proved under `HLinked2.Adequate` and `HLinked2.HostTyped g`
at every profile (`HLinked2.divSpecToRef`, `HLinked2.divRefToSpec`, hence
`HLinked2.sessDivs_eq_refDivs`, `HLinkedSessionDiv.Thms`). `HLinked2.RefSessEquivH` and
`HLinked2.RefSessEquivD` are the reference-machine equivalences of sessions and of sessions with
quiet divergence; `HLinked2.RefSessEquivD.iff_sessDivs` states the divergence clause on the
specification.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component.Runtime (HostFuncId)

local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "RVal" => Silmaril.Wasm.Component.Value.Val

/-! ## Quiet divergence on the reference machine -/

section Quiet

open Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Machine

variable {E : CoreEngine} {σ : Type}

/-- **A quiet segment in host state `st`**: a nonempty run without host events from a
configuration in host state `st` to another one in host state `st`. -/
def QuietSeg (prof : ProfileKind) (hr : HostReady σ) (dispatch : Call E → P E σ (Ret E)) (st : σ)
    (m m' : Machine.Config E σ) : Prop :=
  m.host = st ∧ m'.host = st ∧ ∃ tr, Steps prof hr dispatch m tr m' ∧ tr ≠ [] ∧
    ∀ ev, Label.host ev ∉ tr

/-- **Quiet divergence in host state `st`**: an infinite sequence of quiet segments in host
state `st` from `m`. Under a logging host, no host call is answered after `m`. -/
def QuietDiverges (prof : ProfileKind) (hr : HostReady σ) (dispatch : Call E → P E σ (Ret E))
    (st : σ) (m : Machine.Config E σ) : Prop :=
  Silmaril.InfiniteTrace (QuietSeg prof hr dispatch st) m

/-- **A top-level call diverging quietly in host state `st`**: the host's invocation of call `c`
of `f` on `args`, a finite run without host events, then quiet divergence in host state `st`. -/
def CallQuietDiverges (prof : ProfileKind) (hr : HostReady σ)
    (dispatch : Call E → P E σ (Ret E)) (m : Machine.Config E σ) (c : CallId) (f : FuncId)
    (args : List Val) (st : σ) : Prop :=
  ∃ m₁ tr m₂, Step prof hr dispatch m (.host (invokeTop c f args)) m₁ ∧
    Steps prof hr dispatch m₁ tr m₂ ∧ (∀ ev, Label.host ev ∉ tr) ∧
    QuietDiverges prof hr dispatch st m₂

end Quiet

namespace HLinked2

/-! ## The reference machine -/

section Ref

open Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Canon

variable {σ : Type}

/-- **Quiet divergence of a linked session with host imports**: after instantiating `l.toRef`
under the logging host of `g` from `(s₀, [])`, the resumable session of `calls` has the outcomes
`outs`, and then the call of export `j` of the importer on `vs` diverges quietly in host state
and log `st`. -/
def RefSessDiv (P : Profile) (prof : ProfileKind) (l : HLinked2)
    (g : σ → HostFuncId → List RVal → Option (List RVal × σ)) (s₀ : σ)
    (calls : List (Fin l.imp.exports.length × List IVal)) (outs : List (Option (List IVal)))
    (j : Fin l.imp.exports.length) (vs : List IVal) (st : σ × List HostEvent) : Prop :=
  ∃ m₀ inst es fs m₁ f,
    InstResult.instance m₀ inst es ∈ instBehaviours prof (answerHostS P (logG g))
      (LinkedSession.hostConfig l.host (s₀, [])) l.toRef (importArgs l.host) ∧
    (l.refCalls calls).mapM (fun q => es.lookup q.1) = some fs ∧
    es.lookup l.imp.exports[j].name = some f ∧
    LinkedSession.SessRun prof (answerHostS P (logG g)) m₀ 0
      (fs.zip ((l.refCalls calls).map Prod.snd)) (refOuts outs) m₁ ∧
    CallQuietDiverges prof (answerHostS P (logG g)).hr (answerHostS P (logG g)).dispatch m₁
      ⟨calls.length⟩ f (vs.map toRefVal) st

/-- **The diverging session calls of the reference machine, with the host log**: the outcomes
`outs` and host state and log `st` such that the call of export `j` on `vs` diverges quietly
in `st` after the session `calls` (`RefSessDiv`). -/
def refDivs (P : Profile) (prof : ProfileKind) (l : HLinked2)
    (g : σ → HostFuncId → List RVal → Option (List RVal × σ)) (s₀ : σ)
    (calls : List (Fin l.imp.exports.length × List IVal)) (j : Fin l.imp.exports.length)
    (vs : List IVal) : Set (List (Option (List IVal)) × (σ × List HostEvent)) :=
  {p | RefSessDiv P prof l g s₀ calls p.1 j vs p.2}

end Ref

/-! ## The specification -/

section Spec

open Silmaril.Wasm.Game
open Silmaril.Wasm.Execution.Core (Store)

variable {σ : Type}

/-- **A round that never answers, after a host log**: from the importer's store `u`, the
exporter's store `π` and the host state `st`, the call of export `j` on `vs` starts a
well-formed round whose component import calls so far are an `ExpRunH` segment (wired calls
answered by the exporter) whose host calls are answered as `g` prescribes from `st` to `st'`,
and then diverges internally: the importer host-free (i), the exporter inside a wired call (ii),
or wired chatter (iii). -/
def RoundDiv (P : Profile) (l : HLinked2) (Ie Ii : ScalarInstance)
    (g : σ → HostFuncId → List RVal → Option (List RVal × σ)) (u π : Store Nat) (st : σ)
    (j : Fin l.imp.exports.length) (vs : List IVal) (st' : σ) : Prop :=
  ∃ (d : Linked2.DivRound l.toL2 Ii) (s : Store Nat) (t : Silmaril.Wasm.SingleThreaded.Thread)
    (π₁ : Store Nat),
    d.j = j ∧ d.vs = vs ∧ d.Ok ∧ Ii.Path P (.idle u) d.instMoves (.running d.f s t) ∧
    ExpRunH P l Ie π d.dss.flatten π₁ ∧ HostRun g st (l.hostCalls d.dss.flatten) st' ∧
    (Linked2.DivB P s t ∨ Linked2.DivA P l.toL2 Ie Ii d.f s t π₁ ∨
      Linked2.Chatter P l.toL2 Ie Ii d.f s t π₁)

/-- **The diverging session calls of the specification, with the host log**: the outcomes
`outs` of a specification session of `calls` from the instances' stores, its host calls
answered by the logging host of `g` from `(s₀, [])`, after which the call of export `j` on `vs`
diverges internally after its own host calls, the host state and log being `st'` (`RoundDiv`). -/
def sessDivs (P : Profile) (l : HLinked2)
    (g : σ → HostFuncId → List RVal → Option (List RVal × σ)) (s₀ : σ)
    (calls : List (Fin l.imp.exports.length × List IVal)) (j : Fin l.imp.exports.length)
    (vs : List IVal) : Set (List (Option (List IVal)) × (σ × List HostEvent)) :=
  {p | ∃ (Ie Ii : ScalarInstance) (hs : List (List (Σ _ : (sigN l.host.length).Op, Option Payload)))
      (u π : Store Nat) (st : σ × List HostEvent), l.exp.mod.IsInst Ie ∧ l.imp.mod.IsInst Ii ∧
    SessSpec P l Ie Ii Ii.store Ie.store calls p.1 hs u π ∧
    HostRun (logG g) (s₀, []) hs.flatten st ∧ RoundDiv P l Ie Ii (logG g) u π st j vs p.2}

/-- **A pending host call**: from the running export call `f` at `(s, t)`, the importer calls
out host import `i` (its import `wire.length + i`) on arguments that lift at the import's type
to `ws`. If the host never answers it, the round never answers: host divergence. -/
def HostPend (P : Profile) (l : HLinked2) (Ii : ScalarInstance) (f : Ii.F.Op) (s : Store Nat)
    (t : Silmaril.Wasm.SingleThreaded.Thread) (i : Fin l.host.length) (ws : List IVal) : Prop :=
  ∃ (e : Ii.E.Op) (s' : Store Nat) (t' : Silmaril.Wasm.SingleThreaded.Thread),
    Ii.Path P (.running f s t) [.inl (.ask e)] (.waiting f s' t' e) ∧
    e.1.val = l.wire.length + i.val ∧
    liftArgs l.host[i].2.params (e.2.1.filterMap Silmaril.Wasm.SingleThreaded.toFlat?) = some ws

/-- **A round blocked on the host**: the prefix of `RoundDiv`, then a pending host call of host
import `i` on `ws` (`HostPend`). -/
def RoundHostDiv (P : Profile) (l : HLinked2) (Ie Ii : ScalarInstance)
    (g : σ → HostFuncId → List RVal → Option (List RVal × σ)) (u π : Store Nat) (st : σ)
    (j : Fin l.imp.exports.length) (vs : List IVal) (st' : σ) (i : Fin l.host.length)
    (ws : List IVal) : Prop :=
  ∃ (d : Linked2.DivRound l.toL2 Ii) (s : Store Nat) (t : Silmaril.Wasm.SingleThreaded.Thread)
    (π₁ : Store Nat),
    d.j = j ∧ d.vs = vs ∧ d.Ok ∧ Ii.Path P (.idle u) d.instMoves (.running d.f s t) ∧
    ExpRunH P l Ie π d.dss.flatten π₁ ∧ HostRun g st (l.hostCalls d.dss.flatten) st' ∧
    HostPend P l Ii d.f s t i ws

/-- **Host divergence of the specification**: the outcomes, the host state and log, and the
pending host call `⟨i, ws⟩` of the sessions of `calls` after which the call of export `j` on
`vs` waits forever on the host (`RoundHostDiv`). Under synchronous lowering the reference
machine traps it (`cannotBlockSync`); it is not a reference divergence. -/
def hostDivs (P : Profile) (l : HLinked2)
    (g : σ → HostFuncId → List RVal → Option (List RVal × σ)) (s₀ : σ)
    (calls : List (Fin l.imp.exports.length × List IVal)) (j : Fin l.imp.exports.length)
    (vs : List IVal) :
    Set (List (Option (List IVal)) × (σ × List HostEvent) × (Σ _ : Fin l.host.length, List IVal)) :=
  {p | ∃ (Ie Ii : ScalarInstance) (hs : List (List (Σ _ : (sigN l.host.length).Op, Option Payload)))
      (u π : Store Nat) (st : σ × List HostEvent), l.exp.mod.IsInst Ie ∧ l.imp.mod.IsInst Ii ∧
    SessSpec P l Ie Ii Ii.store Ie.store calls p.1 hs u π ∧
    HostRun (logG g) (s₀, []) hs.flatten st ∧
      RoundHostDiv P l Ie Ii (logG g) u π st j vs p.2.1 p.2.2.1 p.2.2.2}

end Spec

/-- **Specification divergence is reference divergence, with the host log** (a named proposition,
proved under `HLinked2.Adequate` and `HostTyped g` by `HLinked2.divSpecToRef`): every internal
divergence of the specification after a session and a host log is a quiet divergence of the
reference machine in the same host state and log. -/
def DivSpecToRef (P : Profile) (prof : ProfileKind) (l : HLinked2) {σ : Type}
    (g : σ → HostFuncId → List RVal → Option (List RVal × σ)) : Prop :=
  ∀ (s₀ : σ) (calls : List (Fin l.imp.exports.length × List IVal))
    (j : Fin l.imp.exports.length) (vs : List IVal),
    sessDivs P l g s₀ calls j vs ⊆ refDivs P prof l g s₀ calls j vs

/-- **Reference divergence is specification divergence, with the host log** (a named
proposition, proved under `HLinked2.Adequate` and `HostTyped g` by `HLinked2.divRefToSpec`): for
typed calls, every quiet divergence of the reference machine is an internal divergence of the
specification. -/
def DivRefToSpec (P : Profile) (prof : ProfileKind) (l : HLinked2) {σ : Type}
    (g : σ → HostFuncId → List RVal → Option (List RVal × σ)) : Prop :=
  ∀ (s₀ : σ) (calls : List (Fin l.imp.exports.length × List IVal))
    (j : Fin l.imp.exports.length) (vs : List IVal), SimpleI.TypedCalls l.imp calls →
    ValTy.checkList l.imp.exports[j].ty.params vs = true →
    refDivs P prof l g s₀ calls j vs ⊆ sessDivs P l g s₀ calls j vs

/-! ## Equivalences on the reference machine -/

/-- **The resumable-session equivalence of linked components with host imports**, on the
reference machine only: the same export types, the same host imports, and for typed calls,
under every typed host, the same session observations with the host state and log
(`sessObs`). -/
structure RefSessEquivH (P : Profile) (prof : ProfileKind) (l l' : HLinked2) : Prop where
  len : l.imp.exports.length = l'.imp.exports.length
  ty : ∀ j : Fin l.imp.exports.length, l'.imp.exports[Fin.cast len j].ty = l.imp.exports[j].ty
  host : l'.host = l.host
  obs : ∀ calls : List (Fin l.imp.exports.length × List IVal), SimpleI.TypedCalls l.imp calls →
    ∀ {σ : Type} (g : σ → HostFuncId → List RVal → Option (List RVal × σ)), l.HostTyped g →
      ∀ s₀ : σ, sessObs P prof l g s₀ calls =
        sessObs P prof l' g s₀ (Linked2.castCalls (l := l.toL2) (l' := l'.toL2) len calls)

/-- **The resumable-session equivalence with quiet divergence and the host log**, on the
reference machine only: `RefSessEquivH`, and for every typed sequence of calls followed by a
typed call, under every typed host, the same outcomes and host state and log after which that
call diverges quietly (`refDivs`). -/
structure RefSessEquivD (P : Profile) (prof : ProfileKind) (l l' : HLinked2) : Prop
    extends RefSessEquivH P prof l l' where
  div : ∀ (calls : List (Fin l.imp.exports.length × List IVal)) (j : Fin l.imp.exports.length)
      (vs : List IVal), SimpleI.TypedCalls l.imp calls →
      ValTy.checkList l.imp.exports[j].ty.params vs = true →
    ∀ {σ : Type} (g : σ → HostFuncId → List RVal → Option (List RVal × σ)), l.HostTyped g →
      ∀ s₀ : σ, refDivs P prof l g s₀ calls j vs =
        refDivs P prof l' g s₀ (Linked2.castCalls (l := l.toL2) (l' := l'.toL2) len calls)
          (Fin.cast len j) vs

end HLinked2

end Silmaril.Wasm.Component.Reference

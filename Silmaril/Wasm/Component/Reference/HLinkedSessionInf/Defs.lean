module

public import Silmaril.Wasm.Component.Reference.HLinkedSessionDiv.Defs
public import Silmaril.Wasm.Component.Reference.LinkedSessionObs.Defs

/-!
# Infinite plays of linked sessions with host imports: definitions

**Scope.** `HLinked2` (`HLinkedSession.Defs`): the import-free exporter A (`l.exp`) answers the
wired imports of the importer B (`l.imp`), and B's remaining imports are host imports of the
parent, passed through. The reference component is `l.toRef` on `core3P P`, instantiated from the
host functions of `l.host` (`LinkedSession.hostConfig`) under the logging host
`answerHostS P (logG g)` from `(s₀, [])`, as for the finite observations (`HLinked2.sessObs`) and
the divergences (`HLinked2.refDivs`). The session is the resumable extension of REF: a trapped
call aborts that call only, the next call resumes from `resumeCfg` (the store persists, there is
no poisoning).

## Two kinds of infinite play

An infinite play of a session of `HLinked2` (export calls above, host calls below) is one of:

* **infinitely many top-level calls, each terminating** (with finitely many host calls each):
  `HLinked2.RefSessProd` on the reference machine, `HLinked2.SpecSessProd` on the specification;
* **finitely many top-level calls, then a call making infinitely many host calls, each
  answered** (host chatter): `HLinked2.RefSessHProd` / `HLinked2.refHProds` on the reference
  machine, `HLinked2.RoundInf` / `HLinked2.sessHProds` on the specification. This is an infinite
  play of the host interface; it is in neither divergence set (`HLinked2.refDivs` asks that the
  host state recur, which the growing log forbids).

Both are defined independently on the two sides, as single explicit infinite runs, not from
`Comp.den`, not from the session strategies and not as limits of finite prefixes.

## The reference machine

* `HLinked2.RefSessProd P prof l g s₀ a out hst`: an explicit stream `m` of reference
  configurations, `m 0` the configuration after instantiation, call `k` (export `a k`) running
  from `m k` to `m (k + 1)` with outcome `out k` (`SessExec`: results, or a trap and
  `resumeCfg`), and the host state and log at `m k` is `hst k`.
* `CallHostProd prof hr dispatch m c f args ev`: the host's invocation of call `c` from `m`, then
  an explicit infinite run `t` of internal steps along which the host log is, at unboundedly late
  stages, `m.host.2 ++ streamTake ev n` for unboundedly large `n`. Under the logging host the log
  only grows, by one event per answered host call (`HLinked2.logSteps_mono`), so `ev` is the
  stream of the call's answered host calls (function, arguments, results), infinitely many.
* `HLinked2.RefSessHProd P prof l g s₀ calls outs j vs st ev`: the resumable session of `calls`
  has the outcomes `outs` and ends in host state and log `st`, and the call of export `j` on `vs`
  is a `CallHostProd` with the host events `ev`. `HLinked2.refHProds` is the set of
  `(outs, st, ev)`.

## The specification

* `HLinked2.SpecSessProd P l Ie Ii g a out hst`: stores `u k` (B) and `π k` (A) from the
  instances' stores, each call `a k` a one-round `HLinked2.SessSpec` from `(u k, π k)` to
  `(u (k + 1), π (k + 1))` with outcome `out k` and host calls `hs k`, these answered by `g` from
  `hst k` to `hst (k + 1)` (`HostRun`).
* `HLinked2.RoundInf P l Ie Ii g u π st j vs hst`: the call of export `j` on `vs` from `(u, π)`
  asks B's instance (arguments lowered as `DivRound.Ok` checks them), and then B makes infinitely
  many core import calls `c k`, each related to component import calls `ds k` (`ImpRel`), the
  wired ones answered by A (`ExpRunH`, A's store threaded) and the host ones answered by `g` from
  `hst k` to `hst (k + 1)` (`HostRun`), `hst 0 = st`.
* `HLinked2.sessHProds P l g s₀ calls j vs`: the `(outs, st, ev)` such that a specification
  session of `calls` from the instances' stores, its host calls answered by `logG g` from
  `(s₀, [])` to `st`, is followed by a `RoundInf` of the call of `j` on `vs` under `logG g` from
  `st` whose logs are, at unboundedly late rounds, `st.2 ++ streamTake ev n` for unboundedly large
  `n`. The log only grows at answered host calls, so such a round makes infinitely many host
  calls (wired chatter alone keeps the log, and is a divergence: `HLinked2.sessDivs`).

## Equivalence

`HLinked2.RefSessEquivFull P prof l l'`: `HLinked2.RefSessEquivD` (terminating outcomes with the
host log, and quiet divergences), and under every typed host the same productive executions of
typed streams of calls (`RefSessProd`, with the host-state stream) and the same host-chatter
plays after typed sessions (`refHProds`). Reference-machine runs only.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component.Runtime (HostFuncId)
open Silmaril.Games.Abstract (streamTake)

local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "RVal" => Silmaril.Wasm.Component.Value.Val

/-! ## Host chatter on the reference machine -/

section Chatter

open Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Machine

variable {E : CoreEngine} {σ ε : Type}

/-- **A top-level call making infinitely many host calls**: the host's invocation of call `c` of
`f` on `args` from `m`, then an explicit infinite run `t` of internal steps along which the log in
the host state is, at unboundedly late stages, the log of `m` followed by the first `n` host
events of `ev`, for unboundedly large `n`. -/
def CallHostProd (prof : ProfileKind) (hr : HostReady (σ × List ε))
    (dispatch : Call E → P E (σ × List ε) (Ret E)) (m : Machine.Config E (σ × List ε))
    (c : CallId) (f : FuncId) (args : List Val) (ev : ℕ → ε) : Prop :=
  ∃ t : ℕ → Machine.Config E (σ × List ε),
    Step prof hr dispatch m (.host (invokeTop c f args)) (t 0) ∧
    (∀ n, InternalStep prof hr dispatch (t n) (t (n + 1))) ∧
    ∀ N, ∃ n p, N ≤ n ∧ (t p).host.2 = m.host.2 ++ streamTake ev n

end Chatter

namespace HLinked2

/-! ## The reference machine -/

section Ref

open Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Canon

variable {σ : Type}

/-- **A productive execution of a linked session with host imports**: after instantiating
`l.toRef` under the logging host of `g` from `(s₀, [])`, an explicit coherent stream `m` of
reference configurations running the export calls `a 0, a 1, …` of the importer with the outcomes
`out 0, out 1, …` (results, or `none` for a trap followed by `resumeCfg`), the host state and log
at `m k` being `hst k`. -/
def RefSessProd (P : Profile) (prof : ProfileKind) (l : HLinked2)
    (g : σ → HostFuncId → List RVal → Option (List RVal × σ)) (s₀ : σ)
    (a : ℕ → Fin l.imp.exports.length × List IVal) (out : ℕ → Option (List IVal))
    (hst : ℕ → σ × List HostEvent) : Prop :=
  ∃ m₀ inst es, ∃ fs : ℕ → Runtime.FuncId, ∃ m,
    InstResult.instance m₀ inst es ∈ instBehaviours prof (answerHostS P (logG g))
      (LinkedSession.hostConfig l.host (s₀, [])) l.toRef (importArgs l.host) ∧
    (∀ k, es.lookup l.imp.exports[(a k).1].name = some (fs k)) ∧
    SessExec prof (answerHostS P (logG g)) m₀ (fun k => (fs k, (a k).2.map toRefVal))
      (fun k => (out k).map (List.map toRefVal)) m ∧
    ∀ k, (m k).host = hst k

/-- **A session followed by a call making infinitely many host calls**: after instantiating
`l.toRef` under the logging host of `g` from `(s₀, [])`, the resumable session of `calls` has the
outcomes `outs` and ends in host state and log `st`, and the call of export `j` of the importer on
`vs` makes infinitely many host calls, its host events being `ev` (`CallHostProd`). -/
def RefSessHProd (P : Profile) (prof : ProfileKind) (l : HLinked2)
    (g : σ → HostFuncId → List RVal → Option (List RVal × σ)) (s₀ : σ)
    (calls : List (Fin l.imp.exports.length × List IVal)) (outs : List (Option (List IVal)))
    (j : Fin l.imp.exports.length) (vs : List IVal) (st : σ × List HostEvent)
    (ev : ℕ → HostEvent) : Prop :=
  ∃ m₀ inst es fs m₁ f,
    InstResult.instance m₀ inst es ∈ instBehaviours prof (answerHostS P (logG g))
      (LinkedSession.hostConfig l.host (s₀, [])) l.toRef (importArgs l.host) ∧
    (l.refCalls calls).mapM (fun q => es.lookup q.1) = some fs ∧
    es.lookup l.imp.exports[j].name = some f ∧
    LinkedSession.SessRun prof (answerHostS P (logG g)) m₀ 0
      (fs.zip ((l.refCalls calls).map Prod.snd)) (refOuts outs) m₁ ∧
    m₁.host = st ∧
    CallHostProd prof (answerHostS P (logG g)).hr (answerHostS P (logG g)).dispatch m₁
      ⟨calls.length⟩ f (vs.map toRefVal) ev

/-- **The host-chatter plays of the reference machine**: the outcomes, the host state and log
`st` after the session `calls`, and the host events `ev` of the next call of export `j` on `vs`
when it makes infinitely many host calls (`RefSessHProd`). -/
def refHProds (P : Profile) (prof : ProfileKind) (l : HLinked2)
    (g : σ → HostFuncId → List RVal → Option (List RVal × σ)) (s₀ : σ)
    (calls : List (Fin l.imp.exports.length × List IVal)) (j : Fin l.imp.exports.length)
    (vs : List IVal) :
    Set (List (Option (List IVal)) × (σ × List HostEvent) × (ℕ → HostEvent)) :=
  {p | RefSessHProd P prof l g s₀ calls p.1 j vs p.2.1 p.2.2}

end Ref

/-! ## The specification -/

section Spec

open Silmaril.Wasm.Game
open Silmaril.Wasm.Execution.Core (Store)

variable {σ : Type}

/-- **An infinite session of the specification**: from the instances' stores, each call `a k` is
a one-round `SessSpec` with outcome `out k` and host calls `hs k`, which `g` answers from `hst k`
to `hst (k + 1)`. -/
def SpecSessProd (P : Profile) (l : HLinked2) (Ie Ii : ScalarInstance)
    (g : σ → HostFuncId → List RVal → Option (List RVal × σ))
    (a : ℕ → Fin l.imp.exports.length × List IVal) (out : ℕ → Option (List IVal))
    (hst : ℕ → σ) : Prop :=
  ∃ (u π : ℕ → Store Nat) (hs : ℕ → List (Σ _ : (sigN l.host.length).Op, Option Payload)),
    u 0 = Ii.store ∧ π 0 = Ie.store ∧
    ∀ k, SessSpec P l Ie Ii (u k) (π k) [a k] [out k] [hs k] (u (k + 1)) (π (k + 1)) ∧
      HostRun g (hst k) (hs k) (hst (k + 1))

/-- **A round making infinitely many import calls**: from the importer's store `u` and the
exporter's store `π`, the call of export `j` on `vs` asks the importer's core instance (the core
question `f` on the lowered arguments), which then makes infinitely many core import calls
`c 0, c 1, …`, each related to component import calls `ds k` (`ImpRel`): the wired ones answered
by the exporter from its store on (`ExpRunH`), the host ones answered by `g` from `hst k` to
`hst (k + 1)`, `hst 0 = st`. -/
def RoundInf (P : Profile) (l : HLinked2) (Ie Ii : ScalarInstance)
    (g : σ → HostFuncId → List RVal → Option (List RVal × σ)) (u π : Store Nat) (st : σ)
    (j : Fin l.imp.exports.length) (vs : List IVal) (hst : ℕ → σ) : Prop :=
  ∃ (f : Ii.F.Op) (xs : List Flat) (q : ℕ → Ii.HState) (c : ℕ → Σ e : Ii.E.Op, Ii.E.Ar e)
    (ds : ℕ → List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload))
    (πs : ℕ → Store Nat),
    checkLower l.imp.exports[j].ty.params vs = some xs ∧ f.1.val = l.imp.exports[j].core ∧
    f.2.1 = xs.map Silmaril.Wasm.SingleThreaded.ofFlat ∧
    Ii.Path P (.idle u) [.inr (.ask f)] (q 0) ∧ πs 0 = π ∧ hst 0 = st ∧
    ∀ k, Ii.Path P (q k) (callMoves [c k]) (q (k + 1)) ∧ ImpRel l.imp Ii (c k) (ds k) ∧
      ExpRunH P l Ie (πs k) (ds k) (πs (k + 1)) ∧ HostRun g (hst k) (l.hostCalls (ds k)) (hst (k + 1))

/-- **The host-chatter plays of the specification**: the outcomes `outs` and the host state and
log `st` of a specification session of `calls` from the instances' stores, its host calls answered
by the logging host of `g` from `(s₀, [])`, after which the call of export `j` on `vs` is a
`RoundInf` under the logging host from `st` whose logs are, at unboundedly late rounds,
`st.2 ++ streamTake ev n` for unboundedly large `n`. -/
def sessHProds (P : Profile) (l : HLinked2)
    (g : σ → HostFuncId → List RVal → Option (List RVal × σ)) (s₀ : σ)
    (calls : List (Fin l.imp.exports.length × List IVal)) (j : Fin l.imp.exports.length)
    (vs : List IVal) :
    Set (List (Option (List IVal)) × (σ × List HostEvent) × (ℕ → HostEvent)) :=
  {p | ∃ (Ie Ii : ScalarInstance) (hs : List (List (Σ _ : (sigN l.host.length).Op, Option Payload)))
      (u π : Store Nat) (hst : ℕ → σ × List HostEvent), l.exp.mod.IsInst Ie ∧
    l.imp.mod.IsInst Ii ∧ SessSpec P l Ie Ii Ii.store Ie.store calls p.1 hs u π ∧
    HostRun (logG g) (s₀, []) hs.flatten p.2.1 ∧ RoundInf P l Ie Ii (logG g) u π p.2.1 j vs hst ∧
    ∀ N, ∃ n k, N ≤ n ∧ (hst k).2 = p.2.1.2 ++ streamTake p.2.2 n}

end Spec

/-! ## The full equivalence on the reference machine -/

/-- **The full resumable-session equivalence of linked components with host imports**, on
reference-machine runs only: `RefSessEquivD` (the same export types and host imports, the same
terminating outcomes with the host state and log, the same quiet divergences), and under every
typed host the same productive executions of typed streams of calls, with their host-state
streams, and the same host-chatter plays after typed sessions. -/
structure RefSessEquivFull (P : Profile) (prof : ProfileKind) (l l' : HLinked2) : Prop
    extends RefSessEquivD P prof l l' where
  prod : ∀ (a : ℕ → Fin l.imp.exports.length × List IVal) (out : ℕ → Option (List IVal)),
    (∀ k, ValTy.checkList l.imp.exports[(a k).1].ty.params (a k).2 = true) →
    ∀ {σ : Type} (g : σ → HostFuncId → List RVal → Option (List RVal × σ)), l.HostTyped g →
      ∀ (s₀ : σ) (hst : ℕ → σ × List HostEvent),
        (RefSessProd P prof l g s₀ a out hst ↔
          RefSessProd P prof l' g s₀ (Linked2.castStream (l := l.toL2) (l' := l'.toL2) len a)
            out hst)
  hprod : ∀ (calls : List (Fin l.imp.exports.length × List IVal)) (j : Fin l.imp.exports.length)
      (vs : List IVal), SimpleI.TypedCalls l.imp calls →
      ValTy.checkList l.imp.exports[j].ty.params vs = true →
    ∀ {σ : Type} (g : σ → HostFuncId → List RVal → Option (List RVal × σ)), l.HostTyped g →
      ∀ s₀ : σ, refHProds P prof l g s₀ calls j vs =
        refHProds P prof l' g s₀ (Linked2.castCalls (l := l.toL2) (l' := l'.toL2) len calls)
          (Fin.cast len j) vs

end HLinked2

end Silmaril.Wasm.Component.Reference

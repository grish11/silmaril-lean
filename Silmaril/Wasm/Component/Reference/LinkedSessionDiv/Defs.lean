module

public import Silmaril.Wasm.Component.Reference.LinkedSessionRef.Defs
public import Silmaril.Wasm.Component.Reference.SessionObs.Defs
public import Silmaril.Wasm.Component.Reference.SessionStrat.Defs

/-!
# Diverging calls of linked sessions: definitions

**Scope.** `Linked2` only: the import-free exporter A (`l.exp`) answering every import of the
importer B (`l.imp`) through the canonical ABI, under `Linked2.Adequate` for the theorems. The
sessions are #705's `Linked2.SessSpec` (specification) and `Linked2.sessObs` (reference machine,
`l.toRef` under `linkHost impl`; a trapped call resumes from `resumeCfg`, a modelling choice,
REF itself locks the store down).

## The reference observation

`Linked2.RefSessQuiet P prof l impl h₀ calls outs j vs`: after instantiating `l.toRef`, the
resumable reference session of `calls` has the outcomes `outs`, and the next top-level call,
export `j` of the importer on `vs`, diverges (`CallDiverges`: the host's invocation, then an
infinite run of machine steps). Defined from reference runs only (`SessDiv`, as #680's
`RefSessQuiet` for `Simple`). `Linked2.refDivs` is the set of such `outs`.

## The specification: three sources of divergence

After a specification session reaching the importer's store `u` and the exporter's store `π`,
the round of the next call (`Linked2.DivRound`, well formed: `DivRound.Ok`) is played by B's core
instance (`Ii.Path`, from `.idle u` to `.running f s t`), its core import calls related to
component import calls (`ImpRel`) answered by A's specification (`ExpRunT`, from `π` to `π₁`);
then the round never answers (`Linked2.RoundDiv`), for one of three reasons, all on Core runs:

* **(i) B diverges host-free** (`Linked2.DivB`): B's thread runs host-free forever from `(s, t)`;
* **(ii) A diverges inside an import call** (`Linked2.DivA`): B calls out (`.inl (.ask e)`) on
  arguments that lift at the import's type, and the wired export of A diverges on them from its
  current store `π₁` (`DivAt`, #680);
* **(iii) chatter** (`Linked2.Chatter`): B makes infinitely many core import calls in the round,
  each answered by A's specification, the stores of both threaded through them.

`Linked2.sessDivs P l calls j vs`: the outcomes of the specification sessions of `calls` from
the instances' stores after which the call of export `j` on `vs` diverges, by (i), (ii) or (iii).

**Chatter is possible on the reference machine.** A single core activation of B may make
unboundedly many import calls (a core loop calling an import, say `(loop (call $set) (br 0))`).
Each call is a nested `canon lower`/`canon lift` call into A run by the machine without the host;
if each returns, the top-level call never resolves, and the machine runs forever: a
`CallDiverges`. So (iii) is not vacuous, and it is not a case of (i): B's own Core runs between
the calls are finite.

**The game-level counterpart.** These are the three divergent ends of a round of the H2 owner's
linked triple `Games.Abstract.SessionLink.linkS` (#706): the client diverges (i), the server
diverges inside a served call (ii), the client makes infinitely many served calls with finitely
many lower calls in total (iii), the hidden chatter of `DStrategy.comp`
(`DivComp.mem_div_comp_of_chatter`, `mem_div_comp_of_left`, `mem_div_comp_of_right`). The
formal correspondence to `comp_threadS` is not stated here.

## Pending

`Linked2.DivSpecToRef P prof l`: every specification divergence is a reference one
(`sessDivs ⊆ refDivs`). It is a named proposition, **not proved** and assumed by no theorem: the
forward runs of #712 (`LinkedSessionFwd`: `rounds_fwd`, `reach_link_fwd`, `exp_fwd`,
`linkCall_fwd`) are finite, and the three sources need their infinite versions (a host-free
infinite run of B's part, of A's part inside a nested call, and an infinite sequence of served
rounds, each mapped to a nonempty run of the machine). The converse (reference divergence to
specification divergence, as #680's `divAt_of_callDiverges`) is also open.

**Not covered.** Host observations: within `Linked2` every import of B is wired to A, so
`l.toRef` has no host imports and `linkHost impl` is never called; a parent that also passes host
imports to B (`linkedHRef`) lets B call the host, which these definitions do not cover. Productive
(infinite) linked executions are the next step, through `mem_inf_linkS_iff_of_det` (#706). The
parser from bytes to these components, and F6, are pending.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)

local notation "IVal" => Silmaril.Wasm.Component.Val

namespace Linked2

/-! ## The reference machine -/

section Ref

open Silmaril.Wasm.Component.Runtime

/-- **Quiescent divergence of a linked session**: after instantiating `l.toRef` under
`linkHost impl` from `h₀`, the resumable session of `calls` has the outcomes `outs`, and then the
call of export `j` of the importer on `vs` diverges on the reference machine. -/
def RefSessQuiet (P : Profile) (prof : ProfileKind) (l : Linked2) {σ : Type}
    (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ) (h₀ : σ)
    (calls : List (Fin l.imp.exports.length × List IVal)) (outs : List (Option (List IVal)))
    (j : Fin l.imp.exports.length) (vs : List IVal) : Prop :=
  ∃ m₀ inst es fs f,
    InstResult.instance m₀ inst es ∈ instBehaviours prof (linkHost impl) (initConfig h₀) l.toRef [] ∧
    (calls.map fun q => (l.imp.exports[q.1].name, q.2.map toRefVal)).mapM
      (fun q => es.lookup q.1) = some fs ∧
    es.lookup l.imp.exports[j].name = some f ∧
    SessDiv prof (linkHost impl) m₀ 0 (fs.zip (calls.map fun q => q.2.map toRefVal))
      (refOuts outs) f (vs.map toRefVal)

/-- **The diverging session calls of the reference machine**: the outcomes after which the call
of export `j` on `vs` diverges (`RefSessQuiet`). -/
def refDivs (P : Profile) (prof : ProfileKind) (l : Linked2) {σ : Type}
    (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ) (h₀ : σ)
    (calls : List (Fin l.imp.exports.length × List IVal)) (j : Fin l.imp.exports.length)
    (vs : List IVal) : Set (List (Option (List IVal))) :=
  {outs | RefSessQuiet P prof l impl h₀ calls outs j vs}

end Ref

/-! ## The specification -/

section Spec

open Silmaril.Wasm.Game
open Silmaril.Wasm.Execution.Core (Store)

/-- **The start of a round that does not answer**: export `j` of the importer on `vs`, the core
question `f` of the importer's instance, the core import calls `cs` made so far (with their
answers), and the component import calls `dss` they correspond to. -/
structure DivRound (l : Linked2) (Ii : ScalarInstance) where
  /-- The export of the importer (and of the linked component). -/
  j : Fin l.imp.exports.length
  /-- The IR arguments. -/
  vs : List IVal
  /-- The core question of the importer's instance. -/
  f : Ii.F.Op
  /-- The core import calls so far, with their answers. -/
  cs : List (Σ e : Ii.E.Op, Ii.E.Ar e)
  /-- The component import calls of each core import call. -/
  dss : List (List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload))

namespace DivRound

variable {l : Linked2} {Ii : ScalarInstance} (d : DivRound l Ii)

/-- The round is well formed, as `SessRound.Ok`. -/
def Ok : Prop :=
  ∃ xs : List Flat, checkLower l.imp.exports[d.j].ty.params d.vs = some xs ∧
    d.f.1.val = l.imp.exports[d.j].core ∧ d.f.2.1 = xs.map Silmaril.Wasm.SingleThreaded.ofFlat ∧
    List.Forall₂ (ImpRel l.imp Ii) d.cs d.dss

/-- The play of the importer's core instance so far: the question and the import calls. -/
def instMoves : List (Silmaril.Games.Move Ii.E Ii.F) :=
  .inr (.ask d.f) :: callMoves d.cs

end DivRound

/-- **(i) The importer diverges host-free** from its thread `(s, t)`. -/
def DivB (P : Profile) (s : Store Nat) (t : Silmaril.Wasm.SingleThreaded.Thread) : Prop :=
  ∃ g : ℕ → Store Nat × Silmaril.Wasm.SingleThreaded.Thread,
    g 0 = (s, t) ∧ ∀ k, InternalP P (g k) (g (k + 1))

/-- **(ii) The exporter diverges inside an import call**: from the running export call `f` at
`(s, t)`, the importer calls out (core import `e`), the arguments lift at the import's type to
`ws`, and the wired export `w` of the exporter diverges on `ws` from its store `π`. -/
def DivA (P : Profile) (l : Linked2) (Ie Ii : ScalarInstance) (f : Ii.F.Op) (s : Store Nat)
    (t : Silmaril.Wasm.SingleThreaded.Thread) (π : Store Nat) : Prop :=
  ∃ (e : Ii.E.Op) (s' : Store Nat) (t' : Silmaril.Wasm.SingleThreaded.Thread) (nm : String)
    (ft : FuncTy) (ws : List IVal) (w : Fin l.exp.exports.length),
    Ii.Path P (.running f s t) [.inl (.ask e)] (.waiting f s' t' e) ∧
    l.imp.imports[e.1.val]? = some (nm, ft) ∧
    liftArgs ft.params (e.2.1.filterMap Silmaril.Wasm.SingleThreaded.toFlat?) = some ws ∧
    l.wire[e.1.val]? = some w.val ∧ DivAt P Ie l.exp.exports[w] ws π

/-- **(iii) Chatter**: from the running export call `f` at `(s, t)`, the importer makes infinitely
many core import calls `c 0, c 1, …`, each related to component import calls `ds k` (`ImpRel`)
answered by the exporter's specification, from its store `π` on (`ExpRunT`, traps continuing). -/
def Chatter (P : Profile) (l : Linked2) (Ie Ii : ScalarInstance) (f : Ii.F.Op) (s : Store Nat)
    (t : Silmaril.Wasm.SingleThreaded.Thread) (π : Store Nat) : Prop :=
  ∃ (q : ℕ → Ii.HState) (c : ℕ → Σ e : Ii.E.Op, Ii.E.Ar e)
    (ds : ℕ → List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload))
    (st : ℕ → Store Nat),
    q 0 = .running f s t ∧ st 0 = π ∧
    ∀ k, Ii.Path P (q k) (callMoves [c k]) (q (k + 1)) ∧ ImpRel l.imp Ii (c k) (ds k) ∧
      ExpRunT P l Ie (st k) (ds k) (st (k + 1))

/-- **A round that never answers**: from the importer's store `u` and the exporter's store `π`,
the call of export `j` on `vs` starts a well-formed round whose import calls so far are answered
by the exporter, and then diverges by (i), (ii) or (iii). -/
def RoundDiv (P : Profile) (l : Linked2) (Ie Ii : ScalarInstance) (u π : Store Nat)
    (j : Fin l.imp.exports.length) (vs : List IVal) : Prop :=
  ∃ (d : DivRound l Ii) (s : Store Nat) (t : Silmaril.Wasm.SingleThreaded.Thread)
    (π₁ : Store Nat),
    d.j = j ∧ d.vs = vs ∧ d.Ok ∧ Ii.Path P (.idle u) d.instMoves (.running d.f s t) ∧
    ExpRunT P l Ie π d.dss.flatten π₁ ∧
    (DivB P s t ∨ DivA P l Ie Ii d.f s t π₁ ∨ Chatter P l Ie Ii d.f s t π₁)

/-- **The diverging session calls of the specification**: the outcomes `outs` of a specification
session of `calls` from the instances' stores after which the call of export `j` on `vs`
diverges. -/
def sessDivs (P : Profile) (l : Linked2) (calls : List (Fin l.imp.exports.length × List IVal))
    (j : Fin l.imp.exports.length) (vs : List IVal) : Set (List (Option (List IVal))) :=
  {outs | ∃ (Ie Ii : ScalarInstance) (u π : Store Nat), l.exp.mod.IsInst Ie ∧
    l.imp.mod.IsInst Ii ∧ SessSpec P l Ie Ii Ii.store Ie.store calls outs u π ∧
    RoundDiv P l Ie Ii u π j vs}

end Spec

/-- **Specification divergence is reference divergence** (a named proposition, not proved and
assumed by no theorem; see the module documentation): for typed calls, every diverging session
call of the specification is one of the reference machine, under every host. -/
def DivSpecToRef (P : Profile) (prof : ProfileKind) (l : Linked2) : Prop :=
  ∀ (calls : List (Fin l.imp.exports.length × List IVal)) (j : Fin l.imp.exports.length)
    (vs : List IVal), SimpleI.TypedCalls l.imp calls →
    ValTy.checkList l.imp.exports[j].ty.params vs = true →
    ∀ {σ : Type} (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ) (h₀ : σ),
      sessDivs P l calls j vs ⊆ refDivs P prof l impl h₀ calls j vs

end Linked2

end Silmaril.Wasm.Component.Reference

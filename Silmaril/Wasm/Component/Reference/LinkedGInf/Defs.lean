module

public import Silmaril.Wasm.Component.Reference.LinkedGChatter.Defs
public import Silmaril.Wasm.Component.Reference.LinkedGChain.Defs
public import Silmaril.Wasm.Component.Reference.SessionObs.Defs

/-!
# Infinite plays and the full injection of linked components and chains: definitions

**Scope.** `LinkedG` (an exporter `ExpSpec` linked with a simple importer), in particular one
more importer on a chain (`⟨n.spec Ib Is, b, w⟩`); the IR `g.toComp.denUD (impSemD P)` over
`sigU`; the reference machine over `core3P P` under `linkHost impl`. For the theorems, the
deterministic profiles `profile o`. This mirrors `Linked2`'s `RefSessProd` and
`RefSessEquivFull` (`LinkedSessionObs.Defs`) and the IR projections of #833
(`LinkedSessionDAdeq.Defs`).

## Infinite plays of typed call streams

`LinkedG.roundU g a out k`: call `k` of the stream, export `(a k).1` of the importer on
`(a k).2`, answered by `out k` (results, or `none` for a trap), as a round at `sigU` (a round of
`g.toExp Ii`). `LinkedG.sessInfU g a out`: the infinite play, the limit of the plays `uMoves`
of the finite prefixes of these rounds (the form of `ExpSpec.AdeqI`).

## Productive executions on the reference machine

`LinkedG.RefSessProd P prof g impl h₀ a out` is `Linked2.RefSessProd` for `g.toRef`: after
instantiating `g.toRef` under `linkHost impl` from `h₀`, an explicit coherent stream of reference
configurations (`SessExec`) runs the export calls `a 0, a 1, …` with the outcomes
`out 0, out 1, …` (a trap followed by `resumeCfg`). It is defined from reference runs only.

## The full equivalence and the IR projections

`LinkedG.RefSessEquivFull P prof g g'`: the same export types, and, under every host, the same
terminating session outcomes (`LinkedG.sessObs`), the same quiescent divergences
(`LinkedG.RefSessQuiet`) after typed sessions and the same productive executions
(`LinkedG.RefSessProd`) of typed streams. Reference-defined.

The IR denotations of `g` and `g'` have the same type (`DStrategy sigU sigU`), but they also
answer ill-typed calls, on which the exporter interface (`ExpSpec.Adeq`) says nothing. They are
compared on their typed projections, the export indices cast along the equal export counts:

* `LinkedG.IRFinEq`: the finite plays of typed complete sessions (`uMoves (g.sessU calls outs)`)
  of `(g.toComp.denUD (impSemD P)).toStrategy`;
* `LinkedG.IRDivEq`: the divergences after a typed session on a typed pending call;
* `LinkedG.IRInfEq`: the infinite plays of typed call streams (`sessInfU`).

## The hypotheses at a deterministic profile

`LinkedG.ProfOk o g`: what the theorems use of a link at `profile o`: the exporter meets the IR
interface (`Adeq`, `AdeqD`, `AdeqI`), is deterministic (`Det`) and meets the reference interface
with divergence (`RefAdeqUXD`), and the link meets `LinkOk`. `LinkedN.ExtOk n Ib Is b w`: the
hypotheses of `LinkedN.sessDivs_eq_refDivs` on one more importer `b` on the chain `n`; such a
link meets `ProfOk` (`LinkedN.ExtOk.profOk`, `Thms`).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Games Silmaril.Wasm.Component
open Silmaril.Games.Abstract (streamTake)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)
open Silmaril.Wasm.Game (ScalarInstance)

local notation "IVal" => Silmaril.Wasm.Component.Val

namespace LinkedG

/-! ## Infinite plays of typed call streams -/

/-- **Call `k` of a stream as a round at `sigU`**: export `(a k).1` of the importer on `(a k).2`,
answered by `out k` (results, or `none` for a trap). -/
def roundU (g : LinkedG) (a : ℕ → Fin g.imp.exports.length × List IVal)
    (out : ℕ → Option (List IVal)) (k : ℕ) : URound :=
  ⟨((a k).1.val, .vals (a k).2), (out k).map .vals⟩

/-- **The infinite play of a call stream** at `sigU`: the limit of the plays of its finite
prefixes. -/
def sessInfU (g : LinkedG) (a : ℕ → Fin g.imp.exports.length × List IVal)
    (out : ℕ → Option (List IVal)) : Set (List (Move sigU sigU)) :=
  Chain.lim fun n => uMoves (streamTake (g.roundU a out) n)

/-! ## Productive executions on the reference machine -/

/-- **A productive execution of a linked component**: after instantiating `g.toRef` under
`linkHost impl` from `h₀`, an explicit coherent stream of reference configurations running the
export calls `a 0, a 1, …` of the importer with the outcomes `out 0, out 1, …` (results, or
`none` for a trap followed by `resumeCfg`). -/
def RefSessProd (P : Profile) (prof : ProfileKind) (g : LinkedG) {σ : Type}
    (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ) (h₀ : σ)
    (a : ℕ → Fin g.imp.exports.length × List IVal) (out : ℕ → Option (List IVal)) : Prop :=
  ∃ m₀ inst es, ∃ fs : ℕ → Runtime.FuncId,
    InstResult.instance m₀ inst es ∈
      instBehaviours prof (linkHost impl) (initConfig h₀) g.toRef [] ∧
    (∀ k, es.lookup g.imp.exports[(a k).1].name = some (fs k)) ∧
    SessProd prof (linkHost impl) m₀ (fun k => (fs k, (a k).2.map toRefVal))
      (fun k => (out k).map (List.map toRefVal))

/-! ## The full equivalence -/

/-- Calls read at a linked component with the same number of exports. -/
def castCalls {g g' : LinkedG} (h : g.imp.exports.length = g'.imp.exports.length)
    (calls : List (Fin g.imp.exports.length × List IVal)) :
    List (Fin g'.imp.exports.length × List IVal) :=
  calls.map fun q => (Fin.cast h q.1, q.2)

/-- A stream of calls read at a linked component with the same number of exports. -/
def castStream {g g' : LinkedG} (h : g.imp.exports.length = g'.imp.exports.length)
    (a : ℕ → Fin g.imp.exports.length × List IVal) : ℕ → Fin g'.imp.exports.length × List IVal :=
  fun k => (Fin.cast h (a k).1, (a k).2)

/-- The same export types of the importers, in order. -/
def SameTypes (g g' : LinkedG) : Prop := g.imp.exports.map (·.ty) = g'.imp.exports.map (·.ty)

/-- **The full resumable-session equivalence of linked components**, on reference-machine runs
only and under every host: the same export types, the same terminating session outcomes of typed
calls, the same quiescent divergences after every typed session on a typed pending call, and the
same productive executions of every typed stream of calls. -/
structure RefSessEquivFull (P : Profile) (prof : ProfileKind) (g g' : LinkedG) : Prop where
  len : g.imp.exports.length = g'.imp.exports.length
  ty : ∀ j : Fin g.imp.exports.length, g'.imp.exports[Fin.cast len j].ty = g.imp.exports[j].ty
  obs : ∀ calls : List (Fin g.imp.exports.length × List IVal), SimpleI.TypedCalls g.imp calls →
    ∀ {σ : Type} (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ) (h₀ : σ),
      LinkedG.sessObs prof g impl h₀ calls =
        LinkedG.sessObs prof g' impl h₀ (castCalls len calls)
  quiet : ∀ (calls : List (Fin g.imp.exports.length × List IVal))
      (outs : List (Option (List IVal))) (j : Fin g.imp.exports.length) (vs : List IVal),
    SimpleI.TypedCalls g.imp calls → ValTy.checkList g.imp.exports[j].ty.params vs = true →
    ∀ {σ : Type} (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ) (h₀ : σ),
      (LinkedG.RefSessQuiet P prof g impl h₀ calls outs j vs ↔
        LinkedG.RefSessQuiet P prof g' impl h₀ (castCalls len calls) outs (Fin.cast len j) vs)
  prod : ∀ (a : ℕ → Fin g.imp.exports.length × List IVal) (out : ℕ → Option (List IVal)),
    (∀ k, ValTy.checkList g.imp.exports[(a k).1].ty.params (a k).2 = true) →
    ∀ {σ : Type} (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ) (h₀ : σ),
      (LinkedG.RefSessProd P prof g impl h₀ a out ↔
        LinkedG.RefSessProd P prof g' impl h₀ (castStream len a) out)

/-! ## The IR projections -/

/-- **The same finite IR plays of typed sessions**: for typed calls with outcomes, the session
play is a finite play of the IR of `g` at `P` iff it is one of `g'`'s. -/
def IRFinEq (P : Profile) (g g' : LinkedG) : Prop :=
  ∃ len : g.imp.exports.length = g'.imp.exports.length,
    ∀ (calls : List (Fin g.imp.exports.length × List IVal)) (outs : List (Option (List IVal))),
      SimpleI.TypedCalls g.imp calls → calls.length = outs.length →
      (uMoves (g.sessU calls outs) ∈ (g.toComp.denUD (impSemD P)).toStrategy ↔
        uMoves (g'.sessU (castCalls len calls) outs) ∈ (g'.toComp.denUD (impSemD P)).toStrategy)

/-- **The same IR divergences after typed sessions**: for typed calls with outcomes and a typed
pending call, the IRs of `g` and `g'` at `P` diverge alike. -/
def IRDivEq (P : Profile) (g g' : LinkedG) : Prop :=
  ∃ len : g.imp.exports.length = g'.imp.exports.length,
    ∀ (calls : List (Fin g.imp.exports.length × List IVal)) (outs : List (Option (List IVal)))
      (j : Fin g.imp.exports.length) (vs : List IVal),
      SimpleI.TypedCalls g.imp calls → calls.length = outs.length →
      ValTy.checkList g.imp.exports[j].ty.params vs = true →
      (uMoves (g.sessU calls outs) ++ [.inr (.ask (j.val, .vals vs))] ∈
          (g.toComp.denUD (impSemD P)).div ↔
        uMoves (g'.sessU (castCalls len calls) outs) ++
            [.inr (.ask ((Fin.cast len j).val, .vals vs))] ∈ (g'.toComp.denUD (impSemD P)).div)

/-- **The same infinite IR plays of typed call streams**: for a typed stream of calls with
outcomes, its infinite play is one of the IR of `g` at `P` iff it is one of `g'`'s. -/
def IRInfEq (P : Profile) (g g' : LinkedG) : Prop :=
  ∃ len : g.imp.exports.length = g'.imp.exports.length,
    ∀ (a : ℕ → Fin g.imp.exports.length × List IVal) (out : ℕ → Option (List IVal)),
      (∀ k, ValTy.checkList g.imp.exports[(a k).1].ty.params (a k).2 = true) →
      (g.sessInfU a out ∈ (g.toComp.denUD (impSemD P)).inf ↔
        g'.sessInfU (castStream len a) out ∈ (g'.toComp.denUD (impSemD P)).inf)

/-! ## The hypotheses at a deterministic profile -/

/-- **A link at `profile o`, as the theorems use it**: the exporter meets the IR interface
(finite plays, divergence, infinite sessions), is deterministic, and meets the reference
interface with divergence; the link meets `LinkOk`. -/
structure ProfOk (o : GrowOracle) (g : LinkedG) : Prop where
  adeq : g.exp.Adeq (profile o)
  adeqD : g.exp.AdeqD (profile o)
  adeqI : g.exp.AdeqI (profile o)
  det : g.exp.Det (profile o)
  ref : g.exp.RefAdeqUXD (profile o)
  link : g.LinkOk

end LinkedG

/-- **One more importer on a chain with a simple base, as the theorems use it**: the hypotheses
of `LinkedN.sessDivs_eq_refDivs` (the base under the hypotheses of `Simple.expSpec_refAdeqU`,
the links meeting `ChainOkR`, the last link meeting `LinkOk`). -/
structure LinkedN.ExtOk (n : LinkedN) (Ib : ScalarInstance) (Is : List ScalarInstance)
    (b : SimpleI) (w : List Nat) : Prop where
  good : n.base.Good
  inst : n.base.Inst
  isInst : n.base.mod.IsInst Ib
  split : Linked2.ModSplitOk n.base.mod.mod
  names : ∀ x ∈ n.base.exports, ∀ m, x.name ≠ tag "t" m
  chain : ChainOkR (Simple.expSpec n.base Ib) n.links Is
  link : (LinkedG.mk (n.spec Ib Is) b w).LinkOk

end Silmaril.Wasm.Component.Reference

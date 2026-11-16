module

public import Silmaril.Wasm.Component.Reference.LinkedSessionObs.Defs
public import Silmaril.Wasm.Component.Reference.LinkedSessionAdeq.Thms
public import Silmaril.Wasm.Component.Reference.LinkedSessionDivInv.Thms
public import Silmaril.Games.Abstract.StratSession.Thms
import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionObs.Prod

/-!
# Linked components as session play objects: theorems

**Scope.** `Linked2` only: the import-free exporter A answering every import of the importer B
through the canonical ABI, under `Linked2.Adequate` (exporter `Good` and `Inst`; importer `Good`,
`Inst`, `Arity` and `FloatFree`; `WireTy`, `NamesOk`, `WireNodup`; `SplitOk`). The determinism
facts, the injection and the infinite plays are at the deterministic profiles `profile o`; the
finite agreement holds at every profile. The reference component is `l.toRef` on `core3P P`
under `linkHost impl`; every statement about the reference machine holds under every host.

**The triple** (`Linked2.compTripleS P l Ie Ii`, from `Linked2.SessSpec` and `Linked2.RoundDiv`,
not from `Comp.den`) has no plain traps (`Linked2.noPlainTrap_compTripleS`). At `profile o` one
`SessSpec` round is a function of the two stores and the call (`Linked2.round_det`: the outcome
and **both** end stores agree), so the triple is store-deterministic
(`Linked2.storeDet_compTripleS`). This holds also at a trap of A inside one of B's import calls:
B's Proponent moves are unique (`strategy_deterministic`), A's answer to each import call is
unique (the host-free Core run to a result is, `result_unique`), so the import calls, A's
store after each and B's final store are determined. No extra hypothesis is needed.

**Finite agreement** (`Linked2.pubPlays_compSession`, every profile): the plays of
`l.toComp.den (impSem P)` at `sigU` are exactly the plays of `Linked2.compSession P l` whose
questions are in range, read at `sigU` (`sessMove`). Through #726's shape and ill-typed-call
theorems (`Linked2.den_shape`, `Linked2.den_filter_iff`) and #724's `Linked2.sessIR_iff`.

**The injection** (`Linked2.compSession_inj`, at `profile o`, every component choice profile):

`Linked2.RefSessEquivD (profile o) prof l l' ↔ Linked2.SameTypes l l' ∧ Linked2.compSession (profile o) l = Linked2.compSession (profile o) l'`,

an equality of `DStrategy`s (finite plays, divergence and infinite plays), through
`StratSession.threadS_eq_iff`. The divergence clause of `RefSessEquivD` (on reference runs) is
moved to the specification by #733's `Linked2.RefSessEquivD.iff_sessDivs`
(`Linked2.sessDivs_eq_refDivs`), and the terminating clause by #712's `Linked2.sessObs_eq`.

**Infinite plays** (`Linked2.mem_inf_compSession`, `Linked2.sessInf_iff`, at `profile o`): the
infinite plays are the coherent infinite sequences of terminating rounds (no productive streams:
chatter is the divergence of one round); for typed calls these are the streams of calls whose
every finite prefix is a resumable reference session behaviour.

**Productive executions** (`Linked2.RefSessProd`, explicit streams of reference
configurations):

* prefix closure (`Linked2.RefSessProd.prefix`, every profile);
* the converse from store determinism (`Linked2.refSessProd_of_prefix_of_storeDet`; at `profile o`,
  `Linked2.refSessProd_iff_prefix`): the stores of the prefixes cohere, and the reference
  configurations are built forward one linked call at a time by #712's forward runs;
* `Linked2.refSessProd_iff_infRounds`, `Linked2.refSessProd_iff_inf`: productive executions are
  coherent rounds of the triple and infinite plays of `compSession`;
* `Linked2.RefSessEquivFull.iff_refSessEquivD` and `Linked2.compSession_inj_full`: at
  `profile o` the full equivalence (terminating outcomes, quiescent divergence and productive
  executions, all on reference runs) is `RefSessEquivD`, hence equality of session objects.

**Not claimed.**

* The relation of `Linked2.compSession` to the H2 owner's `linkS` of the two instance triples
  (`instTripleS`, #673; `comp_threadS`, #706): those triples are at the core interfaces, and the
  canonical-ABI lift and lower between them and the component interface are not composed here.
* Host observations: they exist only in parents passing host imports to B (`linkedHRef`-style);
  within `Linked2`, `l.toRef` has no host imports and `linkHost impl` is never called.
* n-ary and nested components wait on the H2 owner's `DStrategy.pair`/`atSizes`.
* Contextual full abstraction (the observer is a host calling exports in sequence).
* The parser from bytes to these components, and F6, are pending.
* A trapped call resumes from `resumeCfg`; REF itself locks the store down.

Proofs: `Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionObs.{Triple, Plays, Inj, Prod}`.
-/

public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Games.Abstract.StratThread (StoreDet InfRounds)
open Silmaril.Games.Abstract.StratSession (NoPlainTrap threadS sroundsPlay)
open Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance

variable {P : Profile} {prof : ProfileKind} {l : Linked2} {Ie Ii : SInst}

/-! ## The triple -/

/-- **Every trap keeps both stores**: the linked triple has no plain traps. -/
theorem Linked2.noPlainTrap_compTripleS : NoPlainTrap (Linked2.compTripleS P l Ie Ii) :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionObs.noPlainTrap_compTripleS

/-- **A linked session round is functional** at the deterministic profiles: from the same stores,
the same call has the same outcome and the same end stores of both instances. -/
theorem Linked2.round_det (o : GrowOracle)
    {u π u₁ π₁ u₂ π₂ : Silmaril.Wasm.Execution.Core.Store Nat}
    {j : Fin l.imp.exports.length} {vs : List IVal} {o₁ o₂ : Option (List IVal)}
    (h₁ : Linked2.SessSpec (profile o) l Ie Ii u π [(j, vs)] [o₁] u₁ π₁)
    (h₂ : Linked2.SessSpec (profile o) l Ie Ii u π [(j, vs)] [o₂] u₂ π₂) :
    o₁ = o₂ ∧ u₁ = u₂ ∧ π₁ = π₂ :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionObs.round_det h₁ h₂

/-- **Store determinism** of the linked triple at the deterministic profiles. -/
theorem Linked2.storeDet_compTripleS (o : GrowOracle) :
    StoreDet (Linked2.compTripleS (profile o) l Ie Ii) :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionObs.storeDet_compTripleS

/-- The session object is the threading of the triple of the instances. -/
theorem Linked2.compSession_eq (hIe : l.exp.mod.IsInst Ie) (hIi : l.imp.mod.IsInst Ii) :
    Linked2.compSession P l = threadS (Linked2.compTripleS P l Ie Ii) (Ie.store, Ii.store) :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionObs.compSession_eq hIe hIi

/-! ## Finite agreement -/

/-- **The IR plays are the in-range plays of the session object** (every profile). -/
theorem Linked2.pubPlays_compSession (P : Profile) (l : Linked2) (hl : l.Adequate) :
    pubPlays (l.toComp.den (impSem P)) =
      {q | ∃ p ∈ (Linked2.compSession P l).toStrategy, AskedIn l.imp.exports.length p ∧
        p.map sessMove = q} :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionObs.pubPlays_compSession P l hl

/-- Linked components with the same export count and equal session objects have the same IR
plays. -/
theorem Linked2.compSession_eq_pubPlays {l l' : Linked2} (hl : l.Adequate) (hl' : l'.Adequate)
    (len : l.imp.exports.length = l'.imp.exports.length)
    (h : Linked2.compSession P l = Linked2.compSession P l') :
    pubPlays (l.toComp.den (impSem P)) = pubPlays (l'.toComp.den (impSem P)) := by
  rw [Linked2.pubPlays_compSession P l hl, Linked2.pubPlays_compSession P l' hl', h, len]

/-! ## The injection -/

/-- **The injection of adequate linked components into session objects** (deterministic
profiles, every component choice profile): the reference-defined resumable-session equivalence
with quiet divergence is equality of export types and of session objects, as `DStrategy`s. -/
theorem Linked2.compSession_inj (o : GrowOracle) (prof : ProfileKind) {l l' : Linked2}
    (hl : l.Adequate) (hl' : l'.Adequate) :
    Linked2.RefSessEquivD (profile o) prof l l' ↔
      Linked2.SameTypes l l' ∧
        Linked2.compSession (profile o) l = Linked2.compSession (profile o) l' :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionObs.compSession_inj o prof hl hl'

/-! ## Infinite plays -/

/-- **The infinite plays of the session object**: the plays of coherent infinite sequences of
terminating rounds. -/
theorem Linked2.mem_inf_compSession (o : GrowOracle) (hIe : l.exp.mod.IsInst Ie)
    (hIi : l.imp.mod.IsInst Ii) {J : Set (List (Move (sigN 0) sessSig))} :
    J ∈ (Linked2.compSession (profile o) l).inf ↔
      ∃ a r s, InfRounds (Linked2.compTripleS (profile o) l Ie Ii) (Ie.store, Ii.store) a r s ∧
        J = sroundsPlay a r :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionObs.mem_inf_compSession o hIe hIi

/-- **Infinite typed sessions are reference sessions with infinitely many terminating calls**:
the infinite play of the typed calls `a` answered by `out` is an infinite play of the session
object iff every finite prefix is a resumable reference session behaviour. -/
theorem Linked2.sessInf_iff (o : GrowOracle) (prof : ProfileKind) (hl : l.Adequate)
    (a : ℕ → Fin l.imp.exports.length × List IVal) (out : ℕ → Option (List IVal))
    (ht : ∀ k, ValTy.checkList l.imp.exports[(a k).1].ty.params (a k).2 = true) {σ : Type}
    (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P (profile o)) σ) (h₀ : σ) :
    sroundsPlay (fun k => (((a k).1 : Nat), Payload.vals (a k).2))
        (fun k => ([], outAns (out k))) ∈ (Linked2.compSession (profile o) l).inf ↔
      ∀ k, refOuts (streamTake out k) ∈ Linked2.sessObs prof l impl h₀ (streamTake a k) :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionObs.sessInf_iff o prof hl a out ht impl h₀

/-! ## Productive executions -/

/-- **Prefix closure** (every profile): a productive execution gives every finite prefix as a
resumable reference session behaviour. -/
theorem Linked2.RefSessProd.prefix {σ : Type}
    {impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ} {h₀ : σ}
    {a : ℕ → Fin l.imp.exports.length × List IVal} {out : ℕ → Option (List IVal)}
    (h : Linked2.RefSessProd P prof l impl h₀ a out) (n : ℕ) :
    refOuts (streamTake out n) ∈ Linked2.sessObs prof l impl h₀ (streamTake a n) :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionObs.refSessProd_prefixL h n

/-- **The converse of prefix closure, under store determinism**: if the linked triple is
store-deterministic and every finite prefix of the typed calls `a` with outcomes `out` is a
session behaviour, there is a coherent productive execution. -/
theorem Linked2.refSessProd_of_prefix_of_storeDet (hl : l.Adequate)
    (hdet : ∀ Ie Ii, l.exp.mod.IsInst Ie → l.imp.mod.IsInst Ii →
      StoreDet (Linked2.compTripleS P l Ie Ii))
    (a : ℕ → Fin l.imp.exports.length × List IVal) (out : ℕ → Option (List IVal))
    (ht : ∀ k, ValTy.checkList l.imp.exports[(a k).1].ty.params (a k).2 = true) {σ : Type}
    (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ) (h₀ : σ)
    (h : ∀ k, refOuts (streamTake out k) ∈ Linked2.sessObs prof l impl h₀ (streamTake a k)) :
    Linked2.RefSessProd P prof l impl h₀ a out :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionObs.refSessProd_of_prefixL prof hl hdet
    a out ht impl h₀ h

/-- **Productive executions are their finite prefixes** (deterministic profiles). -/
theorem Linked2.refSessProd_iff_prefix (o : GrowOracle) (hl : l.Adequate)
    (a : ℕ → Fin l.imp.exports.length × List IVal) (out : ℕ → Option (List IVal))
    (ht : ∀ k, ValTy.checkList l.imp.exports[(a k).1].ty.params (a k).2 = true) {σ : Type}
    (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P (profile o)) σ) (h₀ : σ) :
    Linked2.RefSessProd (profile o) prof l impl h₀ a out ↔
      ∀ k, refOuts (streamTake out k) ∈ Linked2.sessObs prof l impl h₀ (streamTake a k) :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionObs.refSessProd_iff_prefixL o prof hl a
    out ht impl h₀

/-- **Productive executions are coherent rounds of the linked triple** (deterministic
profiles). -/
theorem Linked2.refSessProd_iff_infRounds (o : GrowOracle) (hl : l.Adequate)
    (hIe : l.exp.mod.IsInst Ie) (hIi : l.imp.mod.IsInst Ii)
    (a : ℕ → Fin l.imp.exports.length × List IVal) (out : ℕ → Option (List IVal))
    (ht : ∀ k, ValTy.checkList l.imp.exports[(a k).1].ty.params (a k).2 = true) {σ : Type}
    (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P (profile o)) σ) (h₀ : σ) :
    Linked2.RefSessProd (profile o) prof l impl h₀ a out ↔
      ∃ s, InfRounds (Linked2.compTripleS (profile o) l Ie Ii) (Ie.store, Ii.store)
        (fun k => (((a k).1 : Nat), Payload.vals (a k).2)) (fun k => ([], outAns (out k))) s :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionObs.refSessProd_iff_infRoundsL o prof hl
    hIe hIi a out ht impl h₀

/-- **Productive executions are infinite plays of the session object** (deterministic
profiles). -/
theorem Linked2.refSessProd_iff_inf (o : GrowOracle) (hl : l.Adequate)
    (a : ℕ → Fin l.imp.exports.length × List IVal) (out : ℕ → Option (List IVal))
    (ht : ∀ k, ValTy.checkList l.imp.exports[(a k).1].ty.params (a k).2 = true) {σ : Type}
    (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P (profile o)) σ) (h₀ : σ) :
    Linked2.RefSessProd (profile o) prof l impl h₀ a out ↔
      sroundsPlay (fun k => (((a k).1 : Nat), Payload.vals (a k).2))
        (fun k => ([], outAns (out k))) ∈ (Linked2.compSession (profile o) l).inf :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionObs.refSessProd_iff_infL o prof hl a out
    ht impl h₀

/-- **At the deterministic profiles the full equivalence is `RefSessEquivD`**: the productive
clause follows from the terminating outcomes of the prefixes. -/
theorem Linked2.RefSessEquivFull.iff_refSessEquivD (o : GrowOracle) {l l' : Linked2}
    (hl : l.Adequate) (hl' : l'.Adequate) :
    Linked2.RefSessEquivFull (profile o) prof l l' ↔ Linked2.RefSessEquivD (profile o) prof l l' :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionObs.refSessEquivFull_iffL o prof hl hl'

/-- **The full-strategy injection** (deterministic profiles, every component choice profile):
for adequate linked components, the full reference-session equivalence (terminating outcomes,
quiescent divergence and productive executions, all on reference-machine runs) is equality of
export types and of session objects. -/
theorem Linked2.compSession_inj_full (o : GrowOracle) {l l' : Linked2} (hl : l.Adequate)
    (hl' : l'.Adequate) :
    Linked2.RefSessEquivFull (profile o) prof l l' ↔
      Linked2.SameTypes l l' ∧
        Linked2.compSession (profile o) l = Linked2.compSession (profile o) l' :=
  (Linked2.RefSessEquivFull.iff_refSessEquivD o hl hl').trans
    (Linked2.compSession_inj o prof hl hl')

end Silmaril.Wasm.Component.Reference

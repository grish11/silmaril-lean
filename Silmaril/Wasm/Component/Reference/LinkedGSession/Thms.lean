module

public import Silmaril.Wasm.Component.Reference.LinkedGSession.Defs
public import Silmaril.Wasm.Component.Reference.LinkedGInf.Thms
public import Silmaril.Games.Abstract.StratSession.Thms
import Silmaril.Proofs.Wasm.Component.Reference.LinkedGSession.Main

/-!
# Exporters, linked components and chains as session play objects: theorems

**Scope.** An exporter `ExpSpec` at a profile `P`; a linked component `g : LinkedG` at
`profile o` under `LinkedG.ProfOk o g`; one more importer on a chain with a simple base
(`⟨n.spec Ib Is, b, w⟩`, under `LinkedN.ExtOk`). The reference machine is over
`core3P (profile o)` under `linkHost impl`, every host and every component choice profile. This
mirrors #746's `Linked2.compTripleS`, `storeDet_compTripleS`, `compSession_inj_full` and
`refSessProd_iff_inf` (`LinkedSessionObs.Thms`), stated once over the exporter interface.

**Proved (public, below).**

1. **The triple of an exporter** (`ExpSpec.sessTripleS P e`, from `Step` and `DivStep`) has no
   plain traps (`ExpSpec.noPlainTrap_sessTripleS`) and is store-deterministic for a
   deterministic exporter (`ExpSpec.storeDet_sessTripleS`, from `ExpSpec.Det`).
2. **Equal session objects of exporters** (`ExpSpec.session_eq_iff`): for deterministic
   exporters with the same typed questions, `e.session P = e'.session P` iff they have the same
   typed sessions from their initial states (`RunEq`) and the same divergences after them
   (`DivEq`), through `StratSession.threadS_eq_iff`; the bisimulation relates the end states of
   one typed session.
3. **Infinite plays of an exporter** (`ExpSpec.mem_inf_session`,
   `ExpSpec.mem_inf_session_iff`): the coherent infinite sequences of rounds; the play of a
   typed stream of rounds is one iff the stream is a run from the initial state.
4. **Linked components** (`LinkedG.compTripleS P g Ii := (g.toExp Ii).sessTripleS P`, the state
   the importer's store with the exporter's state): `LinkedG.storeDet_compTripleS` (from
   `LinkedG.toExp_det`), `LinkedG.compSession_eq`, and
   **`LinkedG.compSession_inj_full`**: at `profile o`, for links meeting `ProfOk`,

   `LinkedG.RefSessEquivFull (profile o) prof g g' ↔ LinkedG.SameTypes g g' ∧ LinkedG.compSession (profile o) g = LinkedG.compSession (profile o) g'`,

   an equality of `DStrategy`s (finite plays, divergences and infinite plays). The reference
   side goes through #912's `LinkedG.refSessEquivFull_iff` (to the typed IR projections); the
   typed IR projections are the typed sessions and divergences of `g.toExp Ii`
   (`LinkedG.toExp_adeq`, `LinkedG.toExp_adeqD_profile`), so item 2 applies; the infinite IR
   projection follows from the finite one by determinism.
   **`LinkedG.mem_inf_compSession`**: the infinite play of a typed call stream is one of the
   session object iff it is a productive execution on the reference machine.
5. **Chains**: **`LinkedN.compSession_inj_full`**, `LinkedN.mem_inf_compSession` for one more
   importer on a chain with a simple base (through `LinkedN.ExtOk.profOk`).

**Ill-typed questions.** The session object traps every ill-typed question at once, the state
unchanged, on the canonical side, as `Linked2.compFin` does; the injection is on typed
observations, as `RefSessEquivFull` is. The IR traps ill-typed calls at once as well
(`LinkedG.den_filter_iff`, in `LinkedGFilter`), and the finite IR plays are the in-range plays of
the session object (`LinkedG.pubPlays_compSession`, `LinkedGFilter`); the session object is not
claimed to agree with the divergences and infinite plays of `g.toComp.denUD` on ill-typed
calls.

**Deviations from #746.**

* The state of the triple is `(u, π)`, the importer's store and the exporter's state (the state
  of `LinkedG.toExp`), not `Linked2`'s `(π, u)`.
* There is no `LinkedG.RefSessEquivD`; the injection is stated for `RefSessEquivFull` directly,
  under the bundled hypotheses `LinkedG.ProfOk o`.
* `round_det` is `LinkedG.toExp_det` (#909), on `g.toExp Ii`'s steps.

**Not claimed.**

* The finite agreement with the whole IR strategy (`Linked2.pubPlays_compSession`) is not proved
  in this topic; it is `LinkedG.pubPlays_compSession`, in `LinkedGFilter`.
* Nondeterministic profiles; the relation to the H2 owner's `linkS`; host observations of
  parents passing host imports to the importer; the parser from bytes; F6.

Proofs: `Silmaril.Proofs.Wasm.Component.Reference.LinkedGSession.{Exp, Main}`.
-/

public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Games.Abstract.StratThread (StoreDet InfRounds)
open Silmaril.Games.Abstract.StratSession (NoPlainTrap threadS sroundsPlay)
open Silmaril.Wasm.Component
open Silmaril.Wasm.Component.Canon (HostImpl)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Game (ScalarInstance)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

local notation "IVal" => Silmaril.Wasm.Component.Val

/-! ## An exporter -/

namespace ExpSpec

variable {P : Profile} {e e' : ExpSpec}

/-- **Every trap keeps the state**: the triple of an exporter has no plain traps (proved). -/
theorem noPlainTrap_sessTripleS : NoPlainTrap (e.sessTripleS P) :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGSession.noPlainTrap_sessTripleS

/-- **Store determinism** of the triple of a deterministic exporter (proved). -/
theorem storeDet_sessTripleS (hd : e.Det P) : StoreDet (e.sessTripleS P) :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGSession.storeDet_sessTripleS hd

/-- **Equal session objects of deterministic exporters with the same typed questions** are the
same typed sessions and divergences from the initial states (proved). -/
theorem session_eq_iff (hd : e.Det P) (hd' : e'.Det P) (hq : e.SameQ e') :
    e.session P = e'.session P ↔ e.RunEq P e' ∧ e.DivEq P e' :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGSession.session_eq_iff hd hd' hq

/-- **The infinite plays of the session of a deterministic exporter** are the plays of coherent
infinite sequences of rounds (proved). -/
theorem mem_inf_session (hd : e.Det P) {J : Set (List (Move (sigN 0) sessSig))} :
    J ∈ (e.session P).inf ↔
      ∃ a r s, InfRounds (e.sessTripleS P) e.init a r s ∧ J = sroundsPlay a r :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGSession.mem_inf_session hd

/-- **The infinite play of a typed stream of rounds is one of the session object iff the stream
is a run** of the exporter from its initial state (proved, deterministic exporter). -/
theorem mem_inf_session_iff (hd : e.Det P) (r : ℕ → URound) (ht : ∀ k, e.Typed (r k)) :
    sroundsPlay (fun k => (r k).1) (fun k => (([] : List (Call (sigN 0))), sumAns (r k).2)) ∈
        (e.session P).inf ↔
      ∃ S : ℕ → e.St, S 0 = e.init ∧ ∀ k, e.Step P (S k) (r k) (S (k + 1)) :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGSession.mem_inf_session_iff hd r ht

end ExpSpec

/-! ## Linked components -/

namespace LinkedG

variable {P : Profile} {o : GrowOracle} {prof : ProfileKind} {g : LinkedG} {Ii : ScalarInstance}

/-- **Every trap keeps both states**: the linked triple has no plain traps (proved). -/
theorem noPlainTrap_compTripleS : NoPlainTrap (LinkedG.compTripleS P g Ii) :=
  ExpSpec.noPlainTrap_sessTripleS

/-- **Store determinism** of the linked triple on a deterministic exporter (proved,
`profile o`). -/
theorem storeDet_compTripleS (hd : g.exp.Det (profile o)) :
    StoreDet (LinkedG.compTripleS (profile o) g Ii) :=
  ExpSpec.storeDet_sessTripleS (LinkedG.toExp_det hd)

/-- The session object is the threading of the triple of the importer's instance (proved). -/
theorem compSession_eq (hI : g.imp.mod.IsInst Ii) :
    LinkedG.compSession P g = threadS (LinkedG.compTripleS P g Ii) (Ii.store, g.exp.init) :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGSession.compSession_eq hI

/-- **The full injection of linked components into session objects** (proved, `profile o`,
every component choice profile): for links meeting `ProfOk`, the full resumable-session
equivalence on the reference machine (terminating outcomes, quiescent divergences and productive
executions, every host) is equality of export types and of session objects, as `DStrategy`s. -/
theorem compSession_inj_full {g' : LinkedG} (hg : g.ProfOk o) (hg' : g'.ProfOk o) :
    LinkedG.RefSessEquivFull (profile o) prof g g' ↔
      LinkedG.SameTypes g g' ∧
        LinkedG.compSession (profile o) g = LinkedG.compSession (profile o) g' :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGSession.compSession_inj_full hg hg'

/-- **The infinite plays of typed call streams are the productive executions** (proved,
`profile o`, every component choice profile, under every host). -/
theorem mem_inf_compSession (hg : g.ProfOk o) (a : ℕ → Fin g.imp.exports.length × List IVal)
    (out : ℕ → Option (List IVal))
    (ht : ∀ k, ValTy.checkList g.imp.exports[(a k).1].ty.params (a k).2 = true) {σ : Type}
    (impl : HostImpl (core3P (profile o)) σ) (h₀ : σ) :
    sroundsPlay (fun k => (((a k).1 : Nat), Payload.vals (a k).2))
        (fun k => (([] : List (Call (sigN 0))), outAns (out k))) ∈
        (LinkedG.compSession (profile o) g).inf ↔
      LinkedG.RefSessProd (profile o) prof g impl h₀ a out :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGSession.mem_inf_compSession hg a out ht impl h₀

end LinkedG

/-! ## Chains -/

namespace LinkedN

variable {o : GrowOracle} {prof : ProfileKind} {n : LinkedN} {Ib : ScalarInstance}
  {Is : List ScalarInstance} {b : SimpleI} {w : List Nat}

/-- **The full injection for chains** (proved, `profile o`, every component choice profile): for
one more importer on each of two chains with simple bases, the full resumable-session
equivalence on the reference machine is equality of export types and of session objects. -/
theorem compSession_inj_full {n' : LinkedN} {Ib' : ScalarInstance} {Is' : List ScalarInstance}
    {b' : SimpleI} {w' : List Nat} (h : n.ExtOk Ib Is b w) (h' : n'.ExtOk Ib' Is' b' w') :
    LinkedG.RefSessEquivFull (profile o) prof ⟨n.spec Ib Is, b, w⟩ ⟨n'.spec Ib' Is', b', w'⟩ ↔
      LinkedG.SameTypes ⟨n.spec Ib Is, b, w⟩ ⟨n'.spec Ib' Is', b', w'⟩ ∧
        LinkedG.compSession (profile o) ⟨n.spec Ib Is, b, w⟩ =
          LinkedG.compSession (profile o) ⟨n'.spec Ib' Is', b', w'⟩ :=
  LinkedG.compSession_inj_full (h.profOk o) (h'.profOk o)

/-- **The infinite plays of one more importer on a chain are its productive executions**
(proved, `profile o`, every component choice profile, under every host, typed calls). -/
theorem mem_inf_compSession (h : n.ExtOk Ib Is b w) (a : ℕ → Fin b.exports.length × List IVal)
    (out : ℕ → Option (List IVal))
    (ht : ∀ k, ValTy.checkList b.exports[(a k).1].ty.params (a k).2 = true) {σ : Type}
    (impl : HostImpl (core3P (profile o)) σ) (h₀ : σ) :
    sroundsPlay (fun k => (((a k).1 : Nat), Payload.vals (a k).2))
        (fun k => (([] : List (Call (sigN 0))), outAns (out k))) ∈
        (LinkedG.compSession (profile o) ⟨n.spec Ib Is, b, w⟩).inf ↔
      LinkedG.RefSessProd (profile o) prof ⟨n.spec Ib Is, b, w⟩ impl h₀ a out :=
  LinkedG.mem_inf_compSession (h.profOk o) a out ht impl h₀

end LinkedN

end Silmaril.Wasm.Component.Reference

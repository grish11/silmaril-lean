module

public import Silmaril.Games.Abstract.StratLegal.Defs

/-!
# Restricting an open play object by a relational host

An open function is observed by a triple `t : ObsTriple E S A B` (`StratObs`): every import
answer is possible in its logs. A relational host `R : HostRel E` (`HostRun`) fixes which
answers come back, which calls diverge, and which calls get no outcome at all. This module
restricts a triple to what running against `R` can show, componentwise:

* `hostRestrict R t`:
  - finished behaviours (of any end, `div` included) whose log `R` allows (`R.Consistent`);
  - pending calls `(c, m)` with `c` allowed and `m` a call that `R` **stalls** on
    (`R.Stalls m`): `R` has no outcome for `m` (`blocked` in `hostObs`) or may diverge at `m`
    (`hostDiv` in `hostObs`). A pending call that `R` answers is not an observation of the closed
    run: the run continues;
  - productive streams whose every answer `R` allows (`hostObsInf R`);
* `guardT Ok t`: the observations at the questions `Ok` only (other questions get none).

**Relation to legal interfaces.** `R.legal m n := R m (.answer n)` is a legality predicate
(`StratLegal`). `StratLegal.restrict R.legal t` keeps every observation with an allowed log, on
the legal interface, and in particular **every** pending call after an allowed prefix. The host
restriction keeps only the pending calls at which `R` stalls. On the legal interface the two
differ exactly by that filter (`StratHost.restrict_hostRestrict`).

**The host as a strategy, and linking.** `hostD R : DStrategy Sig.empty E` is the host with no
imports: its plays are the legal plays of `Sig.empty ↠ E` whose answers `R` allows (`HostOk`),
it diverges after a call at which `R` may diverge, and every limit of its plays is an infinite
play. At a call with no outcome it has no move and does not diverge. `linkT R t` is the closed
triple of `t` linked with `R`, log erased: composing with `hostD R` (`DStrategy.comp`) gives its
play object (`StratHost.comp_hostD_toDStrat`).

Theorems in `Silmaril.Games.Abstract.StratHost.Thms`.
-/

@[expose] public section

namespace Silmaril.Games.Abstract

open Silmaril.Games

universe u

variable {E : Sig.{u}} {S A B : Type u}

namespace HostRel

/-- **`R` stalls at the call `m`**: it has no outcome for `m`, or it may diverge at `m`. -/
def Stalls (R : HostRel E) (m : E.Op) : Prop := (∀ o, ¬ R m o) ∨ R m .diverge

/-- The answers `R` allows, as a legality predicate. -/
def legal (R : HostRel E) : (m : E.Op) → E.Ar m → Prop := fun m n => R m (.answer n)

end HostRel

namespace StratHost

/-- **The observations at the questions `Ok`.** -/
def guardT (Ok : S → A → Prop) (t : ObsTriple E S A B) : ObsTriple E S A B :=
  (fun s a => {x | Ok s a ∧ x ∈ t.1 s a}, fun s a => {x | Ok s a ∧ x ∈ t.2.1 s a},
    fun s a => {ω | Ok s a ∧ ω ∈ t.2.2 s a})

/-- **The host restriction of a triple**: allowed logs, pending calls at which the host stalls,
and allowed productive streams. -/
def hostRestrict (R : HostRel E) (t : ObsTriple E S A B) : ObsTriple E S A B :=
  (fun s a => {x | x ∈ t.1 s a ∧ R.Consistent x.1},
    fun s a => {x | x ∈ t.2.1 s a ∧ R.Consistent x.1 ∧ R.Stalls x.2},
    hostObsInf R t.2.2)

/-! ## The host as a strategy, and linking -/

/-- Every answer in a play of the host game is allowed by `R`. -/
def HostOk (R : HostRel E) (s : List (Move Sig.empty.{u} E)) : Prop :=
  ∀ m n, (.inr (.ans m n) : Move Sig.empty E) ∈ s → R m (.answer n)

/-- The finite plays of the host: the legal plays with allowed answers. -/
def hostS (R : HostRel E) : Strategy Sig.empty.{u} E where
  plays := {s | Legal s ∧ HostOk R s}
  nil_mem := ⟨Legal.nil, fun _ _ h => nomatch h⟩
  legal h := h.1
  of_prefix := fun ⟨hl, ho⟩ hst => ⟨hl.of_prefix hst, fun m n h => ho m n (hst.subset h)⟩
  receptive := fun ⟨_, ho⟩ hx hxy hO => ⟨⟨_, hx.append (.single hxy)⟩, fun m n h =>
    (List.mem_append.1 h).elim (ho m n) fun h => by cases List.mem_singleton.1 h; exact hO.elim⟩

/-- **The host `R` as a strategy without imports**: it answers each call `m` of `E` with an
answer `R` allows, diverges at the calls where `R` may diverge, and is quiescent (no move, no
divergence) at the calls `R` has no outcome for. Every limit of its plays is an infinite play. -/
def hostD (R : HostRel E) : DStrategy Sig.empty.{u} E where
  toStrategy := hostS R
  div := {s | s ∈ hostS R ∧ ∃ m, Path .idle s (.run m) ∧ R m .diverge}
  inf := {I | IsInfPlay I ∧ I ⊆ (hostS R).plays}
  div_mem h := h.1
  div_run := fun ⟨_, m, h, _⟩ => ⟨m, h⟩
  inf_isInf h := h.1
  inf_sub h := h.2

/-- **Linking `t` with the host `R`, interaction hidden**: a closed triple. A behaviour of `t`
whose log `R` allows is a behaviour with its log erased; it diverges at a call prefix of `t`
(`satP`, so including calls forced by behaviours and streams) at which `R` may diverge, and after
an allowed productive stream (infinitely many hidden host interactions). A call prefix at which
`R` has no outcome gives nothing: the closed run is quiescent. No pending call, no stream. -/
def linkT (R : HostRel E) (t : ObsTriple E S A B) : ObsTriple Sig.empty.{u} S A B :=
  (fun s a => {x | (∃ c, (c, x.2) ∈ (hostRestrict R t).1 s a) ∨ (x.2 = .div ∧
      ((∃ c m, (c, m) ∈ (hostRestrict R (StratObs.sat t)).2.1 s a ∧ R m .diverge) ∨
        ((hostRestrict R t).2.2 s a).Nonempty))},
    fun _ _ => ∅, fun _ _ => ∅)

end StratHost

end Silmaril.Games.Abstract

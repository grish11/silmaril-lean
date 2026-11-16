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

end StratHost

end Silmaril.Games.Abstract

module

public import Silmaril.Games.Abstract.SessionHost.Defs

/-!
# Sessions with host imports: a counterexample (definitions)

`SessionHost.pair_comp_threadS` identifies the composite of the host beside copycat and the
session of `t` with the session of the linked triple `hostLinkS R t`, assuming that the linked
triple is store-deterministic (`StoreDet (hostLinkS R t)`). This topic gives a component and a
host for which that hypothesis fails, the component itself being store-deterministic
(`StoreDet t`) and even deterministic given answers (`AFun.Det t.1`).

* **The host** `pickHost` serves the one host import of `pickSig`, a call `()` answered by a
  number, with any number.
* **The component** `boundHostComp` is the bounding client of
  `SessionLinkCex.boundClient` with its call made on the host import: its first round asks the
  host for some `n` and keeps the bound `n` on its later rounds (a countdown from `some n`). Its
  component imports `F` are never called.

The host call is hidden by linking, so the linked triple has every finite number of rounds from
`none` but the bound is a hidden host answer: the linked session plays `unitRounds`, infinitely
many rounds without calls, and no interaction of the host beside copycat with the session of the
component does.

Theorems in `Silmaril.Games.Abstract.SessionHostCex.Thms`.
-/

@[expose] public section

namespace Silmaril.Games.Abstract.SessionHostCex

open Silmaril.Games Silmaril.Games.Abstract.StratObs Silmaril.Games.Abstract.StratThread

variable {F : Sig.{0}}

/-- One host import `()`, answered by a number. -/
def pickSig : Sig.{0} := ⟨Unit, fun _ => ℕ⟩

/-- The host answering the host import with any number. -/
def pickHost : HostRel pickSig := fun _ o => ∃ n, o = .answer n

/-- The host call answered `n`. -/
def pickCall (n : ℕ) : Call (pickSig ⊕ₛ F) := ⟨.inl (), n⟩

/-- A component whose first round asks the host for some `n` and keeps `n` as the bound on its
later rounds, which make no calls. -/
def boundHostComp : ObsTriple (pickSig ⊕ₛ F) (Option ℕ) Unit (Unit ⊕ Unit) :=
  (fun s _ => {e | (s = none ∧ ∃ n, e = ([pickCall n], .ret (.inl ()) (some n))) ∨
      ∃ n, s = some (n + 1) ∧ e = ([], .ret (.inl ()) (some n))},
    fun _ _ => ∅, fun _ _ => ∅)

/-- The infinite play of rounds without calls answering `()`. -/
def unitRounds : Set (List (Move F (sig1 Unit Unit))) :=
  StratSession.sroundsPlay (fun _ => ()) fun _ => ([], .inl ())

end Silmaril.Games.Abstract.SessionHostCex

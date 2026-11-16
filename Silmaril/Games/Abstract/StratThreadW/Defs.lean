module

public import Silmaril.Games.Abstract.StratThread.Thms
public import Silmaril.Games.Abstract.StratSession.Defs

/-!
# Threading with coherent execution witnesses

`StratThread.threadT t s₀` takes its infinite plays completing infinitely many rounds as a
*trace limit*: every member extends to a member whose run ends idle at *some* store. For a
nondeterministic source the stores of these runs need not extend one another, so such an
infinite play need not be executable (`StratThread.not_coherent`).

**The witness semantics.** `threadW t s₀ : DStrategy E (sig1 A B)` has the finite plays and the
divergent plays of `threadT t s₀`, and its infinite plays are exactly (`winfs`):

* finitely many completed rounds `Rounds t s₀ rs s`, then a question `a` and the calls of a
  productive stream `ω ∈ t.2.2 s a` (`streamPlay (roundsMoves rs) a ω`); or
* the play `roundsPlay a r` of a coherent infinite sequence of rounds
  `InfRounds t s₀ a r s`, with an explicit store sequence `s : ℕ → S` through all rounds.

Each such play is an infinite play of `threadT t s₀` (`winfs_subset`), which gives the
`DStrategy` fields. For store-deterministic triples the two semantics agree; for the countdown
triple of `StratThread.not_coherent` they differ (`Silmaril.Games.Abstract.StratThreadW.Thms`).

**Sessions.** `threadSW t s₀` is the witness semantics of a store-retaining triple
`t : ObsTriple E S A (B ⊕ PUnit)`, relabelled along `StratSession.merge` exactly as
`StratSession.threadS t s₀ = relabel (threadT t s₀)`.

Theorems in `Silmaril.Games.Abstract.StratThreadW.Thms`.
-/

@[expose] public section

namespace Silmaril.Games.Abstract.StratThreadW

open Silmaril.Games Silmaril.Games.Abstract.StratObs Silmaril.Games.Abstract.StratThread

universe u

variable {E : Sig.{u}} {S A B : Type u}

/-- **The witnessed infinite plays**: a productive stream after finitely many completed rounds,
or the play of a coherent infinite sequence of rounds with an explicit store sequence. -/
def winfs (t : ObsTriple E S A B) (s₀ : S) : Set (Set (List (Move E (sig1 A B)))) :=
  {I | (∃ rs s a ω, Rounds t s₀ rs s ∧ ω ∈ t.2.2 s a ∧ I = streamPlay (roundsMoves rs) a ω) ∨
    ∃ a r s, InfRounds t s₀ a r s ∧ I = roundsPlay a r}

/-- Every witnessed infinite play is an infinite play of the trace-limit threading. -/
theorem winfs_subset (t : ObsTriple E S A B) (s₀ : S) : winfs t s₀ ⊆ (threadT t s₀).inf := by
  rintro I (⟨rs, s, a, ω, hrs, hω, rfl⟩ | ⟨a, r, s, h, rfl⟩)
  exacts [mem_inf.2 ⟨s, hrs, hω⟩, h.mem_inf]

/-- **The threading of a triple from `s₀` with witnessed infinite plays**: the finite and
divergent plays of `threadT t s₀`, and the infinite plays `winfs t s₀`. -/
def threadW (t : ObsTriple E S A B) (s₀ : S) : DStrategy E (sig1 A B) where
  toStrategy := (threadT t s₀).toStrategy
  div := (threadT t s₀).div
  inf := winfs t s₀
  div_mem h := (threadT t s₀).div_mem h
  div_run h := (threadT t s₀).div_run h
  inf_isInf h := (threadT t s₀).inf_isInf (winfs_subset t s₀ h)
  inf_sub h := (threadT t s₀).inf_sub (winfs_subset t s₀ h)

/-- **The session threading of a store-retaining triple with witnessed infinite plays**: the
witness threading relabelled along `merge`, as `threadS` relabels `threadT`. -/
def threadSW (t : ObsTriple E S A (B ⊕ PUnit.{u + 1})) (s₀ : S) : DStrategy E (sig1 A B) :=
  StratSession.relabel (threadW t s₀)

end Silmaril.Games.Abstract.StratThreadW

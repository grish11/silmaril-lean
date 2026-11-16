module

public import Silmaril.Games.Abstract.StratSession.Defs

/-!
# Sessions whose rounds abort on a trap from below: definitions

A session client calls its imports during a round. When an import answers with a trap, Core
Wasm traps the caller at once: the round ends with a trap, and no further import call is made in
it. This module states that property of a store-retaining triple, and the corresponding
property of a strategy, for a lower interface `E` with a predicate `T m n` saying that the answer
`n` to the call `m` is a trap (for a session interface `sig1 A' B'`, `n = .inr ()`; for Wasm host
calls, a result `.trap`).

* `TrapEnd e`: `e` ends a round with a trap: `.ret (.inr ()) s` (a trap keeping the store `s`) or
  a plain `.trap`.
* `TrapAbortsRound T t`: in every finished behaviour of `t` (of any end, including divergence)
  whose call log contains a call answered by a trap, that call is the last one and the behaviour
  ends with a trap; no pending call follows a trapped call; no productive stream receives a
  trap.
* `TrapAbortsBelow T σ`: in every play of `σ : DStrategy E (sig1 A B)`, a trap answer from
  below is followed, if at all, by the trap answer `.inr ()` to the current question.
  `TrapEndsBelow T σ` is the weaker form: the next move is at the upper interface.
-/

@[expose] public section

namespace Silmaril.Games.Abstract.SessionTrap

open Silmaril.Games Silmaril.Games.Abstract.StratObs

universe u

variable {E : Sig.{u}} {S A B : Type u}

/-- **A trap end**: a trap keeping its store, or a plain trap. -/
def TrapEnd : End S (B ⊕ PUnit.{u + 1}) → Prop
  | .ret (.inr _) _ => True
  | .trap => True
  | _ => False

/-- **Every round of `t` aborts at a trap from below**, the trap answers being those satisfying
`T`. -/
structure TrapAbortsRound (T : (m : E.Op) → E.Ar m → Prop)
    (t : ObsTriple E S A (B ⊕ PUnit.{u + 1})) : Prop where
  /-- A behaviour ends at its first trapped call, with a trap. -/
  beh : ∀ s a c m n d e, T m n → (c ++ ⟨m, n⟩ :: d, e) ∈ t.1 s a → d = [] ∧ TrapEnd e
  /-- No pending call after a trapped call. -/
  pend : ∀ s a c m n d m', T m n → (c ++ ⟨m, n⟩ :: d, m') ∉ t.2.1 s a
  /-- No productive stream receives a trap. -/
  inf : ∀ s a ω, ω ∈ t.2.2 s a → ∀ k, ¬ T (ω k).1 (ω k).2

/-- **After a trap from below, the round answers a trap**, if it moves at all. -/
def TrapAbortsBelow {A B : Type u} (T : (m : E.Op) → E.Ar m → Prop)
    (σ : DStrategy E (sig1 A B)) : Prop :=
  ∀ (p : List (Move E (sig1 A B))) (m : E.Op) (n : E.Ar m) (y : Move E (sig1 A B)),
    T m n → p ++ [.inl (.ans m n), y] ∈ σ.toStrategy →
      ∃ a, y = .inr (.ans a (.inr PUnit.unit))

/-- **After a trap from below, the round makes no further call.** -/
def TrapEndsBelow {G : Sig.{u}} (T : (m : E.Op) → E.Ar m → Prop) (σ : DStrategy E G) : Prop :=
  ∀ (p : List (Move E G)) (m : E.Op) (n : E.Ar m) (y : Move E G),
    T m n → p ++ [.inl (.ans m n), y] ∈ σ.toStrategy → ∃ g, y = .inr g

end Silmaril.Games.Abstract.SessionTrap

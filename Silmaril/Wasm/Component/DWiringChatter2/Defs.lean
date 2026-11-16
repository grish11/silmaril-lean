module

public import Silmaril.Wasm.Component.DWiringLaws.Defs

/-!
# Chatter between an environment and the node above it, routed: definitions

`DStrategy.ext e D N = D.comp (extTop e N)`, where `extTop e N` is copycat
beside `N` below `splitH e`. A play `c : List (Move sigU sigU)` of `extTop e N`
has moves at `D`'s upper interface (`.inl`) and at the outer interface
(`.inr`). This module names how those moves are routed to copycat and to `N`.

* `splitQ e q`: `splitH e` sends an outer question `q` with `q.1 < e` to
  copycat (`.inl q`), and any other to `N`, shifted (`.inr (q.1 - e, q.2)`).
* `splitRoute e`: the move of the pairing `(DStrategy.id sigU).pair N`
  corresponding to a move of `extTop e N`. Moves at `D`'s interface are
  unchanged; outer questions and their answers are routed by `splitQ e`.
  The pairing play under a play `c` of `extTop e N` is `c.map (splitRoute e)`
  (`Silmaril.Wasm.Component.DWiringChatter2.Thms`).
* Within the pairing play, the moves at `D`'s interface belong to the round in
  progress (`Split.halves`): to copycat during a round of a question routed to
  copycat (they are the moves passed through to `D`), and to `N` during a round
  of `N` (they are `N`'s calls to `D` and their answers).
* `ExtChatter e I L p`: the shape of hidden chatter between `D` and
  `extTop e N`, in terms of an infinite play `I` of `D` and an infinite play
  `L` of `N`. A finite prefix `s₀` of `D` interacts with a finite play `c₀` of
  `extTop e N` with visible part `p`; there, a round of `N` is in progress and
  copycat's half of the pairing play is a finite copycat play. Afterwards `D`
  and `N` exchange moves forever (`w`, answered by `D` at its upper interface
  and played by `N` at its lower interface), with no visible move: the outer
  moves and copycat are silent.
-/

@[expose] public section

namespace Silmaril.Wasm.Component

open Silmaril.Games

/-- Where `splitH e` sends an outer question: copycat below `e`, else `N`, shifted. -/
def splitQ (e : Nat) (q : sigU.Op) : (sigU ⊕ₛ sigU).Op :=
  if q.1 < e then .inl q else .inr (q.1 - e, q.2)

/-- **The routing of `splitH e`**: a move of `extTop e N` as a move of the
pairing below `splitH e`. Moves at `D`'s interface are unchanged; outer
questions and answers go to copycat (index below `e`) or to `N` (shifted). -/
def splitRoute (e : Nat) : Move sigU sigU → Move sigU (sigU ⊕ₛ sigU)
  | .inl l => .inl l
  | .inr (.ask q) => .inr (.ask (splitQ e q))
  | .inr (.ans q r) =>
    if q.1 < e then .inr (.ans (.inl q) r) else .inr (.ans (.inr (q.1 - e, q.2)) r)

/-- **Hidden chatter between `D` and the node above it, routed.** `I` is an
infinite play of `D` and `L` one of `N`. A prefix `s₀` of `I` interacts with a
legal play `c₀` above `D` with visible part `p`. Routing `c₀` through
`splitH e` and splitting by rounds, a round of `N` is in progress, copycat's half
`u₀` is a copycat play, and `N`'s half `t₀` continues in `L`. After that, `D`
and `N` exchange arbitrarily long `w` (moves of `D`'s upper interface, played
by `N` below) with nothing visible. -/
def ExtChatter {X : Sig.{0}} (e : Nat) (I : Set (List (Move X sigU)))
    (L : Set (List (Move sigU sigU))) (p : List (Move X sigU)) : Prop :=
  ∃ s₀ c₀, Zip s₀ c₀ p ∧ Legal c₀ ∧ Split.side false (c₀.map (splitRoute e)) = true ∧
    (Split.halves false (c₀.map (splitRoute e))).1 ∈ Strategy.id sigU ∧
    ∀ k, ∃ w : List (Ev sigU), k ≤ w.length ∧ s₀ ++ w.map .inr ∈ I ∧
      (Split.halves false (c₀.map (splitRoute e))).2 ++ w.map .inl ∈ L

end Silmaril.Wasm.Component

module

public import Silmaril.Wasm.Component.DWiring.Defs

/-!
# Divergence and infinite plays of divergence-observing wiring: definitions

The predicates in which `Silmaril.Wasm.Component.DWiringLaws.Thms` states the
divergences and infinite plays of `DStrategy.atSizes` and `DStrategy.ext` exactly,
in terms of the strategies being wired:

* `AllCall h`: `h` answers every question by exactly one call (`narrowH`,
  `splitH`). Above a strategy, such a handler makes it move whenever the
  visible play grows.
* `TrapChatter n σ s`: an infinite play of `σ` which, from a position where `σ`
  is running, consists only of trap events below `widenH n` (`IsTrap`), lined
  up with a play of `widenH n` whose visible part is `s`.
* `ThroughBelow h I K` and `ThroughAbove h K J`: an infinite play `I` seen
  through the handler `h` below it, or `K` seen through `h` above it, with
  unboundedly many visible moves. The visible infinite play is `K`
  (respectively `J`), the limit of increasing finite interactions.
* `DStrategy.extTop e N`: the part of `DStrategy.ext e D N` above `D`, copycat
  beside `N`, split at `e`; `ext e D N = D.comp (extTop e N)` by definition.
-/

@[expose] public section

namespace Silmaril.Wasm.Component

open Silmaril.Games

universe u

/-- A handler answering every question by exactly one call: its program is
`call m k` with every continuation `k n` a `pure`. -/
def AllCall {E F : Sig.{u}} (h : Handler E F) : Prop :=
  ∀ q, ∃ m k, h q = .call m k ∧ ∀ n, ∃ r, k n = .pure r

/-- **Trap chatter after `s`.** An infinite play `I` of `σ` with a member `t₀`
after which `σ` is running and every move is a trap event below `widenH n`,
lined up with a play `u` of `widenH n`: `u` and `t₀` interact with the visible
part `s`. -/
def TrapChatter {G : Sig.{0}} (n : Nat) (σ : DStrategy sigU G)
    (s : List (Move (sigN n) G)) : Prop :=
  ∃ I ∈ σ.inf, ∃ t₀ ∈ I, (∃ g, Path .idle t₀ (.run g)) ∧
    (∀ w x, t₀ ++ w ++ [x] ∈ I → ∃ e, x = .inl e ∧ IsTrap n e) ∧
    ∃ u ∈ Strategy.ofHandler (widenH n), Zip u t₀ s

/-- **`I` seen through a handler `h` below it.** Increasing interactions of
plays of `h` with members of `I`, whose visible parts grow without bound and
converge to `K`. -/
def ThroughBelow {E F G : Sig.{u}} (h : Handler E F) (I : Set (List (Move F G)))
    (K : Set (List (Move E G))) : Prop :=
  ∃ (u : Chain (Move E F)) (t : Chain (Move F G)) (s : Chain (Move E G)),
    (∀ m, Zip (u m) (t m) (s m)) ∧ (∀ m, u m ∈ Strategy.ofHandler h) ∧ (∀ m, t m ∈ I) ∧
      u.Mono ∧ t.Mono ∧ s.Mono ∧ s.Unbounded ∧ K = s.lim

/-- **`K` seen through a handler `h` above it.** Increasing interactions of
members of `K` with plays of `h`, whose visible parts grow without bound and
converge to `J`. -/
def ThroughAbove {E F G : Sig.{u}} (h : Handler F G) (K : Set (List (Move E F)))
    (J : Set (List (Move E G))) : Prop :=
  ∃ (s : Chain (Move E F)) (w : Chain (Move F G)) (p : Chain (Move E G)),
    (∀ m, Zip (s m) (w m) (p m)) ∧ (∀ m, s m ∈ K) ∧ (∀ m, w m ∈ Strategy.ofHandler h) ∧
      s.Mono ∧ w.Mono ∧ p.Mono ∧ p.Unbounded ∧ J = p.lim

/-- The part of `DStrategy.ext e D N` above `D`: copycat beside `N`, split at `e`. -/
def DStrategy.extTop (e : Nat) (N : DStrategy sigU sigU) : DStrategy sigU sigU :=
  ((DStrategy.id sigU).pair N).comp (DStrategy.ofHandler (splitH e))

end Silmaril.Wasm.Component

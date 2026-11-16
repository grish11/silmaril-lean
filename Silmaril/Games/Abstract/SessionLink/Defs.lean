module

public import Silmaril.Games.Abstract.StratSession.Defs

/-!
# Linking sessions: a client session served by a server session

A *server* `t : ObsTriple E S A (B ⊕ PUnit)` and a *client*
`u : ObsTriple (sig1 A B) S' A' (B' ⊕ PUnit)` are store-retaining triples (`StratSession`). The
client imports `F = sig1 A B`, the interface of the server's session: each import call of the
client is a call `⟨a, x⟩ : Call F`, a question `a` with its answer `x : B ⊕ PUnit` (a value
`.inl b` or a trap `.inr ()`). Composing the two sessions (`DStrategy.comp`) lets the server's
session `threadS t s₀` serve the client's session `threadS u s₀'`; the interaction on `F` is
hidden. This module defines the **linked triple** `linkS t u : ObsTriple E (S × S') A'
(B' ⊕ PUnit)`, whose session is that composite (`SessionLink.Thms`).

**Served rounds.** A client call `⟨a, x⟩` is served by one *session round* of the server at its
current store: a finished behaviour `(c, .ret x s₁)` of `t` at `(s, a)`, with log `c`; the next
call is served from `s₁`. A continuing trap `.ret (.inr ()) s₁` answers `.inr ()` and the server
store persists. A sequence of session rounds `rs` from `s` to `s₁` is `StratThread.Rounds t s rs
s₁`; it serves the calls `served rs`, and its log is `servedLog rs`. An infinite sequence of
served calls `ω` is served coherently by `InfServe t s ω l st`: round `k` has log `l k` and runs
from the store `st k` to `st (k + 1)`.

**A round of the linked triple** at the store `(s, s')` with the question `a'` is a round of the
client at `s'` whose every import call is served, the server store threaded through the calls.
Its log is the log of the served rounds: the server's calls on `E`. Its ends:

* the client returns or traps (with a store, `linkEnd`): the same, with both final stores;
  a plain client trap is a plain trap; the client diverges: `div`;
* the server diverges inside a served call: `div`;
* the client makes infinitely many calls (a productive stream of `u`), all served, with finitely
  many server calls on `E` in total: `div`. This is the hidden *chatter* of `DStrategy.comp`.

Its pending calls are the call prefixes (`StratObs.satP`) of the server inside a served call,
after served rounds, the served call being a call prefix of the client. Its productive streams are
a stream of the server inside one served call, or infinitely many served calls with infinitely many
server calls on `E` (the concatenation of their logs).

**Plain traps of the server.** A plain trap `End.trap` of the server answers the current call with
`.inr ()` and then *ends the server session*: every later call of the client is never answered.
The store `S × S'` has no state for a dead server, so `linkS` ignores plain traps of `t`; the
theorems assume `StratSession.NoPlainTrap t`.

Theorems in `Silmaril.Games.Abstract.SessionLink.Thms`.
-/

@[expose] public section

namespace Silmaril.Games.Abstract.SessionLink

open Silmaril.Games Silmaril.Games.Abstract.StratObs Silmaril.Games.Abstract.StratThread

universe u

variable {E : Sig.{u}} {S S' A B A' B' : Type u}

/-- The calls served by session rounds: the question and the answer of each round. -/
def served (rs : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))) : List (Call (sig1 A B)) :=
  rs.map fun r => ⟨r.1, r.2.2⟩

/-- The log of session rounds: their calls on `E`, in order. -/
def servedLog (rs : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))) : List (Call E) :=
  rs.flatMap fun r => r.2.1

/-- **A coherent infinite service** of the calls `ω` from the store `s`: round `k` answers the
call `ω k` with the log `l k`, as a session round of `t` from the store `st k` to
`st (k + 1)`. -/
structure InfServe (t : ObsTriple E S A (B ⊕ PUnit.{u + 1})) (s : S)
    (ω : ℕ → Call (sig1 A B)) (l : ℕ → List (Call E)) (st : ℕ → S) : Prop where
  /-- The service starts at `s`. -/
  zero : st 0 = s
  /-- Round `k` serves `ω k`. -/
  step : ∀ k, (l k, End.ret (ω k).2 (st (k + 1))) ∈ t.1 (st k) (ω k).1

/-- The log of the first `n` rounds of an infinite service. -/
def logTake (l : ℕ → List (Call E)) (n : ℕ) : List (Call E) := (streamTake l n).flatten

/-- The end of a linked round: a client end, with the final server store. -/
def linkEnd (s : S) : End S' B' → End (S × S') B'
  | .ret y s' => .ret y (s, s')
  | .trap => .trap
  | .div => .div

/-- **The linked triple**: the client `u` with its imports served by the session of `t`, the
server store threaded through the calls and kept across rounds. See the module documentation. -/
def linkS (t : ObsTriple E S A (B ⊕ PUnit.{u + 1}))
    (u : ObsTriple (sig1 A B) S' A' (B' ⊕ PUnit.{u + 1})) :
    ObsTriple E (S × S') A' (B' ⊕ PUnit.{u + 1}) :=
  (fun σ a' => {x |
      -- the client ends, every call served
      (∃ rs s₁ e, Rounds t σ.1 rs s₁ ∧ (served rs, e) ∈ u.1 σ.2 a' ∧
        x = (servedLog rs, linkEnd s₁ e)) ∨
      -- the server diverges inside a served call
      (∃ rs s₁ a c, Rounds t σ.1 rs s₁ ∧ (served rs, a) ∈ satP u σ.2 a' ∧
        (c, End.div) ∈ t.1 s₁ a ∧ x = (servedLog rs ++ c, End.div)) ∨
      -- chatter: a client stream, all served, finitely many calls on `E`
      (∃ ω ∈ u.2.2 σ.2 a', ∃ l st n, InfServe t σ.1 ω l st ∧ (∀ k, n ≤ k → l k = []) ∧
        x = (logTake l n, End.div))},
    fun σ a' => {x | ∃ rs s₁ a c, Rounds t σ.1 rs s₁ ∧ (served rs, a) ∈ satP u σ.2 a' ∧
      (c, x.2) ∈ satP t s₁ a ∧ x.1 = servedLog rs ++ c},
    fun σ a' => {ω |
      -- a server stream inside a served call
      (∃ rs s₁ a ω', Rounds t σ.1 rs s₁ ∧ (served rs, a) ∈ satP u σ.2 a' ∧ ω' ∈ t.2.2 s₁ a ∧
        ∀ k, streamTake ω ((servedLog rs).length + k) = servedLog rs ++ streamTake ω' k) ∨
      -- a client stream, all served, infinitely many calls on `E`
      (∃ ω' ∈ u.2.2 σ.2 a', ∃ l st, InfServe t σ.1 ω' l st ∧
        (∀ n, ∃ k, n ≤ (logTake l k).length) ∧
        ∀ k, streamTake ω (logTake l k).length = logTake l k)})

end Silmaril.Games.Abstract.SessionLink

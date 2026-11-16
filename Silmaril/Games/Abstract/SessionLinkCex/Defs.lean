module

public import Silmaril.Games.Abstract.SessionLink.Defs

/-!
# Linking sessions: counterexamples (definitions)

`SessionLink.comp_threadS` identifies the composite of a server session and a client session
with the session of the linked triple `linkS t u`, assuming that the server has no plain traps
(`NoPlainTrap t`), that it is store-deterministic (`StoreDet t`), and that the linked triple is
store-deterministic (`StoreDet (linkS t u)`). This topic gives one small pair of components for
each hypothesis, and one for the remark that `linkS` does not preserve `AFun.Det`. All the
components import nothing on `E` and work on `Unit`, `ℕ` and `Option ℕ`.

* **A plain server trap** (`trapServer`, `trapClient`): the server traps plainly; the client calls
  it once and returns, whatever the answer. The composite answers, but `linkS` ignores plain
  traps, so the linked triple never returns.
* **A non-coherent server** (`cdServer`, `chatClient`): the server is the countdown of
  `StratThread.not_coherent` (from `none` return to any `some n`, from `some (n + 1)` return to
  `some n`); the client, asked once, calls the server forever. Every finite number of calls is
  served, so the composite chatters, but no infinite service is coherent, so the linked triple
  does not diverge.
* **A non-coherent linked triple** (`echoServer`, `boundClient`): the server answers every
  question `n : ℕ` at once; the client's first round calls the server with some `n` and keeps the
  bound `n` on its later rounds (a countdown from `some n`). The call is hidden, so the linked
  triple has every finite number of rounds but the bound is a hidden choice: the composite has no
  infinite play of rounds, the linked session has one.
* **Linking does not preserve `AFun.Det`** (`divServer`, `mayClient`): the server diverges; the
  client may return at once or call the server. Both are deterministic given answers, but the
  linked triple both returns and diverges with the empty log.

Theorems in `Silmaril.Games.Abstract.SessionLinkCex.Thms`.
-/

@[expose] public section

namespace Silmaril.Games.Abstract.SessionLinkCex

open Silmaril.Games Silmaril.Games.Abstract.StratObs Silmaril.Games.Abstract.StratThread

variable {E : Sig.{0}}

/-! ## A plain server trap -/

/-- A server that traps plainly. -/
def trapServer : ObsTriple E Unit Unit (Unit ⊕ Unit) :=
  (fun _ _ => {([], .trap)}, fun _ _ => ∅, fun _ _ => ∅)

/-- A client that calls the server once with the trap answer and returns. -/
def trapClient : ObsTriple (sig1 Unit Unit) Unit Unit (Unit ⊕ Unit) :=
  (fun _ _ => {([⟨(), .inr ()⟩], .ret (.inl ()) ())}, fun _ _ => ∅, fun _ _ => ∅)

/-! ## A non-coherent server -/

/-- The countdown server: from `none` return to any `some n`, from `some (n + 1)` to `some n`. -/
def cdServer : ObsTriple E (Option ℕ) Unit (Unit ⊕ Unit) :=
  (fun s _ => {e | ∃ n, (s = none ∨ s = some (n + 1)) ∧ e = ([], .ret (.inl ()) (some n))},
    fun _ _ => ∅, fun _ _ => ∅)

/-- The constant call of the chattering client. -/
def chatCall : Call (sig1 Unit Unit) := ⟨(), .inl ()⟩

/-- A client that, asked once, calls the server forever. -/
def chatClient : ObsTriple (sig1 Unit Unit) Unit Unit (Unit ⊕ Unit) :=
  (fun _ _ => ∅, fun _ _ => ∅, fun _ _ => {fun _ => chatCall})

/-! ## A non-coherent linked triple -/

/-- A server answering every question at once. -/
def echoServer : ObsTriple E Unit ℕ (Unit ⊕ Unit) :=
  (fun _ _ => {([], .ret (.inl ()) ())}, fun _ _ => ∅, fun _ _ => ∅)

/-- A client whose first round calls the server with some `n` and keeps `n` as the bound on its
later rounds, which make no calls. -/
def boundClient : ObsTriple (sig1 ℕ Unit) (Option ℕ) Unit (Unit ⊕ Unit) :=
  (fun s _ => {e | (s = none ∧ ∃ n x, e = ([⟨n, x⟩], .ret (.inl ()) (some n))) ∨
      ∃ n, s = some (n + 1) ∧ e = ([], .ret (.inl ()) (some n))},
    fun _ _ => ∅, fun _ _ => ∅)

/-- The infinite play of rounds without calls answering `()`. -/
def unitRounds : Set (List (Move E (sig1 Unit Unit))) :=
  StratSession.sroundsPlay (fun _ => ()) fun _ => ([], .inl ())

/-! ## Linking does not preserve `AFun.Det` -/

/-- A server that diverges. -/
def divServer : ObsTriple E Unit Unit (Unit ⊕ Unit) :=
  (fun _ _ => {([], .div)}, fun _ _ => ∅, fun _ _ => ∅)

/-- A client that may return at once or call the server. -/
def mayClient : ObsTriple (sig1 Unit Unit) Unit Unit (Unit ⊕ Unit) :=
  (fun _ _ => {([], .ret (.inl ()) ())}, fun _ _ => {([], ())}, fun _ _ => ∅)

end Silmaril.Games.Abstract.SessionLinkCex

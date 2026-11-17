module

public import Silmaril.Games.Abstract.StratSession.Defs

/-!
# Store-dependent legality of import answers in a session

`StratLegal` restricts the import answers of a triple by a legality that depends on the call and
the answer only. Here legality depends on the **store**: a log legality
`Lg : S → A → List (Call E) → Prop` says which import logs `c` are legal in a round asked `a` at
the store `s`. (For Wasm the store at an import call is not visible in the play; it is a
function of the round's store and of the log, read from the instance's hidden states.)

* `PrefixClosed Lg`: legality of a log implies legality of its prefixes.
* `restrictLog Lg t`: the finished behaviours whose logs are legal at their round store, the call
  prefixes of `t` (`StratObs.satP`) after legal logs, and the productive streams all of whose
  finite prefixes are legal.

**Legal plays.** The store of a session play is threaded by the threading automaton of `t`
(`StratThread.TSt`): a running or waiting state `run s a c` / `wait s a c m` records the store `s`
at which the current round was asked and the round's log `c`. `StLegal Lg` holds at such a state
when `Lg s a c`, and at every other state.

* `LegalAtS Lg t s₀ q`: every run of the threading automaton of `t` from `s₀` along a play
  relabelled to `q` (`StratSession.relMove`) ends in a legal state.
* `PLegal Lg t s₀ q`: **Proponent-legality**: before each Proponent move of `q` the prefix is
  `LegalAtS`. Opponent moves are not constrained: a strategy is receptive, so after a legal log
  every answer of the environment is still a play; only the strategy's next move needs the
  answer to be legal.
* `SLegal Lg t s₀ q`: `PLegal` and `LegalAtS`; the legality of a divergent play, whose divergence
  is an observation of its last state.

Theorems in `Silmaril.Games.Abstract.SessionLegal.Thms`.
-/

@[expose] public section

namespace Silmaril.Games.Abstract.SessionLegal

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
open Silmaril.Games.Abstract.StratThread Silmaril.Games.Abstract.StratSession

universe u

variable {E : Sig.{u}} {S A B : Type u}

/-- **Log legality is closed under prefixes.** -/
def PrefixClosed (Lg : S → A → List (Call E) → Prop) : Prop :=
  ∀ s a c d, Lg s a (c ++ d) → Lg s a c

/-- **The legal part of a triple**: legal finished behaviours, call prefixes after legal logs,
and productive streams with legal prefixes. -/
def restrictLog (Lg : S → A → List (Call E) → Prop) (t : ObsTriple E S A B) : ObsTriple E S A B :=
  (fun s a => {x | x ∈ t.1 s a ∧ Lg s a x.1},
    fun s a => {x | x ∈ satP t s a ∧ Lg s a x.1},
    fun s a => {ω | ω ∈ t.2.2 s a ∧ ∀ k, Lg s a (streamTake ω k)})

/-- **A legal state of the threading automaton**: a running or waiting round has a legal log at
its round store. -/
def StLegal (Lg : S → A → List (Call E) → Prop) : TSt E S A → Prop
  | .run s a c => Lg s a c
  | .wait s a c _ => Lg s a c
  | _ => True

/-- **Legal after the session play `q`**: every run of the threading automaton of `t` from `s₀`,
along a play relabelled to `q`, ends in a legal state. -/
def LegalAtS (Lg : S → A → List (Call E) → Prop) (t : ObsTriple E S A (B ⊕ PUnit.{u + 1}))
    (s₀ : S) (q : List (Move E (sig1 A B))) : Prop :=
  ∀ p y, p.map relMove = q → TRun t.1 (satP t) (.idle s₀) p y → StLegal Lg y

/-- **Proponent-legality of a session play**: the prefix before each Proponent move is legal. -/
def PLegal (Lg : S → A → List (Call E) → Prop) (t : ObsTriple E S A (B ⊕ PUnit.{u + 1}))
    (s₀ : S) (q : List (Move E (sig1 A B))) : Prop :=
  ∀ q₁ o q₂, q = q₁ ++ o :: q₂ → o.IsP → LegalAtS Lg t s₀ q₁

/-- **Legality of a session play, its end included**: the legality of divergent plays. -/
def SLegal (Lg : S → A → List (Call E) → Prop) (t : ObsTriple E S A (B ⊕ PUnit.{u + 1}))
    (s₀ : S) (q : List (Move E (sig1 A B))) : Prop :=
  PLegal Lg t s₀ q ∧ LegalAtS Lg t s₀ q

end Silmaril.Games.Abstract.SessionLegal

module

public import Silmaril.Wasm.Abstract.NodeBridge.Defs
public import Silmaril.Games.Abstract.SessionLegal.Defs

/-!
# Host-answer domains of an instance session: definitions

A scalar Core 3.0 instance `I` answers an import call by any `Answer` of the import type
(`NodeBridge.instHost`). A **host-answer domain** `Q : Store Nat → Result → Prop` says which
answers are allowed at the store of the call; for Wasm, `Cfg.CfgInst.LegalRes` (an exception
answer names an exception of the call store). The store at an import call is not a move of the
game: it is recorded

* in the Core events `((hh, s, us), (s', r))` of the open Core triple (`coreTripleSO`), and
* in the hidden states `.waiting f s t e` of the instance's transition system
  (`ScalarInstance.Path`), where `s` is the store at which the call `e` was made.

This module states the domain at both places and relates them.

* `evRestrict Q t`: a Core triple restricted to logs and streams whose host events answer as `Q`
  allows at their call store (`Cfg.CfgInst.legalT` is `evRestrict LegalRes`).
* `instTripleQ I P Q := viewTriple I (evRestrict Q (coreTripleSO P (instHost I)))`: the instance
  triple restricted by `Q` on the Core events (`Cfg.CfgInst.instTripleL` at `Q = LegalRes`).
* `RoundLegal I P Q s a c`: **the domain on the instance game**. In the round asked `a` at the
  store `s`, every import answer `x.2` of the log `c` is allowed by `Q` at the store `s'` of every
  hidden state `.waiting a s' t x.1` in which the instance waits for it. It is a prefix-closed log
  legality in the sense of `Games.Abstract.SessionLegal`.
* `LegalPlay I P Q s₀ q := SessionLegal.PLegal (RoundLegal I P Q) (instTripleS I P) s₀`: a play
  of the instance session (`ssig I.exports`) is legal when, before each of its Proponent moves,
  every import answer so far is allowed at its call store, the store being threaded along the play
  by the session (round stores, `StratThread.TSt`) and the instance (call stores, `.waiting`).
  `LegalPlayD` also constrains the end of the play (the legality of divergences).

Theorems in `Silmaril.Wasm.Abstract.NodeLegal.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract.NodeLegal

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
open Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract.NodeBridge (instHost viewTriple coreTripleSO)
open Silmaril.Wasm.Abstract.InstSession (Res instTripleS)
open Silmaril.Wasm.Numerics (Profile)

/-- **A Core triple restricted by a host-answer domain**: logs and streams in which every host
event `((hh, s, us), (s', r))` answers `r` allowed by `Q` at its call store `s`. -/
def evRestrict (Q : Store Nat → Result → Prop) {S A B : Type}
    (t : ObsTriple (wasmHostSig Nat) S A B) : ObsTriple (wasmHostSig Nat) S A B :=
  (fun s a => {x | x ∈ t.1 s a ∧ ∀ ev ∈ x.1, Q ev.1.2.1 ev.2.2},
    fun s a => {x | x ∈ t.2.1 s a ∧ ∀ ev ∈ x.1, Q ev.1.2.1 ev.2.2},
    fun s a => {ω | ω ∈ t.2.2 s a ∧ ∀ k, Q (ω k).1.2.1 (ω k).2.2})

variable (I : ScalarInstance) (P : Profile) (Q : Store Nat → Result → Prop)

/-- **The instance triple restricted by `Q` on the Core events.** -/
noncomputable def instTripleQ : ObsTriple I.E (Store Nat) I.F.Op (Res I.exports ⊕ PUnit) :=
  viewTriple I (evRestrict Q (coreTripleSO P (instHost I)))

/-- **A log allowed by `Q` in the instance game**: in the round asked `a` at the store `s`, each
import answer of `c` is allowed at the store of every hidden state waiting for it. -/
def RoundLegal (s : Store Nat) (a : I.F.Op) (c : List (Call I.E)) : Prop :=
  ∀ c₁ x c₂, c = c₁ ++ x :: c₂ → ∀ s' t,
    I.Path P (.idle s) (.inr (.ask a) :: (callMoves c₁ ++ [.inl (.ask x.1)])) (.waiting a s' t x.1) →
      Q s' (Answer.toResult (ft := I.imports.get x.1.1) x.2)

/-- **A legal play of the instance session from `s₀`**: before each Proponent move, every import
answer so far is allowed by `Q` at its call store. -/
def LegalPlay (s₀ : Store Nat) (q : List (Move I.E (InstSession.ssig I.exports))) : Prop :=
  SessionLegal.PLegal (RoundLegal I P Q) (instTripleS I P) s₀ q

/-- **A legal play, its end included**: also the answers after the last Proponent move. -/
def LegalPlayD (s₀ : Store Nat) (q : List (Move I.E (InstSession.ssig I.exports))) : Prop :=
  SessionLegal.SLegal (RoundLegal I P Q) (instTripleS I P) s₀ q

end Silmaril.Wasm.Abstract.NodeLegal

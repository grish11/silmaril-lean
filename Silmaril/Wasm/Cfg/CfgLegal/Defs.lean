module

public import Silmaril.Wasm.Cfg.CfgInst.Defs
public import Silmaril.Wasm.Abstract.NodeLegal.Defs

/-!
# The legal typed host-answer domain of instance sessions: definitions

`CfgInst.instTripleL I P` restricts the instance triple to **legal host exceptions**: an import
answering `Answer.throw a` names an exception of the store at that call
(`CfgInst.LegalRes s r`, i.e. `Answer.ThrowsBelow s.exns.length`). It is stated on the Core events,
which record the call store. Here the same domain is stated **on the plays of the instance
session**, on its own interface `I.E ↠ ssig I.exports`, the interface the component layer reads
back (`InstSession.spullD`, `semOfSD`):

* `LegalPlay I P s₀ q`: the play `q` of the instance session from `s₀` is legal before each of
  its Proponent moves: every import answer `throw a` so far has `a < s.exns.length` at the store
  `s` of its call. The store is threaded along the play: the session threads the round stores
  (traps keep their store; instance answers to the environment are store-preserving), and the
  instance's hidden states `.waiting a s t e` give the store of each call within a round
  (`NodeLegal.RoundLegal`). Opponent may still give an illegal answer as the last move (a strategy
  is receptive); the instance does not move after it.
* `LegalPlayD I P s₀ q`: the same, the end of `q` included (the legality of a divergence).

Global exception typing is not weakened and stores are not padded: the domain is a predicate on
plays, and the objects it restricts are unchanged.

* `cfgSemD`: **the CFG-built Core 3.0 component semantics**: every numeric instance by its CFG
  instance session `CfgInst.cfgInstSessionsL` (no fallback). On instances of the domain it is
  `CfgInst.legalSemD` (`CfgInst.legalSemD_sem_eq`).

Theorems in `Silmaril.Wasm.Cfg.CfgLegal.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Cfg.CfgLegal

open Silmaril.Games
open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract.InstSession (ssig)

variable (I : ScalarInstance) (P : Numerics.Profile)

/-- **A legal play of the instance session from `s₀`**: before each Proponent move, every
import answer so far throws only exceptions of the store at its call. -/
abbrev LegalPlay (s₀ : Store Nat) (q : List (Move I.E (ssig I.exports))) : Prop :=
  Abstract.NodeLegal.LegalPlay I P CfgInst.LegalRes s₀ q

/-- **A legal play, its end included.** -/
abbrev LegalPlayD (s₀ : Store Nat) (q : List (Move I.E (ssig I.exports))) : Prop :=
  Abstract.NodeLegal.LegalPlayD I P CfgInst.LegalRes s₀ q

/-- **The CFG-built Core 3.0 component semantics**: each numeric instance by its CFG instance
session with legal host exceptions, at its instantiation store. -/
noncomputable def cfgSemD : Component.DCoreSem Component.Reference.NumInstance :=
  Abstract.InstSession.threadSemSD CfgInst.cfgInstSessionsL

end Silmaril.Wasm.Cfg.CfgLegal

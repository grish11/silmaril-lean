module

public import Silmaril.Games.Abstract.StratObs.Defs

/-!
# Legal call/answer interfaces for the canonical play object

A legality predicate `L : (m : E.Op) → E.Ar m → Prop` says which answers to an import call are
legal; for Wasm, the answers a callee of the call's type may give. The **legal interface**
`legalSig E L` has the same calls, and as answers to `m` only the legal ones (a subtype): in its
game, Opponent can give legal answers only. This is a typed interface, not a filter on plays.

* `liftCall`, `liftMove`, `liftSt`: forgetting legality, from the legal interface to `E`;
* `restrict L t`: the observations of `t` whose logs answer legally, transported to the legal
  interface: a behaviour, pending call or productive stream over `legalSig E L` is in
  `restrict L t` when its log, legality forgotten, is in `t`;
* `toDStratL L t := toDStrat (restrict L t)`: the play object of `t` on the legal interface.

Theorems in `Silmaril.Games.Abstract.StratLegal.Thms`.
-/

@[expose] public section

namespace Silmaril.Games.Abstract.StratLegal

open Silmaril.Games Silmaril.Games.Abstract

universe u

variable {E : Sig.{u}} {S A B : Type u}

/-- **The legal interface**: the calls of `E`, answered only legally. -/
def legalSig (E : Sig.{u}) (L : (m : E.Op) → E.Ar m → Prop) : Sig.{u} :=
  ⟨E.Op, fun m => {n // L m n}⟩

variable {L : (m : E.Op) → E.Ar m → Prop}

/-- A legally answered call, legality forgotten. -/
def liftCall (x : Call (legalSig E L)) : Call E := ⟨x.1, x.2.1⟩

/-- An event of the legal interface, legality forgotten. -/
def liftEv : Ev (legalSig E L) → Ev E
  | .ask m => .ask m
  | .ans m n => .ans m n.1

/-- A move with legal import answers, legality forgotten. -/
def liftMove {F : Sig.{u}} : Move (legalSig E L) F → Move E F
  | .inl e => .inl (liftEv e)
  | .inr e => .inr e

/-- An automaton state, legality forgotten. -/
def liftSt : StratObs.St (legalSig E L) S A → StratObs.St E S A
  | .idle => .idle
  | .run q c => .run q (c.map liftCall)
  | .wait q c m => .wait q (c.map liftCall) m

/-- **The legally answered observations** of `t`, on the legal interface. -/
def restrict (L : (m : E.Op) → E.Ar m → Prop) (t : ObsTriple E S A B) :
    ObsTriple (legalSig E L) S A B :=
  (fun s a => {x | (x.1.map liftCall, x.2) ∈ t.1 s a},
    fun s a => {x | (x.1.map liftCall, x.2) ∈ t.2.1 s a},
    fun s a => {ω | (fun n => liftCall (ω n)) ∈ t.2.2 s a})

/-- **The play object on the legal interface.** -/
def toDStratL (L : (m : E.Op) → E.Ar m → Prop) (t : ObsTriple E S A B) :
    DStrategy (legalSig E L) (funSig S A B) :=
  StratObs.toDStrat (restrict L t)

end Silmaril.Games.Abstract.StratLegal

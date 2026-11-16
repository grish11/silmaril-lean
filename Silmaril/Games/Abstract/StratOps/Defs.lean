module

public import Silmaril.Games.Abstract.StratObs.Defs
public import Silmaril.Games.Abstract.FullFun.Defs

/-!
# Premonoidal operations on observation triples and on the canonical play object

An observation triple `t : ObsTriple E S A B` is a full observation `full t : FullFun E S A B`
(finished behaviours and productive runs) together with pending calls. The operations here
extend the `FullFun` operations with a pending component; on the `(AFun, PInf)` part they *are*
the `FullFun` operations (`full_seqT` and the other `full_…` lemmas hold by `rfl`).

* `seqT t u`: the pending calls of `t`, and the pending calls of `u` at `(s₁, b)` after a
  finished return `ret b s₁` of `t` with log `c₁`, the log being `c₁ ++ c₂`;
* `pureT`: the identity, with no pending call;
* `mapT`, `comapT`: post- and pre-composition with a pure function; the pending calls are
  unchanged (re-indexed by the argument for `comapT`);
* `whiskerRightT`, `whiskerLeftT`: run on one component of a pair and carry the other through;
  the pending calls at `(a, c)` (resp. `(c, a)`) are those at `a`;
* `iterT`: iteration (`inl` exits, `inr` continues); the pending calls are those of the body
  reached after a finite chain of finished continuing iterations (`FullFun.ContChain`).

`Total u` says `u` has some observation (behaviour, pending call or productive run) at every
state and argument; it is the hypothesis under which sequencing commutes with saturation in
its first argument (`Silmaril.Games.Abstract.StratOps.Thms`).

## The game-level operations

`readback σ` reads a triple off a divergence-observing strategy on the function interface:
finished behaviours from completed one-round plays, divergent behaviours from one-round
divergent plays, pending calls from one-round plays ending in a call, and productive runs from
one-round infinite plays `streamPlay [] q ω`. On play objects it is saturation
(`readback_toDStrat : readback (toDStrat t) = sat t`).

The game-level operations `seqD`, `pureD`, `mapD`, `comapD`, `whiskerRightD`, `whiskerLeftD`
and `iterD` are **defined through readback**: read the triples back, apply the triple operation,
and take the play object. No direct interaction construction on strategies (composition with
hiding of the intermediate interface) is given or claimed here; the theorems show that these
operations agree with the triple operations on the image of `toDStrat`.
-/

@[expose] public section

namespace Silmaril.Games.Abstract.StratOps

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs

universe u

variable {E : Sig.{u}} {S A B C : Type u}

/-! ## Triples as full observations with pending calls -/

/-- The full observation of a triple: its finished behaviours and productive runs. -/
def full (t : ObsTriple E S A B) : FullFun E S A B := (t.1, t.2.2)

/-- The triple of a full observation and pending calls. -/
def ofFull (F : FullFun E S A B) (P : Pending E S A) : ObsTriple E S A B := (F.1, P, F.2)

/-- A triple with some observation at every state and argument. -/
def Total (t : ObsTriple E S A B) : Prop :=
  ∀ s a, (t.1 s a).Nonempty ∨ (t.2.1 s a).Nonempty ∨ (t.2.2 s a).Nonempty

/-! ## Operations on triples -/

/-- **Sequencing.** The pending calls of `t`, and after a finished return of `t`, the pending
calls of `u` on its result and state. -/
def seqT (t : ObsTriple E S A B) (u : ObsTriple E S B C) : ObsTriple E S A C :=
  ofFull (FullFun.seq (full t) (full u)) fun s a => t.2.1 s a ∪
    {x | ∃ (c₁ : List (Call E)) (b : B) (s₁ : S) (c₂ : List (Call E)) (m : E.Op),
      (c₁, End.ret b s₁) ∈ t.1 s a ∧ (c₂, m) ∈ u.2.1 s₁ b ∧ x = (c₁ ++ c₂, m)}

/-- **The identity**: return the argument, no pending call. -/
def pureT : ObsTriple E S A A := ofFull FullFun.pure fun _ _ => ∅

/-- **Post-composition with a pure function**; the pending calls are unchanged. -/
def mapT (t : ObsTriple E S A B) (h : B → C) : ObsTriple E S A C :=
  ofFull ((full t).map h) t.2.1

/-- **Pre-composition with a pure function.** -/
def comapT {A' : Type u} (t : ObsTriple E S A B) (k : A' → A) : ObsTriple E S A' B :=
  ofFull ((full t).comap k) fun s a => t.2.1 s (k a)

/-- **Right whiskering** `t ⋉ C`; the pending calls at `(a, c)` are those at `a`. -/
def whiskerRightT (t : ObsTriple E S A B) (C : Type u) : ObsTriple E S (A × C) (B × C) :=
  ofFull ((full t).whiskerRight C) fun s p => t.2.1 s p.1

/-- **Left whiskering** `C ⋊ t`; the pending calls at `(c, a)` are those at `a`. -/
def whiskerLeftT (C : Type u) (t : ObsTriple E S A B) : ObsTriple E S (C × A) (C × B) :=
  ofFull ((full t).whiskerLeft C) fun s p => t.2.1 s p.2

/-- **Iteration** of a loop body (`inl` exits, `inr` continues). The pending calls are those
of the body after a finite chain of finished continuing iterations. -/
def iterT (t : ObsTriple E S A (B ⊕ A)) : ObsTriple E S A B :=
  ofFull (FullFun.iter (full t)) fun s a =>
    {x | ∃ (c : List (Call E)) (s' : S) (a' : A) (c' : List (Call E)) (m : E.Op),
      FullFun.ContChain t.1 s a c s' a' ∧ (c', m) ∈ t.2.1 s' a' ∧ x = (c ++ c', m)}

/-! ## Reading a triple back from a play object -/

/-- **Readback**: the one-round observations of a strategy on the function interface. A
finished return or trap is a completed round, a divergence a divergent one-round play, a
pending call a one-round play ending in that call, and a productive run a one-round infinite
play. -/
def readback (σ : DStrategy E (funSig S A B)) : ObsTriple E S A B :=
  (fun s a => {x | match x with
      | (c, .ret b s') =>
        (.inr (.ask (s, a)) :: (callMoves c ++ [.inr (.ans (s, a) (.inl (b, s')))]) :
          List (Move E (funSig S A B))) ∈ σ.toStrategy
      | (c, .trap) =>
        (.inr (.ask (s, a)) :: (callMoves c ++ [.inr (.ans (s, a) (.inr PUnit.unit))]) :
          List (Move E (funSig S A B))) ∈ σ.toStrategy
      | (c, .div) => (.inr (.ask (s, a)) :: callMoves c : List (Move E (funSig S A B))) ∈ σ.div},
    fun s a => {x | (.inr (.ask (s, a)) :: (callMoves x.1 ++ [.inl (.ask x.2)]) :
      List (Move E (funSig S A B))) ∈ σ.toStrategy},
    fun s a => {ω | streamPlay [] (s, a) ω ∈ σ.inf})

/-! ## Game-level operations, defined through readback -/

/-- Sequencing of play objects, through readback. -/
def seqD (σ : DStrategy E (funSig S A B)) (τ : DStrategy E (funSig S B C)) :
    DStrategy E (funSig S A C) :=
  toDStrat (seqT (readback σ) (readback τ))

/-- The identity play object. -/
def pureD : DStrategy E (funSig S A A) := toDStrat pureT

/-- Post-composition of a play object with a pure function, through readback. -/
def mapD (σ : DStrategy E (funSig S A B)) (h : B → C) : DStrategy E (funSig S A C) :=
  toDStrat (mapT (readback σ) h)

/-- Pre-composition of a play object with a pure function, through readback. -/
def comapD {A' : Type u} (σ : DStrategy E (funSig S A B)) (k : A' → A) :
    DStrategy E (funSig S A' B) :=
  toDStrat (comapT (readback σ) k)

/-- Right whiskering of a play object, through readback. -/
def whiskerRightD (σ : DStrategy E (funSig S A B)) (C : Type u) :
    DStrategy E (funSig S (A × C) (B × C)) :=
  toDStrat (whiskerRightT (readback σ) C)

/-- Left whiskering of a play object, through readback. -/
def whiskerLeftD (C : Type u) (σ : DStrategy E (funSig S A B)) :
    DStrategy E (funSig S (C × A) (C × B)) :=
  toDStrat (whiskerLeftT C (readback σ))

/-- Iteration of a play object, through readback. -/
def iterD (σ : DStrategy E (funSig S A (B ⊕ A))) : DStrategy E (funSig S A B) :=
  toDStrat (iterT (readback σ))

end Silmaril.Games.Abstract.StratOps

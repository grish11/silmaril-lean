module

public import Silmaril.Wasm.Abstract.Body.Defs
public import Silmaril.Games.Abstract.Function.Defs

/-!
# From interaction-tree bodies to trace-set functions

Abstract functions (`Silmaril.Games.Abstract.AFun`) are arbitrary,
nondeterministic sets of call behaviours. Interaction-tree bodies
(`Silmaril.Wasm.Abstract.Body.BodyM`) are deterministic given the
environment's answers. They are a **restricted submodel**, not a replacement.
This module gives the explicit denotation `toAFun` from bodies to abstract
functions, reading each finite path of the tree (import calls with their
answers, then a return, a trap or silent divergence) as a call behaviour.

`Silmaril.Wasm.Abstract.BodyTrace.Thms` proves that every denoted function is
deterministic given the history, and that not every abstract function is
denoted (a nondeterministic one is not). The image is contained in the
deterministic functions.

**What the denotation forgets.**

* Trap payloads: `AFun` has one `trap` end.
* Infinite productive runs (infinitely many import calls): `AFun` has no
  infinite behaviours, so bodies that differ only on infinite branches may
  have the same denotation.

The denotation is therefore not claimed to be injective.

**Universes.** Bodies take values in `Type (u + 1)` (interaction trees are
large), so the import signature is lifted (`liftSig`) to match.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract.BodyTrace

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Abstract.Body

universe u

/-- An import signature lifted one universe up. -/
def liftSig (E : Sig.{u}) : Sig.{u + 1} := ⟨ULift.{u + 1} E.Op, fun m => ULift.{u + 1} (E.Ar m.down)⟩

/-- How a finite path of an interaction tree ends. -/
inductive PathEnd (A : Type (u + 1)) : Type (u + 1)
  /-- Returned `a`. -/
  | val (a : A)
  /-- Diverged silently. -/
  | div

/-- `Path t cs r`: the tree `t` performs the import calls `cs` (with their
answers) and then ends as `r`. -/
inductive Path {E : Sig.{u}} {A : Type (u + 1)} :
    Silmaril.Elgot.ITree.Tree (SigEv E) A → List (Call E) → PathEnd A → Prop
  /-- A return. -/
  | ret {t : Silmaril.Elgot.ITree.Tree (SigEv E) A} {a : A} :
      t = Silmaril.Elgot.ITree.ret a → Path t [] (.val a)
  /-- Silent divergence. -/
  | div {t : Silmaril.Elgot.ITree.Tree (SigEv E) A} :
      t = Silmaril.Elgot.ITree.diverge → Path t [] .div
  /-- An import call answered by `n`, then the rest. -/
  | vis {t : Silmaril.Elgot.ITree.Tree (SigEv E) A} {R : Type u} {e : SigEv E R}
      {k : R → Silmaril.Elgot.ITree.Tree (SigEv E) A} {n : R} {cs : List (Call E)}
      {r : PathEnd A} :
      t = Silmaril.Elgot.ITree.vis e k → Path (k n) cs r →
      Path t (⟨e.1, cast e.2.symm n⟩ :: cs) r

/-- An import call, lifted. -/
def liftCall {E : Sig.{u}} (c : Call E) : Call (liftSig E) := ⟨ULift.up c.1, ULift.up c.2⟩

/-- The end of a body's path as the end of a call behaviour. -/
def endOf {S T B : Type (u + 1)} : PathEnd (Except T (B × S)) → End S B
  | .val (.ok (b, s)) => .ret b s
  | .val (.error _) => .trap
  | .div => .div

/-- The trace-set function denoted by a body. -/
def toAFun {E : Sig.{u}} {S T A B : Type (u + 1)} (f : Hom E S T A B) :
    AFun (liftSig E) S A B := fun s a =>
  {x | ∃ cs r, Path ((f a).run s).run cs r ∧ x = (cs.map liftCall, endOf r)}

end Silmaril.Wasm.Abstract.BodyTrace

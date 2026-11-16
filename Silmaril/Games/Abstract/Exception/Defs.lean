module

public import Silmaril.Games.Abstract.Function.Defs

/-!
# Exception properties of abstract functions

A function whose result type is `R ⊕ X` returns a value (`inl`) or lets an
exception `x : X` escape (`inr`), as `wasmFun` does with uncaught Wasm
exceptions.

* `MayEscape f s a`: some *executable* behaviour of `f` at `s` and `a` ends
  with an escaping exception. Behaviours are runs, not graph paths.
* `NoEscape f`: no run of `f` ever lets an exception escape.
* `underAssm Q f`: the runs whose import calls and answers all satisfy `Q`.
  An assumption about the environment, such as "imports never raise", is a
  `Q`. `NoEscapeUnder Q f` is no escape under that assumption.
* `seqX f g`: run `f`, then `g` on its value, propagating an escaping
  exception of `f` without running `g`. A caller that never throws itself
  still lets a callee's exception through.
* `handleX f h`: run `f`, and on an escaping exception run the handler `h`.
  This is a local `try`/`catch`: the exception was raised but did not escape.

**Semantic, not syntactic.** `NoEscape` says no executable run escapes. It does
not say that a control-flow graph has no syntactic path to a raise exit, because
graphs over-approximate and may contain infeasible paths. Removing a raise
exit, or any handler transfer, from a graph needs its own proof that the
graph's executable semantics is preserved. A function that does not escape may
still raise and catch locally, so its handler edges must stay.
-/

@[expose] public section

namespace Silmaril.Games.Abstract.AFun

open Silmaril.Games

universe u

variable {E : Sig.{u}} {S A R R' X : Type u}

/-- Some run ends with an escaping exception. -/
def MayEscape (f : AFun E S A (R ⊕ X)) (s : S) (a : A) : Prop :=
  ∃ c x s', (c, End.ret (.inr x) s') ∈ f s a

/-- No run ever lets an exception escape. -/
def NoEscape (f : AFun E S A (R ⊕ X)) : Prop := ∀ s a, ¬ MayEscape f s a

/-- The runs whose import calls (with their answers) all satisfy `Q`. -/
def underAssm (Q : Call E → Prop) (f : AFun E S A (R ⊕ X)) : AFun E S A (R ⊕ X) :=
  fun s a => {x | x ∈ f s a ∧ ∀ y ∈ x.1, Q y}

/-- No escape, assuming every import call satisfies `Q`. -/
def NoEscapeUnder (Q : Call E → Prop) (f : AFun E S A (R ⊕ X)) : Prop :=
  NoEscape (underAssm Q f)

/-- Continue with `g` on a value; pass an escaping exception through. -/
def propagate (g : AFun E S R (R' ⊕ X)) : AFun E S (R ⊕ X) (R' ⊕ X) := fun s r =>
  match r with
  | .inl v => g s v
  | .inr x => {([], End.ret (.inr x) s)}

/-- Sequencing with exception propagation. -/
def seqX (f : AFun E S A (R ⊕ X)) (g : AFun E S R (R' ⊕ X)) : AFun E S A (R' ⊕ X) :=
  seq f (propagate g)

/-- Return a value unchanged; run the handler on an exception. -/
def catchWith (h : AFun E S X (R ⊕ X)) : AFun E S (R ⊕ X) (R ⊕ X) := fun s r =>
  match r with
  | .inl v => {([], End.ret (.inl v) s)}
  | .inr x => h s x

/-- A local `try`/`catch`: run `f`, handle its escaping exceptions with `h`. -/
def handleX (f : AFun E S A (R ⊕ X)) (h : AFun E S X (R ⊕ X)) : AFun E S A (R ⊕ X) :=
  seq f (catchWith h)

end Silmaril.Games.Abstract.AFun

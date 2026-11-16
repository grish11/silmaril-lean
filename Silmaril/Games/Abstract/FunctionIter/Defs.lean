module

public import Silmaril.Games.Abstract.Function.Defs

/-!
# Iteration of abstract functions

A loop body `f : AFun E S A (B ⊕ A)` either exits with `inl b` or continues
with `inr a'`, in the state it left. `AFun.iter f` collects every *finite*
call behaviour of running it to the end, with divergence accounted for
explicitly:

* `exit`, `trap`, `div`: the current iteration returns `inl b`, traps or
  diverges, after the calls `c`;
* `step`: the current iteration returns `inr a'` in state `s'` after the calls
  `c₁`, and the loop continues from `(s', a')` with behaviour `(c₂, e)`; the
  whole run is `(c₁ ++ c₂, e)`;
* `spin`: an infinite chain of iterations, each returning `inr` **without any
  import call**. This is silent divergence, `([], div)`, even though no single
  iteration diverges. Following finitely many `step`s, it gives `(c, div)`
  for the calls `c` made before the chain.

An infinite chain in which infinitely many iterations make import calls is an
infinite *productive* run. `AFun` has no infinite behaviours, so such a run
contributes no behaviour, as for a single function. Nothing is assumed of `f`:
it may be nondeterministic, and need not be productive.
-/

@[expose] public section

namespace Silmaril.Games.Abstract.AFun

open Silmaril.Games

universe u

variable {E : Sig.{u}} {S A B : Type u}

/-- The finite behaviours of iterating `f` from state `s` and argument `a`. -/
inductive IterBeh (f : AFun E S A (B ⊕ A)) : S → A → CallBeh E S B → Prop
  /-- The current iteration exits with `b`. -/
  | exit {s a c b s'} : (c, .ret (.inl b) s') ∈ f s a → IterBeh f s a (c, .ret b s')
  /-- The current iteration traps. -/
  | trap {s a c} : (c, .trap) ∈ f s a → IterBeh f s a (c, .trap)
  /-- The current iteration diverges silently. -/
  | div {s a c} : (c, .div) ∈ f s a → IterBeh f s a (c, .div)
  /-- The current iteration continues with `a'` in state `s'`. -/
  | step {s a c₁ a' s' c₂ e} : (c₁, .ret (.inr a') s') ∈ f s a → IterBeh f s' a' (c₂, e) →
      IterBeh f s a (c₁ ++ c₂, e)
  /-- An infinite chain of silent continuing iterations from `(s, a)`. -/
  | spin {s a} (σ : Nat → S × A) : σ 0 = (s, a) →
      (∀ n, ([], .ret (.inr (σ (n + 1)).2) (σ (n + 1)).1) ∈ f (σ n).1 (σ n).2) →
      IterBeh f s a ([], .div)

/-- Iterate a loop body: `inl` exits, `inr` continues. -/
def iter (f : AFun E S A (B ⊕ A)) : AFun E S A B := fun s a => {x | IterBeh f s a x}

end Silmaril.Games.Abstract.AFun

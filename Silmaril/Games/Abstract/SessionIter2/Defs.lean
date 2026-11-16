module

public import Silmaril.Games.Abstract.SessionIter.Defs

/-!
# Session iteration: continuing chains (definitions)

For a session loop body `t : ObsTriple E S A ((B ⊕ A) ⊕ PUnit)` (`SessionIter.iterS`), the
plays of `threadS (iterS t)` that do not complete a round are described by chains of
*continuing* body returns `.ret (.inl (.inr a')) s'`:

* `ContS t s a c s' a'`: a finite chain of continuing returns from `(s, a)` to `(s', a')`, the
  logs concatenating to `c` (`FullFun.ContChain` of the body read as an `iterT` body);
* `InfContS t s a l`: an infinite chain of continuing returns from `(s, a)`, the `n`-th with
  log `l n`. With `l = fun _ => []` it is a silent infinite chain (a divergence of the
  iteration); with infinitely many calls it is a productive stream (`Shape.StreamConcat l ω`).

Theorems in `Silmaril.Games.Abstract.SessionIter2.Thms`.
-/

@[expose] public section

namespace Silmaril.Games.Abstract.SessionIter2

open Silmaril.Games Silmaril.Games.Abstract.StratObs

universe u

variable {E : Sig.{u}} {S A B : Type u}

/-- **A finite chain of continuing body returns** from `(s, a)` to `(s', a')`, with logs
concatenating to `c`. -/
inductive ContS (t : ObsTriple E S A ((B ⊕ A) ⊕ PUnit.{u + 1})) :
    S → A → List (Call E) → S → A → Prop
  /-- No iteration. -/
  | refl {s a} : ContS t s a [] s a
  /-- One continuing return with log `c₁`, then the rest of the chain. -/
  | step {s a c₁ s₁ a₁ c₂ s' a'} : (c₁, End.ret (.inl (.inr a₁)) s₁) ∈ t.1 s a →
      ContS t s₁ a₁ c₂ s' a' → ContS t s a (c₁ ++ c₂) s' a'

/-- **An infinite chain of continuing body returns** from `(s, a)`, the `n`-th with log `l n`. -/
def InfContS (t : ObsTriple E S A ((B ⊕ A) ⊕ PUnit.{u + 1})) (s : S) (a : A)
    (l : ℕ → List (Call E)) : Prop :=
  ∃ σ : ℕ → S × A, σ 0 = (s, a) ∧
    ∀ n, (l n, End.ret (.inl (.inr (σ (n + 1)).2)) (σ (n + 1)).1) ∈ t.1 (σ n).1 (σ n).2

end Silmaril.Games.Abstract.SessionIter2

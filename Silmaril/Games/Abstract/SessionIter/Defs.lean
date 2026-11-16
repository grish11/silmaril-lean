module

public import Silmaril.Games.Abstract.SessionCat.Defs

/-!
# Session iteration with store-retaining traps: definitions

On store-retaining session triples `ObsTriple E S A (B ⊕ PUnit)` (`StratSession`), sequencing
within a round is `SessionCat.seqS`, the Kleisli sequencing of the exception monad `· ⊕ PUnit`.
This topic adds its iteration.

**Iteration.** A loop body `t : ObsTriple E S A ((B ⊕ A) ⊕ PUnit)` returns `.inl (.inl b)` to
exit with `b`, `.inl (.inr a')` to continue with `a'`, or a continuing trap `.inr ()`, which
aborts the whole iteration and keeps the trap store. `iterS t : ObsTriple E S A (B ⊕ PUnit)` is
`StratOps.iterT` of the body with its result reassociated by `iterAssoc` (`inl` exits with a
session answer, a value or a continuing trap; `inr` continues): no new operation is built.
`exitS` is the session continuation that exits with its argument.

**Rounds.** A completed session round `(a, c, x)` of `seqS t u` or `iterS t` is made of rounds of
the components within one round, the stores threaded and a continuing trap aborting the round:

* `SeqRet t u s a c x s'`: `t` traps keeping the store `s'`, or `t` returns the value `b` at
  `s₁` and `u` returns `x` from `(s₁, b)`, the log being the concatenation;
* `IterRet t s a c x s'`: a finite chain of continuing body returns, then an exiting value or a
  continuing trap;
* `RoundsBy R s rs s'`: the rounds `rs` chain from `s` to `s'` along the one-round relation `R`
  (`StratThread.Rounds` for the returns of a triple).

Theorems in `Silmaril.Games.Abstract.SessionIter.Thms`.
-/

@[expose] public section

namespace Silmaril.Games.Abstract.SessionIter

open Silmaril.Games Silmaril.Games.Abstract.StratObs Silmaril.Games.Abstract.StratOps
  Silmaril.Games.Abstract.SessionCat

universe u

variable {E : Sig.{u}} {S A B C : Type u}

/-- The result of a session loop body read as an `iterT` result: an exiting value and a
continuing trap are the session answer (`inl`), a continuing argument continues (`inr`). -/
def iterAssoc : (B ⊕ A) ⊕ PUnit.{u + 1} → (B ⊕ PUnit.{u + 1}) ⊕ A
  | .inl (.inl b) => .inl (.inl b)
  | .inl (.inr a) => .inr a
  | .inr _ => .inl (.inr PUnit.unit)

/-- **Session iteration**: `.inl (.inl b)` exits with `b`, `.inl (.inr a')` continues with `a'`,
and a continuing trap aborts the iteration, keeping its store. -/
def iterS (t : ObsTriple E S A ((B ⊕ A) ⊕ PUnit.{u + 1})) : ObsTriple E S A (B ⊕ PUnit.{u + 1}) :=
  iterT (mapT t iterAssoc)

/-- The session continuation exiting a loop with its argument. -/
def exitS : ObsTriple E S B ((B ⊕ A) ⊕ PUnit.{u + 1}) := mapT pureT (Sum.inl ∘ Sum.inl)

/-! ## Rounds -/

/-- **One returning round of a sequence**: a continuing trap of `t`, or a value of `t` continued
by a return of `u`. -/
def SeqRet (t : ObsTriple E S A (B ⊕ PUnit.{u + 1})) (u : ObsTriple E S B (C ⊕ PUnit.{u + 1}))
    (s : S) (a : A) (c : List (Call E)) (x : C ⊕ PUnit.{u + 1}) (s' : S) : Prop :=
  (x = .inr PUnit.unit ∧ (c, End.ret (.inr PUnit.unit) s') ∈ t.1 s a) ∨
    ∃ c₁ b s₁ c₂, (c₁, End.ret (.inl b) s₁) ∈ t.1 s a ∧ (c₂, End.ret x s') ∈ u.1 s₁ b ∧
      c = c₁ ++ c₂

/-- **One returning round of an iteration**: continuing body returns, then an exit or a
continuing trap. -/
inductive IterRet (t : ObsTriple E S A ((B ⊕ A) ⊕ PUnit.{u + 1})) :
    S → A → List (Call E) → B ⊕ PUnit.{u + 1} → S → Prop
  /-- The body exits with `b`. -/
  | exit {s a c b s'} : (c, End.ret (.inl (.inl b)) s') ∈ t.1 s a → IterRet t s a c (.inl b) s'
  /-- The body traps, keeping the store: the iteration is aborted. -/
  | trap {s a c s'} : (c, End.ret (.inr PUnit.unit) s') ∈ t.1 s a →
      IterRet t s a c (.inr PUnit.unit) s'
  /-- The body continues with `a'`, then the rest of the iteration. -/
  | step {s a c₁ a' s₁ c₂ x s'} : (c₁, End.ret (.inl (.inr a')) s₁) ∈ t.1 s a →
      IterRet t s₁ a' c₂ x s' → IterRet t s a (c₁ ++ c₂) x s'

/-- Completed rounds along a one-round relation, the stores threaded. -/
inductive RoundsBy (R : S → A → List (Call E) → B → S → Prop) :
    S → List (A × List (Call E) × B) → S → Prop
  | nil (s : S) : RoundsBy R s [] s
  | cons {s s₁ s₂ : S} {a : A} {c : List (Call E)} {b : B} {rs : List (A × List (Call E) × B)} :
      R s a c b s₁ → RoundsBy R s₁ rs s₂ → RoundsBy R s ((a, c, b) :: rs) s₂

end Silmaril.Games.Abstract.SessionIter

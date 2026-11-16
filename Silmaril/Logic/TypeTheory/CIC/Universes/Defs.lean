module

public import Mathlib.Order.Lattice.Nat

@[expose] public section

/-! # PCUIC universe expressions and sorts

Adapted from `MetaRocq/metarocq` at
`c8cd46054518193103c3bb33aa6e15c7f489e72c`, `common/theories/Universes.v`.
The MIT notice is retained in `licenses/MetaRocq-MIT.txt`.

Expressions use a tree presentation of finite maxima and successors rather
than MetaRocq's canonical nonempty sets of level expressions. Their meaning is
natural-number valuation. `Type 0` is Set; Prop and SProp have type `Type 1`.
The selected cumulativity policy is MetaRocq's checked-universe standard profile
with `prop_sub_type = true`. Ordinary Prop and SProp remain distinct.
-/

namespace Silmaril.Logic.TypeTheory.CIC

universe u v

/-- Algebraic universes with explicit level names, zero, successors and maxima. -/
inductive UniverseExpr (Level : Type u) where
  | zero
  | level (name : Level)
  | succ (u : UniverseExpr Level)
  | max (u v : UniverseExpr Level)
  deriving DecidableEq, Repr

namespace UniverseExpr

/-- Interpret named levels in the natural numbers. -/
def eval {Level : Type u} (ρ : Level → ℕ) : UniverseExpr Level → ℕ
  | .zero => 0
  | .level l => ρ l
  | .succ u => u.eval ρ + 1
  | .max u v => Nat.max (u.eval ρ) (v.eval ρ)

/-- Simultaneous substitution of universe expressions for level names. -/
def subst {Level : Type u} {Level' : Type v} (σ : Level → UniverseExpr Level') :
    UniverseExpr Level → UniverseExpr Level'
  | .zero => .zero
  | .level l => σ l
  | .succ u => .succ (u.subst σ)
  | .max u v => .max (u.subst σ) (v.subst σ)

/-- Rename universe names without changing the successor/max structure. -/
def rename {Level : Type u} {Level' : Type v} (f : Level → Level') :
    UniverseExpr Level → UniverseExpr Level' := subst (.level ∘ f)

/-- A level expression fits a finite semantic universe supply under a valuation. -/
def UsesBelow {Level : Type u} (ρ : Level → ℕ) (n : ℕ) (u : UniverseExpr Level) : Prop :=
  u.eval ρ < n

/-- Number of available levels needed by a numeric ground expression. -/
def universeBound (u : UniverseExpr ℕ) : ℕ := u.eval id + 1

end UniverseExpr

/-- Rocq's ordinary propositions, strict propositions, and predicative Type universes. -/
inductive SortExpr (Level : Type u) where
  | prop
  | sprop
  | type (u : UniverseExpr Level)
  deriving DecidableEq, Repr

namespace SortExpr

/-- Apply a universe-expression transformation to a sort. -/
def map {Level : Type u} {Level' : Type v}
    (f : UniverseExpr Level → UniverseExpr Level') : SortExpr Level → SortExpr Level'
  | .prop => .prop
  | .sprop => .sprop
  | .type u => .type (f u)

/-- The sort typing another sort; this is not the cumulativity relation. -/
def super {Level : Type u} : SortExpr Level → SortExpr Level
  | .prop | .sprop => .type (.succ .zero)
  | .type u => .type (.succ u)

/-- The sort join used by PCUIC product formation. -/
def sup {Level : Type u} : SortExpr Level → SortExpr Level → SortExpr Level
  | .sprop, b => b
  | .prop, .sprop => .prop
  | .prop, b => b
  | .type a, .type b => .type (.max a b)
  | .type a, _ => .type a

/-- Products into Prop and SProp are impredicative. -/
def product {Level : Type u} (domain range : SortExpr Level) : SortExpr Level :=
  match range with
  | .prop | .sprop => range
  | .type _ => sup domain range

/-- Selected PCUIC sort cumulativity, with ordinary Prop a subtype of Type.

SProp is not cumulatively a subtype of Prop or Type. This relation does not
assert equality of proofs of an ordinary proposition.
-/
def Cumul {Level : Type u} (ρ : Level → ℕ) : SortExpr Level → SortExpr Level → Prop
  | .prop, .prop | .sprop, .sprop => True
  | .type a, .type b => a.eval ρ ≤ b.eval ρ
  | .prop, .type _ => True
  | _, _ => False

/-- All Type universes in a sort fit the specified finite supply. -/
def UsesBelow {Level : Type u} (ρ : Level → ℕ) (n : ℕ) : SortExpr Level → Prop
  | .prop | .sprop => True
  | .type u => u.UsesBelow ρ n

/-- Finite count required by a sort with numeric ground levels. -/
def universeBound : SortExpr ℕ → ℕ
  | .prop | .sprop => 0
  | .type u => u.universeBound

end SortExpr

/-- An inductive declaration's permitted target families for dependent elimination.

This records the source classification; choosing the correct classification
from an inductive block requires a separate declaration-checking proof.
-/
inductive AllowedElimination where
  | intoSProp
  | intoPropSProp
  | intoSetPropSProp
  | intoAny
  deriving DecidableEq, Repr

/-- The selected elimination classification permits the target sort. -/
def AllowedElimination.Allows {Level : Type u} (ρ : Level → ℕ)
    (policy : AllowedElimination) (s : SortExpr Level) : Prop :=
  match policy, s with
  | .intoAny, _ => True
  | .intoSProp, .sprop => True
  | .intoPropSProp, .prop | .intoPropSProp, .sprop => True
  | .intoSetPropSProp, .prop | .intoSetPropSProp, .sprop => True
  | .intoSetPropSProp, .type u => u.eval ρ = 0
  | _, _ => False

end Silmaril.Logic.TypeTheory.CIC

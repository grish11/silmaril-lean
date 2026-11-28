module

public import Silmaril.Semantics.ElgotMonads.Thms
public import Mathlib.Order.FixedPoints

/-! # Nondeterministic finite trace observations -/

@[expose] public section

namespace Silmaril.Semantics.NondeterministicTrace

universe u

/-- May return a value with a log in the given monoid. An empty set supplies no observation. -/
abbrev Finite (W : Type u) := WriterT W SetM

/-- A may observer can also report an incomplete branch with its finite log and a tag.
Sequencing retains that observation and skips the continuation on that branch. -/
abbrev Tagged (W T : Type u) := ExceptT T (Finite W)

namespace Finite

variable {W V A B : Type u}

def outcomes (p : Finite W A) : Set (A × W) := p.run.run

def ofOutcomes (s : Set (A × W)) : Finite W A := WriterT.mk (show SetM _ from s)

/-- Interpret the log of each outcome through a monoid homomorphism. -/
def mapLog [Monoid W] [Monoid V] (h : W →* V) (p : Finite W A) : Finite V A :=
  ofOutcomes (Prod.map id h '' p.outcomes)

variable [Monoid W]

/-- A finite run ends in a return. The accumulated log follows execution order. -/
inductive Runs (f : A → Finite W (B ⊕ A)) : A → B → W → Prop
  | done {a b w} : (.inl b, w) ∈ (f a).outcomes → Runs f a b w
  | more {a next b u v} :
      (.inr next, u) ∈ (f a).outcomes → Runs f next b v → Runs f a b (u * v)

/-- Unfold once in the pointwise inclusion order on observations. -/
def unfoldLoop (f : A → Finite W (B ⊕ A)) : (A → Set (B × W)) →o (A → Set (B × W)) where
  toFun k a := {p | (.inl p.1, p.2) ∈ (f a).outcomes ∨
    ∃ next u v, (.inr next, u) ∈ (f a).outcomes ∧ (p.1, v) ∈ k next ∧ u * v = p.2}
  monotone' := by
    rintro k l h a p (done | ⟨next, u, v, edge, tail, eq⟩)
    · exact Or.inl done
    · exact Or.inr ⟨next, u, v, edge, h next tail, eq⟩

end Finite

namespace Tagged

variable {W V T A : Type u}

def outcomes (p : Tagged W T A) : Set (Except T A × W) := p.run.outcomes

def ofOutcomes (s : Set (Except T A × W)) : Tagged W T A := ExceptT.mk (Finite.ofOutcomes s)

/-- A branch explicitly supplies an incomplete observation with its log. -/
def incomplete (tag : T) (w : W) : Tagged W T A := ofOutcomes {(.error tag, w)}

variable [Monoid W]

/-- Embed successful observations as successful branches of the tagged semantics. -/
def includeResults (p : Finite W A) : Tagged W T A := ExceptT.mk (p >>= pure ∘ Except.ok)

/-- Interpret every log and retain the return value or incomplete tag. -/
def mapLog [Monoid V] (h : W →* V) (p : Tagged W T A) : Tagged V T A :=
  ExceptT.mk (p.run.mapLog h)

/-- Add explicitly supplied incomplete observations as alternatives. -/
def withIncomplete (tag : T) (prefixes : Set W) (p : Tagged W T A) : Tagged W T A :=
  ofOutcomes (p.outcomes ∪ ((fun w => (Except.error tag, w)) '' prefixes))

end Tagged
end Silmaril.Semantics.NondeterministicTrace

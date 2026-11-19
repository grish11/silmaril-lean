module

public import Mathlib.Order.Closure
public import Mathlib.Order.CompleteLatticeIntervals
public import Mathlib.Order.Hom.CompleteLattice

/-! # Abstract judgment signatures and positive laws

No executions, graphs, memory, equality decisions, enumerations, or support/exit
operations occur here. Even the family of judgment shapes is a parameter.
A raw model is a set of typed atoms. A law is a fixed positive implication
from a possibly infinite set of atoms to one atom. Side conditions select the
rule set independently of the model; no negative or existential model tests
are hidden in rule applicability.
-/

@[expose] public section
namespace Silmaril.Semantics.Region.Abstract
universe u v

/-- Arbitrary judgment shapes with their typed arguments. -/
structure Signature where
  Shape : Type u
  Args : Shape → Type v

abbrev Signature.Atom (S : Signature.{u, v}) := Sigma S.Args
abbrev RawModel (Atom : Type u) := Set Atom
abbrev Signature.Model (S : Signature.{u, v}) := RawModel S.Atom

/-- Infinitary Horn-style rule. All side conditions belong to membership in
`Rules`, fixed before choosing a model. Empty premises express facts. -/
structure Rule (Atom : Type u) where
  premises : Set Atom
  head : Atom

abbrev Rules (Atom : Type u) := Set (Rule Atom)

def Closed {Atom : Type u} (rules : Rules Atom) (M : RawModel Atom) : Prop :=
  ∀ rule ∈ rules, rule.premises ⊆ M → rule.head ∈ M

/-- Intersection of every closed extension. Existence needs no search or
finiteness: the full atom set is always closed. -/
def closure {Atom : Type u} (rules : Rules Atom) (M : RawModel Atom) : RawModel Atom :=
  {a | ∀ N, Closed rules N → M ⊆ N → a ∈ N}

abbrev ClosedModel {Atom : Type u} (rules : Rules Atom) := {M : RawModel Atom // Closed rules M}

/-- Fixing a lawful ceiling is a different stratum from requiring arbitrary
semantic soundness/nonvacuity of each model. -/
abbrev Below {Atom : Type u} {rules : Rules Atom} (ceiling : ClosedModel rules) :=
  Set.Iic ceiling

/-- Renaming/reduct of raw judgments, independent of any law preservation. -/
def reindex {Atom : Type u} {Other : Type v} (f : Atom → Other)
    (M : RawModel Other) : RawModel Atom := f ⁻¹' M

/-- Existential forgetting/direct image. Unlike reduct, it need not preserve
intersections, because the witnesses for different models can differ. -/
def forget {Atom : Type u} {Other : Type v} (f : Atom → Other)
    (M : RawModel Atom) : RawModel Other := f '' M

/-- Fixed rule-transport premise for reducts. It does not inspect any model. -/
def RuleMap {Atom : Type u} {Other : Type v} (f : Atom → Other)
    (source : Rules Atom) (target : Rules Other) : Prop :=
  ∀ r ∈ source, ∃ t ∈ target, t.head = f r.head ∧ t.premises ⊆ f '' r.premises

end Silmaril.Semantics.Region.Abstract

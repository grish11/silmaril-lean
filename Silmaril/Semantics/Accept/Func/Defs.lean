module

public import Silmaril.Semantics.Accept.Rel.Defs

/-!
# The functional shape of relations

A relation `R : α -|> β` (Mathlib's `SetRel α β`, read as a program observed as pairs
(input, output)) can be classified by how many outputs an input has and how many inputs an
output has:

* `Total R`: every input has at least one output (left-total; Mathlib's `Relator.LeftTotal`,
  CSLib's `Relation.Serial` for homogeneous relations, `R.dom = Set.univ`);
* `SingleValued R`: every input has at most one output (right-unique, a partial function;
  Mathlib's `Relator.RightUnique`, and exactly the graphs `PFun.graph'` of `α →. β`);
* `Surjective R`: every output is produced by some input (right-total; `Relator.RightTotal`,
  `R.cod = Set.univ`);
* `Injective R`: an output determines its input (left-unique; `Relator.LeftUnique`,
  equivalently `R.inv` is single-valued);
* `Functional R := Total R ∧ SingleValued R`: exactly one output per input, i.e. `R` is the
  graph `Function.graph f` of a unique total map `f`;
* `OneToOne R := Functional R ∧ Injective R ∧ Surjective R`: the graph of a bijection.

`Injective ∧ SingleValued` is Mathlib's `Relator.BiUnique`. The four basic notions are stated
in exactly the shape of the `Relator` definitions, so the bridges in `Thms` are definitional.

Functions can be extracted back from relations (classically, so noncomputably):

* `toPartial R : α → Option β` picks some output when there is one, and `none` otherwise;
  for a single-valued `R`, `ofPartial (toPartial R) = R`;
* `toFun h : α → β` picks an output of each input given `h : Total R`; for a functional `R`,
  `Function.graph (toFun h) = R`.
-/

@[expose] public section

namespace Silmaril.Accept

universe u v

open scoped SetRel

variable {α : Type u} {β : Type v}

/-- Every input has an output (left-total). -/
def Total (R : α -|> β) : Prop := ∀ a, ∃ b, a ~[R] b

/-- Every input has at most one output (right-unique: a partial function). -/
def SingleValued (R : α -|> β) : Prop := ∀ ⦃a b b'⦄, a ~[R] b → a ~[R] b' → b = b'

/-- Every output is produced by some input (right-total). -/
def Surjective (R : α -|> β) : Prop := ∀ b, ∃ a, a ~[R] b

/-- An output determines its input (left-unique). -/
def Injective (R : α -|> β) : Prop := ∀ ⦃a a' b⦄, a ~[R] b → a' ~[R] b → a = a'

/-- Exactly one output per input: the graph of a total map. -/
def Functional (R : α -|> β) : Prop := Total R ∧ SingleValued R

/-- The graph of a bijection: functional, injective and surjective. -/
def OneToOne (R : α -|> β) : Prop := Functional R ∧ Injective R ∧ Surjective R

open Classical in
/-- Some output of `a` along `R` if there is one (classical choice), `none` otherwise. -/
noncomputable def toPartial (R : α -|> β) : α → Option β :=
  fun a => if h : ∃ b, a ~[R] b then some h.choose else none

/-- An output of each input of a total relation (classical choice). -/
noncomputable def toFun {R : α -|> β} (h : Total R) : α → β := fun a => (h a).choose

end Silmaril.Accept

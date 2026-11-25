module

public import Silmaril.SSA.RVSDG.Categorical.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Defs

/-! # Ordered finite selector types in λSSA

A selector for `n + 1` arms is the right-associated sum of `n + 1`
copies of the unit type. This file gives the type, the actual λSSA
tag expressions and the ordered legs of the interpreted coproduct.
-/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA (Tm)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel)

universe u v d h
variable {τ : Type u} [TypeFormers τ] {Φ : Type v}

/-- `selectorType n` has `n + 1` alternatives. The first tag is on the left. -/
def selectorType : Nat → τ
  | 0 => unit
  | n + 1 => coprod unit (selectorType n)

/-- Canonical λSSA syntax for a tag. Each right injection advances one arm. -/
def selectorLiteral : (n : Nat) → Fin (n + 1) → Tm Φ
  | 0, _ => .unit
  | n + 1, i => Fin.cases (.inl .unit) (fun j => .inr (selectorLiteral n j)) i

variable {D : Type d} [Category.{h} D] [CartesianMonoidalCategory D] [HasFiniteCoproducts D]
variable (M : TypeModel τ D)

/-- The leg for each tag, using the chosen λSSA unit and coproduct isomorphisms. -/
noncomputable def selectorTag :
    (n : Nat) → Fin (n + 1) → (𝟙_ D ⟶ M.obj (selectorType n))
  | 0, _ => M.unitIso.inv
  | n + 1, i => Fin.cases
    (M.unitIso.inv ≫ coprod.inl ≫ (M.coprodIso _ _).inv)
    (fun j => selectorTag n j ≫ coprod.inr ≫ (M.coprodIso _ _).inv) i

noncomputable def ssaSelectorCofan (n : Nat) : Cofan (fun _ : Fin (n + 1) => 𝟙_ D) :=
  Cofan.mk (M.obj (selectorType n)) (selectorTag M n)

/-- The RVSDG cocone after removing the unit payload. -/
def rvSelectorCofan (sel : Categorical.Selectors D) (n : Nat) : Cofan (fun _ : Fin n => 𝟙_ D) :=
  Cofan.mk (sel.obj n) sel.tag

end Silmaril.SSA.RVSDG.LambdaSSA

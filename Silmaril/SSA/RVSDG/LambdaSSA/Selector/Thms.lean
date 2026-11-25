module

public import Silmaril.SSA.RVSDG.LambdaSSA.Selector.Defs
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Selector

/-! # The λSSA finite sum and RVSDG selector agree in tag order -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA (Tm)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel)

universe u v d h
variable {τ : Type u} [TypeFormers τ] {Φ : Type v}

theorem selectorLiteral_typing [HasTy Φ τ] {Γ : List τ} (n : Nat) (i : Fin (n + 1)) :
    Tm.HasType Γ (selectorLiteral (Φ := Φ) n i) (selectorType n) :=
  Proofs.selector_typing n i

variable {D : Type d} [Category.{h} D] [CartesianMonoidalCategory D] [HasFiniteCoproducts D]
variable (M : TypeModel τ D) (sel : Categorical.Selectors D)

/-- Both interpretations are coproducts of `n + 1` copies of the tensor unit. -/
noncomputable def selectorIso (n : Nat) : M.obj (selectorType n) ≅ sel.obj (n + 1) :=
  (Proofs.ssa_selector_colimit M n).coconePointUniqueUpToIso (Proofs.rv_selector_colimit sel (n + 1))

/-- The isomorphism preserves node arm numbers, including with opaque
choices of coproduct objects and λSSA type-model isomorphisms. -/
theorem selectorIso_tag (n : Nat) (i : Fin (n + 1)) :
    selectorTag M n i ≫ (selectorIso M sel n).hom = sel.tag i :=
  (Proofs.ssa_selector_colimit M n).comp_coconePointUniqueUpToIso_hom
    (Proofs.rv_selector_colimit sel (n + 1)) ⟨i⟩

end Silmaril.SSA.RVSDG.LambdaSSA

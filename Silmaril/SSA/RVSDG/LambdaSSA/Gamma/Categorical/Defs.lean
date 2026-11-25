module

public import Silmaril.SSA.RVSDG.LambdaSSA.Gamma.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Selector.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.Categorical.Defs

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory (fst snd lift)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical (ctxObj)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel)

universe u v d h
variable {τ : Type u} {Φ : Type v} [TypeFormers τ] [HasTy Φ τ]
variable {D : Type d} [Category.{h} D] [CartesianMonoidalCategory D] [HasFiniteCoproducts D]

/-- Restore the λSSA case context with the selector as its newest entry. -/
noncomputable def gammaEntryMap (M : TypeModel τ D) (sel : Categorical.Selectors D)
    (prim : ∀ f : Φ, M.obj (instrSrc f) ⟶ M.obj (instrTrg f)) (extra : Nat) (Γ : List τ) :
    (valueModel M sel prim).ports (.control (extra + 2) :: inputs Γ) ⟶
      ctxObj M (selectorType (extra + 1) :: Γ) :=
  lift (snd _ _ ≫ entryMap M Γ sel prim) (fst _ _ ≫ (selectorIso M sel (extra + 1)).inv)

end Silmaril.SSA.RVSDG.LambdaSSA

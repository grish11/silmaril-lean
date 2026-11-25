module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Thms

/-! # Closed let-η soundness for exact LetIter -/

@[expose] public section

namespace Silmaril.Isotope.LetIter.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.LocallyNameless (Derivation Tm)

/-- Let-η on closed terms, quantified over small strong Elgot Freyd models. -/
def ClosedLetEtaSound : Prop :=
  ∀ {V C : Type 1} [Category.{0} V] [Category.{0} C]
    [CartesianMonoidalCategory V] [SymmetricCategory V]
    [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
    [HasFiniteCoproducts V] [HasFiniteCoproducts C]
    [DistributiveTensor V] [DistributivePremonoidalCategory C]
    [Iteration C] [ElgotCategory C]
    (J : V ⥤ C) [StrongElgotFreydCategory J]
    {τ : Type 1} [TypeFormers τ] (M : TypeModel τ V)
    {Φ : Type} [HasTy Φ τ] [InstructionModel J M Φ]
    {t : Tm Empty Φ 0} {A : τ}
    (d : Derivation Φ (Ctx.nil : Ctx Empty τ) .nil t A),
    let v : Derivation Φ (Ctx.nil : Ctx Empty τ) (.snoc .nil A) (.bv 0) A := .bv
    denote J M (.let₁ d v) = denote J M d

end Silmaril.Isotope.LetIter.Semantics.Categorical

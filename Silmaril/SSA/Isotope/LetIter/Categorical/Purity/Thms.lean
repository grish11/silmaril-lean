module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.Categorical.Purity

/-! # Value factorization of exact categorical LetIter denotations -/

public section

namespace Silmaril.Isotope.LetIter.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.LocallyNameless (Derivation Tm Pure)

universe v₁ v₂ u₁ u₂ u₃ u₄ u₅ u₆

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : V ⥤ C) [StrongElgotFreydCategory J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {ν : Type u₄} [DecidableEq ν]
  {Φ : Type u₅} [HasTy Φ τ] [InstructionModel J M Φ]
  {ε : Type u₆} [HasEff Φ ε] {pureEff : ε}

/-- A syntactically pure exact LetIter derivation denotes the image of a value
arrow if each primitive instruction at the pure effect does. -/
theorem denote_pure_factor
    (hInstr : ∀ f : Φ, IsPure pureEff f →
      ∃ p : M.obj (instrSrc f) ⟶ M.obj (instrTrg f),
        InstructionModel.denote (J := J) (M := M) f = J.map p)
    {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ n} {A : τ}
    (d : Derivation Φ Γ β t A) (hp : Pure pureEff t) :
    ∃ p : envObj M Γ β ⟶ M.obj A, denote J M d = J.map p :=
  denote_pure_factor_proof J M hInstr d hp

end Silmaril.Isotope.LetIter.Semantics.Categorical

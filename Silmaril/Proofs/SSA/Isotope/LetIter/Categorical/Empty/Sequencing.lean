module

public import Silmaril.SSA.Isotope.LetIter.Categorical.LetEta.Thms

public section

namespace Silmaril.Isotope.LetIter.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.LocallyNameless (Derivation Tm)

universe v₁ v₂ u₁ u₂ u₃ u₄ u₅

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {ν : Type u₄} [DecidableEq ν]
  {Φ : Type u₅} [HasTy Φ τ] [InstructionModel J M Φ]

/-- Categorical empty elimination can sequence its scrutinee explicitly. -/
theorem denote_let_abort_proof {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ n}
    (d : Derivation Φ Γ β t (empty : τ)) (A : τ) :
    denote J M (.let₁ d (.abort (C := A) (.bv (ι := 0)))) = denote J M (.abort (C := A) d) := by
  let p := J.map (M.emptyIsInitial.to (M.obj A))
  calc
    _ = denote J M (.let₁ d (.bv (ι := 0))) ≫ p := by
      simp only [denote, ProofRelevant.Semantics.Categorical.bind]
      let e := ProofRelevant.Semantics.Categorical.extend J (denote J M d)
      let f := J.map (envSnocIso M Γ β (empty : τ)).hom
      let g := J.map (boundVar M (Γ := Γ) (β := .snoc β (empty : τ)) 0)
      exact ((Category.assoc e (f ≫ g) p).trans
        (congrArg (fun k => e ≫ k) (Category.assoc f g p))).symm
    _ = _ := congrArg (fun f => f ≫ p) (denote_let_eta_of_centralUnit J M d)

end Silmaril.Isotope.LetIter.Semantics.Categorical

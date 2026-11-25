module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Iteration.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Sequencing.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.Categorical.Sequencing.Uniformity

/-! # Native LetIter typed uniformity -/

public section

namespace Silmaril.Isotope.LetIter.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory PremonoidalCategory
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (duplicate)
open scoped MonoidalCategory

universe u₁ u₂ v₁ v₂
variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]

open Silmaril.Isotope.LetIter.LocallyNameless

universe u v w
variable {τ : Type u} [TypeFormers τ] {ν : Type w} [DecidableEq ν]
  {Φ : Type v} [HasTy Φ τ] {Γ : Ctx ν τ}
  (M : TypeModel τ V) [InstructionModel J M Φ]

local notation "Env" => envObj M Γ
local notation "tensorIso" => Functor.StrongPremonoidal.tensorIso (J := J)

/-- The exact uniformity equation follows from the denotation of its state-change square. -/
theorem denote_iter_uniformity_of_value {n : Nat} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {h b b' : Tm ν Φ (n + 1)} {A X B : τ}
    (central : IsCentral (J.map (duplicate (Env β)) ≫ (tensorIso (Env β) (Env β)).inv))
    (da : Derivation Φ Γ β a A)
    (dh : Derivation Φ Γ (.snoc β A) h X)
    (db : Derivation Φ Γ (.snoc β A) b (coprod B A))
    (db' : Derivation Φ Γ (.snoc β X) b' (coprod B X))
    (u : Env (.snoc β A) ⟶ M.obj X) (pureMap : denote J M dh = J.map u)
    (square : denote J M (.case db (.inl (.bv (ι := 0)))
        (.inr (dh.rename (TypedRenaming.underBinder β A A)))) =
      denote J M ((db'.rename (TypedRenaming.underBinder β A X)).instantiate dh)) :
    denote J M (.iter da db) = denote J M (.iter (.let₁ da dh) db') :=
  denote_iter_uniformity_of_value_proof J M central da dh db db' u pureMap square

/-- A syntactically pure state change supplies the value arrow in native uniformity. -/
theorem denote_iter_uniformity_of_pure {n : Nat} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {h b b' : Tm ν Φ (n + 1)} {A X B : τ}
    (central : IsCentral (J.map (duplicate (Env β)) ≫ (tensorIso (Env β) (Env β)).inv))
    (da : Derivation Φ Γ β a A)
    (dh : Derivation Φ Γ (.snoc β A) h X)
    (db : Derivation Φ Γ (.snoc β A) b (coprod B A))
    (db' : Derivation Φ Γ (.snoc β X) b' (coprod B X))
    {ε : Type*} [HasEff Φ ε] {pe : ε}
    (pureInstr : ∀ f : Φ, IsPure pe f → ∃ p : M.obj (instrSrc f) ⟶ M.obj (instrTrg f),
      InstructionModel.denote (J := J) (M := M) f = J.map p)
    (pure : Pure pe h)
    (square : denote J M (.case db (.inl (.bv (ι := 0)))
        (.inr (dh.rename (TypedRenaming.underBinder β A A)))) =
      denote J M ((db'.rename (TypedRenaming.underBinder β A X)).instantiate dh)) :
    denote J M (.iter da db) = denote J M (.iter (.let₁ da dh) db') :=
  denote_iter_uniformity_of_pure_proof J M central da dh db db' pureInstr pure square

end Silmaril.Isotope.LetIter.Semantics.Categorical

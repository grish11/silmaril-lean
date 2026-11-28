module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Eta.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CategoricalEntryLet

/-! # Entry-let sequencing at arbitrary CFG arity -/

public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.DeBruijn (lift)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]
  [RegionTypingCoherent (Φ := Φ) J M]

/-- A typed entry let can precede the literal flat CFG in the existing
coherent shared-tensor semantics. All local blocks are weakened past the
new payload binder. The proof uses categorical CFG η with branch arguments
bound once, so the blocks and the entry continuation may contain arbitrary
typed computations and recursive control. -/
theorem denoteRegion_cfgEntryLet
    (shared : ∀ E X : V, ∃ h : J.obj E ⊗ J.obj X = J.obj (E ⊗ X),
      Functor.StrongPremonoidal.tensorIso (J := J) E X = eqToIso h)
    {n : Nat} {Γ : VCtx τ} {L : LCtx τ} {S : τ} {a : Tm Φ} {d : Region Φ}
    {blocks : Fin n → Region Φ} (R : Fin n → τ)
    (ha : Tm.HasType Γ a S)
    (hd : Region.HasType (S :: Γ) d (List.ofFn R ++ L))
    (hb : ∀ i, Region.HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L)) :
    denoteRegion J M (.cfg R (.let₁ ha hd) hb) =
      denoteRegion J M (.let₁ ha (.cfg R hd
        (fun i => (hb i).renameVars ((Ren.wk Γ S).lift (R i))))) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CategoricalEntryLet.denoteRegion_cfgEntryLet
    J M shared R ha hd hb

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical

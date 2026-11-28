module

public import Silmaril.SSA.Isotope.LetParIter.Categorical.Defs
public import Silmaril.SSA.Isotope.LetParIter.Substitution.Defs
public import Silmaril.SSA.Isotope.LetIter.Categorical.Substitution.Environment.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Naturality.Thms
public import Silmaril.Semantics.Categories.Freyd.Parallel.Thms

public section

namespace Silmaril.Isotope.LetParIter.Categorical

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped MonoidalCategory
open Parallel (Derivation)
open LetIter.Semantics.Categorical
  (TypeModel InstructionModel envObj freeLookup boundVar envSnocIso envPairHom dropSlot
    envRenameMap envRenameMap_free envRenameMap_bound envRenameMap_snoc envRenameMap_pair
    bind_pre_map pair_pre_map case_pre_map contextualLoop_pre_map)

universe v₁ v₂ u₁ u₂ u v w

variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] [∀ X Y : C, Preorder (X ⟶ Y)]
  (J : V ⥤ C) [StrongElgotFreydCategory J] (P : FreydCategory.OrderedParallel J)
  {τ : Type u} [TypeFormers τ] (M : TypeModel τ V)
  {ν : Type v} [DecidableEq ν] {Φ : Type w} [HasTy Φ τ] [InstructionModel J M Φ]
  {Γ : Ctx ν τ}

set_option backward.isDefEq.respectTransparency false in
private theorem denote_cast {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ n}
    {A B : τ} (h : A = B) (d : Derivation Φ Γ β t A) :
    denote J P M (h ▸ d) = denote J P M d ≫ J.map (eqToHom (congrArg M.obj h)) := by
  cases h
  simp

set_option backward.isDefEq.respectTransparency false in
theorem denote_rename_proof {n : Nat} {β : BoundCtx τ n}
    {t : Tm ν Φ n} {A : τ} (d : Derivation Φ Γ β t A) :
    ∀ {k : Nat} {δ : BoundCtx τ k} (r : BoundCtx.Renaming β δ),
      denote J P M (Typing.rename r d) = J.map (envRenameMap M Γ r) ≫ denote J P M d := by
  induction d with
  | fv h =>
    intro k δ r
    simp only [Typing.rename, denote, ← J.map_comp, freeLookup, ← Category.assoc,
      envRenameMap_free]
  | @bv n β i =>
    intro k δ r
    simp only [Typing.rename, denote_cast, denote, ← J.map_comp, envRenameMap_bound]
  | op _ ih | inl _ ih | inr _ ih | abort _ ih =>
    intro k δ r
    simp only [Typing.rename, denote, ih, Category.assoc]
  | let₁ _ _ ih₁ ih₂ =>
    intro k δ r
    simp only [Typing.rename, denote, ih₁, ih₂]
    rw [← J.map_comp_assoc, envRenameMap_snoc, J.map_comp_assoc, bind_pre_map]
  | unit =>
    intro k δ r
    simp only [Typing.rename, denote, ← J.map_comp, ← Category.assoc,
      SemiCartesianMonoidalCategory.comp_toUnit]
  | pair _ _ ih₁ ih₂ =>
    intro k δ r
    simp only [Typing.rename, denote, ih₁, ih₂, pair_pre_map, Category.assoc]
  | let₂ _ _ ih₁ ih₂ =>
    intro k δ r
    simp only [Typing.rename, denote, ih₁, ih₂, MonoidalCategory.id_tensorHom]
    rw [← J.map_comp_assoc (envPairHom M Γ δ _ _), envRenameMap_pair, J.map_comp_assoc,
      ← J.map_comp_assoc (_ ◁ (M.productIso _ _).hom),
      MonoidalCategory.whisker_exchange, J.map_comp_assoc, bind_pre_map]
  | case _ _ _ ih₁ ih₂ ih₃ =>
    intro k δ r
    simp only [Typing.rename, denote, ih₁, ih₂, ih₃, Category.assoc]
    rw [← J.map_comp_assoc (envSnocIso M Γ δ _).hom, envRenameMap_snoc, J.map_comp_assoc,
      ← J.map_comp_assoc (envSnocIso M Γ δ _).hom, envRenameMap_snoc, J.map_comp_assoc,
      case_pre_map]
  | iter _ _ ih₁ ih₂ =>
    intro k δ r
    simp only [Typing.rename, denote, ih₁, ih₂, Category.assoc]
    rw [← J.map_comp_assoc, envRenameMap_snoc, J.map_comp_assoc, contextualLoop_pre_map,
      bind_pre_map]
  | par _ _ ih₁ ih₂ =>
    intro k δ r
    simp only [Typing.rename, denote, ih₁, ih₂, ← P.par_reindex, Category.assoc]

end Silmaril.Isotope.LetParIter.Categorical

module

public import Silmaril.Proofs.SSA.Isotope.LetParIter.Categorical.Environment
public import Silmaril.Proofs.SSA.Isotope.LetParIter.Categorical.Purity
public import Silmaril.Proofs.SSA.Isotope.LetParIter.Categorical.Renaming

public section

namespace Silmaril.Isotope.LetParIter.Categorical

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped MonoidalCategory
open Parallel (Derivation Pure)
open LetIter.Semantics.Categorical
  (TypeModel InstructionModel envObj freeLookup envSnocIso envPairHom dropSlot
    envSubstMap bind_pre_map pair_pre_map case_pre_map contextualLoop_pre_map extend_map)

universe v₁ v₂ u₁ u₂ u v w q

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

local notation "Env" => envObj M Γ
set_option backward.isDefEq.respectTransparency false

private theorem subst_up_value {n k : Nat} {β : BoundCtx τ n} {δ : BoundCtx τ k}
    {σ : Fin n → Tm ν Φ k} (s : Subst (Γ := Γ) β δ σ)
    (p : ∀ i, Env δ ⟶ M.obj (β.get i)) (hs : ∀ i, denote J P M (s i) = J.map (p i))
    (A : τ) (i : Fin (n + 1)) : denote J P M (s.up A i) = J.map (upValues M p A i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Subst.up, Fin.cases_zero, upValues, denote]
  · simp only [Subst.up, Fin.cases_succ, upValues, denote_rename_proof,
      envRenameMap_succ_proof, hs j, J.map_comp]

theorem denote_bsubst_proof {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ n} {A : τ}
    (d : Derivation Φ Γ β t A) : ∀ {k : Nat} {δ : BoundCtx τ k} {σ : Fin n → Tm ν Φ k}
      (s : Subst (Γ := Γ) β δ σ) (p : ∀ i, Env δ ⟶ M.obj (β.get i)),
      (∀ i, denote J P M (s i) = J.map (p i)) →
      denote J P M (Typing.bsubst s d) = J.map (envSubstMap M Γ β δ p) ≫ denote J P M d := by
  induction d with
  | fv h =>
    intro k δ σ s p hs
    simp only [Typing.bsubst, denote, ← J.map_comp, freeLookup, ← Category.assoc,
      envSubstMap, lift_fst]
  | @bv n β i =>
    intro k δ σ s p hs
    simp only [Typing.bsubst, denote, ← J.map_comp, envSubstMap_bound]
    exact hs i
  | op _ ih | inl _ ih | inr _ ih | abort _ ih =>
    intro k δ σ s p hs
    simp only [Typing.bsubst, denote, ih s p hs, Category.assoc]
  | let₁ _ _ ih₁ ih₂ =>
    intro k δ σ s p hs
    simp only [Typing.bsubst, denote, ih₁ s p hs, ih₂ _ _ (subst_up_value J P M s p hs _)]
    rw [← J.map_comp_assoc, envSubstMap_snoc, J.map_comp_assoc, bind_pre_map]
  | unit =>
    intro k δ σ s p hs
    simp only [Typing.bsubst, denote, ← J.map_comp, ← Category.assoc,
      SemiCartesianMonoidalCategory.comp_toUnit]
  | pair _ _ ih₁ ih₂ =>
    intro k δ σ s p hs
    simp only [Typing.bsubst, denote, ih₁ s p hs, ih₂ s p hs, pair_pre_map, Category.assoc]
  | let₂ _ _ ih₁ ih₂ =>
    intro k δ σ s p hs
    simp only [Typing.bsubst, denote, ih₁ s p hs,
      ih₂ _ _ (subst_up_value J P M _ _ (subst_up_value J P M s p hs _) _),
      MonoidalCategory.id_tensorHom]
    rw [← J.map_comp_assoc (envPairHom M Γ δ _ _), envSubstMap_pair, J.map_comp_assoc,
      ← J.map_comp_assoc (_ ◁ (M.productIso _ _).hom),
      MonoidalCategory.whisker_exchange, J.map_comp_assoc, bind_pre_map]
  | case _ _ _ ih₁ ih₂ ih₃ =>
    intro k δ σ s p hs
    simp only [Typing.bsubst, denote, ih₁ s p hs, ih₂ _ _ (subst_up_value J P M s p hs _),
      ih₃ _ _ (subst_up_value J P M s p hs _), Category.assoc]
    rw [← J.map_comp_assoc (envSnocIso M Γ δ _).hom, envSubstMap_snoc, J.map_comp_assoc,
      ← J.map_comp_assoc (envSnocIso M Γ δ _).hom, envSubstMap_snoc, J.map_comp_assoc,
      case_pre_map]
  | iter _ _ ih₁ ih₂ =>
    intro k δ σ s p hs
    simp only [Typing.bsubst, denote, ih₁ s p hs, ih₂ _ _ (subst_up_value J P M s p hs _),
      Category.assoc]
    rw [← J.map_comp_assoc, envSubstMap_snoc, J.map_comp_assoc, contextualLoop_pre_map,
      bind_pre_map]
  | par _ _ ih₁ ih₂ =>
    intro k δ σ s p hs
    simp only [Typing.bsubst, denote, ih₁ s p hs, ih₂ s p hs, ← P.par_reindex, Category.assoc]

theorem denote_instantiate_proof {n : Nat} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)} {A B : τ}
    (da : Derivation Φ Γ β a A) (db : Derivation Φ Γ (.snoc β A) b B)
    (f : Env β ⟶ M.obj A) (hf : denote J P M da = J.map f) :
    denote J P M (Typing.instantiate db da) =
      J.map (lift (𝟙 (Env β)) f ≫ (envSnocIso M Γ β A).hom) ≫ denote J P M db := by
  rw [Typing.instantiate, denote_bsubst_proof J P M db _ (Fin.cases f (LetIter.Semantics.Categorical.boundVar M)),
    envSubstMap_instantiate]
  exact fun i => Fin.cases hf (fun _ => rfl) i

theorem letBeta_sound_proof {n : Nat} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)} {A B : τ}
    (da : Derivation Φ Γ β a A) (db : Derivation Φ Γ (.snoc β A) b B)
    (f : Env β ⟶ M.obj A) (hf : denote J P M da = J.map f) :
    denote J P M (.let₁ da db) = denote J P M (Typing.instantiate db da) := by
  rw [denote_instantiate_proof J P M da db f hf, denote, hf,
    LetIter.ProofRelevant.Semantics.Categorical.bind, extend_map, J.map_comp_assoc]

end Silmaril.Isotope.LetParIter.Categorical

module

public import Silmaril.SSA.Isotope.LetParIter.Categorical.Soundness.Defs
public import Silmaril.SSA.Isotope.LetParIter.Categorical.Thms

public section

namespace Silmaril.Isotope.LetParIter.Categorical

open CategoryTheory CategoryTheory.Limits
open Parallel (Derivation)
open LetIter.Semantics.Categorical (TypeModel InstructionModel envObj)

universe u₁ u₂ v₁ v₂ u v w q

variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] [∀ X Y : C, Preorder (X ⟶ Y)]
  (J : V ⥤ C) [StrongElgotFreydCategory J] (P : FreydCategory.OrderedParallel J)
  {τ : Type u} [TypeFormers τ] [Subtyping τ] (M : TypeModel τ V)
  {ν : Type v} [DecidableEq ν] {Φ : Type w} [HasTy Φ τ] [InstructionModel J M Φ]
  {ε : Type q} [HasEff Φ ε] {pe : ε}

set_option backward.isDefEq.respectTransparency false in
theorem sound_of_native_proof (L : Laws J P) (central : CentralDiagonal J)
    (pureInstr : ∀ f : Φ, IsPure pe f → ∃ p : M.obj (instrSrc f) ⟶ M.obj (instrTrg f),
      InstructionModel.denote (J := J) (M := M) f = J.map p)
    (nativeSound : FixedNativeSound (ν := ν) J P M (Φ := Φ) pe)
    {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A : τ}
    {da : Derivation Φ Γ β a A} {db : Derivation Φ Γ β b A}
    (h : Equiv pe Γ da db) : denote J P M da = denote J P M db := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | native da db h => exact nativeSound da db h
  | rename r _ ih => simp only [denote_rename, ih]
  | bsubst s hs _ ih =>
    choose p hp using fun i => denote_pure J P M pureInstr (s i) (hs i)
    simp only [denote_bsubst J P M _ s p hp, ih]
  | op _ ih | inl _ ih | inr _ ih | abort _ ih => simp only [denote, ih]
  | let₁ _ _ ih₁ ih₂ | pair _ _ ih₁ ih₂ | let₂ _ _ ih₁ ih₂ | par _ _ ih₁ ih₂
  | iter _ _ ih₁ ih₂ => simp only [denote, ih₁, ih₂]
  | case _ _ _ ihe ihl ihr => simp only [denote, ihe, ihl, ihr]
  | swap da db => exact swap_sound J P M da db
  | assoc da db dc => exact assoc_sound J P M da db dc
  | purePair ha hb da db => exact purePair_sound J P M pureInstr da db ha hb
  | unitLeft da => exact unitLeft_sound J P M da
  | unitRight da => exact unitRight_sound J P M da
  | map da db df dg hf hg => exact map_sound J P M pureInstr L da db df dg hf hg
  | parCaseLeft de he dl dr dp => exact parCaseLeft_sound J P M pureInstr L de he dl dr dp
  | parCaseRight de he dl dr dp => exact parCaseRight_sound J P M pureInstr L de he dl dr dp
  | letBeta da db ha => exact letBeta_sound J P M pureInstr da db ha
  | letEta da => exact letEta_sound J P M da
  | iterFixpoint da db => exact iterFixpoint_sound J P M da db
  | iterUniformity da dh hp db db' _ ih =>
    obtain ⟨u, hu⟩ := denote_pure J P M pureInstr dh hp
    exact iterUniformity_sound_of_value J P M (central (envObj M Γ _)) da dh db db' u hu ih
  | iterBind da db => exact iterBind_sound J P M da db

end Silmaril.Isotope.LetParIter.Categorical

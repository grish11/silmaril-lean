module

public import Silmaril.Proofs.SSA.Isotope.LetParIter.Categorical.Renaming
public import Silmaril.Proofs.SSA.Isotope.LetParIter.Categorical.Tuples

public section

namespace Silmaril.Isotope.LetParIter.Categorical

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped MonoidalCategory
open Parallel (Derivation Pure)
open LetIter.Semantics.Categorical
  (TypeModel InstructionModel envObj envPairHom envSnocIso envRenameMap pair_maps_eq_map_lift)

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
  {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}

variable (L : Laws J P) {ε : Type q} [HasEff Φ ε] {pe : ε}
  (pureInstr : ∀ f : Φ, IsPure pe f →
    ∃ p : M.obj (instrSrc f) ⟶ M.obj (instrTrg f),
      InstructionModel.denote (J := J) (M := M) f = J.map p)

include L pureInstr

set_option backward.isDefEq.respectTransparency false in
theorem map_sound_proof {a b : Tm ν Φ n} {f g : Tm ν Φ (n + 1)} {A B D E : τ}
    (da : Derivation Φ Γ β a A) (db : Derivation Φ Γ β b B)
    (df : Derivation Φ Γ (.snoc β A) f D) (dg : Derivation Φ Γ (.snoc β B) g E)
    (hf : Pure pe f) (hg : Pure pe g) :
    denote J P M (.par (.let₁ da df) (.let₁ db dg)) =
      denote J P M (.let₂ (.par da db) (.pair (Typing.leftResult df) (Typing.underBinder dg))) := by
  obtain ⟨u, hu⟩ := denote_pure_proof J P M pureInstr df hf
  obtain ⟨v, hv⟩ := denote_pure_proof J P M pureInstr dg hg
  let p := lift (envRenameMap M Γ (Typing.leftResultRenaming β A B) ≫ u)
    (envRenameMap M Γ (BoundCtx.Renaming.underBinder β A B) ≫ v) ≫ (M.productIso D E).inv
  have hp : denote J P M (.pair (Typing.leftResult df) (Typing.underBinder dg)) = J.map p := by
    simp only [p, Typing.leftResult, Typing.underBinder, denote, denote_rename_proof,
      hu, hv, ← J.map_comp, pair_maps_eq_map_lift]
  have route : envPairHom M Γ β A B ≫ p =
      splitContext (envObj M Γ β) (M.obj A) (M.obj B) ≫
        (((envSnocIso M Γ β A).hom ≫ u) ⊗ₘ ((envSnocIso M Γ β B).hom ≫ v)) ≫
          (M.productIso D E).inv := by
    simp only [p, ← Category.assoc]
    congr 1
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst, envPair_leftResult_assoc, tensorHom_fst]
    · simp only [Category.assoc, lift_snd, envPair_underBinder_assoc, tensorHom_snd]
  rw [denote_let₂_pure_tail J P M _ _ p hp, denote_par_unpack J P M, route]
  simp only [denote, hu, hv, LetIter.ProofRelevant.Semantics.Categorical.bind, ← J.map_comp,
    par_context_maps_proof J P L, Category.assoc]

end Silmaril.Isotope.LetParIter.Categorical

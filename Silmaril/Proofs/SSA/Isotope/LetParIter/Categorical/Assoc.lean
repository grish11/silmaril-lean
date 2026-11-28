module

public import Silmaril.Proofs.SSA.Isotope.LetParIter.Categorical.Tuples

public section

namespace Silmaril.Isotope.LetParIter.Categorical

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped MonoidalCategory
open Parallel (Derivation Pure)
open LetIter.Semantics.Categorical
  (TypeModel InstructionModel envObj boundVar envPairHom envSnocIso extend_map extend_postmap
    pair_maps_eq_map_lift)
open LetIter.ProofRelevant.Semantics.Categorical (extend)

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

local notation "R" => envObj M Γ β
local notation "O" => M.obj

set_option backward.isDefEq.respectTransparency false in
theorem assoc_sound_proof {a b c : Tm ν Φ n} {A B D : τ}
    (da : Derivation Φ Γ β a A) (db : Derivation Φ Γ β b B) (dc : Derivation Φ Γ β c D) :
    denote J P M (Typing.assoc (.par (.par da db) dc)) =
      denote J P M (.par da (.par db dc)) := by
  let σ := (β.snoc (product A B)).snoc D
  let δ := (σ.snoc A).snoc B
  let tail : Derivation (tier := .iter) Φ Γ σ _ (product A (product B D)) :=
    .let₂ (.bv (i := 1)) (.pair (.bv (i := 1)) (.pair (.bv (i := 0)) (.bv (i := 2))))
  let fstPair := boundVar M (Γ := Γ) (β := σ) 1 ≫ (M.productIso A B).hom
  let q := lift (boundVar M (Γ := Γ) (β := δ) 1)
    (lift (boundVar M (Γ := Γ) (β := δ) 0) (boundVar M (Γ := Γ) (β := δ) 2) ≫
      (M.productIso B D).inv) ≫ (M.productIso A (product B D)).inv
  let p := lift (𝟙 (envObj M Γ σ)) fstPair ≫ envPairHom M Γ σ A B ≫ q
  have hp : denote J P M tail = J.map p := by
    dsimp only [tail]
    rw [denote_let₂_pure_tail J P M _ _ q (by
      simp only [q, denote, pair_maps_eq_map_lift, ← J.map_comp])]
    simp only [p, fstPair, denote, ← J.map_comp, extend_map]
  let k := (M.productIso A B).hom ▷ O D ≫ (α_ (O A) (O B) (O D)).hom ≫
    O A ◁ (M.productIso B D).inv ≫ (M.productIso A (product B D)).inv
  have route : envPairHom M Γ β (product A B) D ≫ p = snd R _ ≫ k := by
    simp only [p, q, k, ← Category.assoc]
    apply congrArg (fun f : R ⊗ (O (product A B) ⊗ O D) ⟶ O A ⊗ O (product B D) =>
      f ≫ (M.productIso A (product B D)).inv)
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc]
      change _ = snd R _ ≫ (M.productIso A B).hom ▷ O D ≫ (α_ _ _ _).hom ≫
        O A ◁ (M.productIso B D).inv ≫ fst (O A) (O (product B D))
      simp [Category.assoc, fstPair, envPair_one_assoc, envPair_one]
    · simp only [Category.assoc]
      change _ = snd R _ ≫ (M.productIso A B).hom ▷ O D ≫ (α_ _ _ _).hom ≫
        O A ◁ (M.productIso B D).inv ≫ snd (O A) (O (product B D))
      simp only [lift_snd, whiskerLeft_snd]
      simp only [← Category.assoc]
      apply congrArg (fun f : R ⊗ (O (product A B) ⊗ O D) ⟶ O B ⊗ O D =>
        f ≫ (M.productIso B D).inv)
      apply CartesianMonoidalCategory.hom_ext
      · simp only [Category.assoc]
        change _ = snd R _ ≫ (M.productIso A B).hom ▷ O D ≫ (α_ _ _ _).hom ≫
          snd (O A) (O B ⊗ O D) ≫ fst (O B) (O D)
        simp [Category.assoc, fstPair, envPair_zero, envPair_one_assoc]
      · simp only [Category.assoc]
        change _ = snd R _ ≫ (M.productIso A B).hom ▷ O D ≫ (α_ _ _ _).hom ≫
          snd (O A) (O B ⊗ O D) ≫ snd (O B) (O D)
        simp only [lift_snd]
        rw [envPair_two (Γ := Γ) M (β.snoc (product A B)) D A B]
        change envPairHom M Γ β (product A B) D ≫
          lift (𝟙 (envObj M Γ σ)) fstPair ≫ fst (envObj M Γ σ) _ ≫
            boundVar M (Γ := Γ) (β := σ) 0 = _
        rw [lift_fst_assoc, Category.id_comp, envPair_zero]
        simp
  change denote J P M (.let₂ (.par (.par da db) dc) tail) = _
  rw [denote_let₂_result_map J P M _ tail p hp k route, J.map_comp, ← Category.assoc,
    denote_par_unpack J P M]
  simp only [denote, k, J.map_comp]
  have h₁ := P.par_postmap (P.par (denote J P M da) (denote J P M db)) (denote J P M dc)
    (M.productIso A B).inv (𝟙 (O D))
  have h₂ := P.par_postmap (denote J P M da) (P.par (denote J P M db) (denote J P M dc))
    (𝟙 (O A)) (M.productIso B D).inv
  rw [J.map_id, Category.comp_id] at h₁ h₂
  rw [← h₁, ← h₂]
  simp only [Category.assoc, ← J.map_comp_assoc, MonoidalCategory.tensorHom_id,
    MonoidalCategory.id_tensorHom]
  rw [← MonoidalCategory.comp_whiskerRight_assoc, Iso.inv_hom_id,
    MonoidalCategory.id_whiskerRight, Category.id_comp, J.map_comp_assoc,
    ← Category.assoc, P.par_assoc]

end Silmaril.Isotope.LetParIter.Categorical

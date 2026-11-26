module

public import Silmaril.SSA.Isotope.LetParIter.Equations.Defs
public import Silmaril.Proofs.SSA.Isotope.LetParIter.Categorical.Environment
public import Silmaril.Proofs.SSA.Isotope.LetParIter.Categorical.Laws
public import Silmaril.Proofs.SSA.Isotope.LetParIter.Categorical.Purity

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
theorem denote_let₂_pure_tail {a : Tm ν Φ n} {b : Tm ν Φ (n + 2)} {A B D : τ}
    (da : Derivation Φ Γ β a (product A B)) (db : Derivation Φ Γ (.snoc (.snoc β A) B) b D)
    (p : envObj M Γ (.snoc (.snoc β A) B) ⟶ O D) (hp : denote J P M db = J.map p) :
    denote J P M (.let₂ da db) =
      extend J (denote J P M da ≫ J.map (M.productIso A B).hom) ≫
        J.map (envPairHom M Γ β A B ≫ p) := by
  simp only [denote, hp, LetIter.ProofRelevant.Semantics.Categorical.bind, extend_postmap,
    MonoidalCategory.id_tensorHom, J.map_comp, Category.assoc]

theorem denote_let₂_result_map {a : Tm ν Φ n} {b : Tm ν Φ (n + 2)} {A B D : τ}
    (da : Derivation Φ Γ β a (product A B)) (db : Derivation Φ Γ (.snoc (.snoc β A) B) b D)
    (p : envObj M Γ (.snoc (.snoc β A) B) ⟶ O D) (hp : denote J P M db = J.map p)
    (k : O A ⊗ O B ⟶ O D) (route : envPairHom M Γ β A B ≫ p = snd R _ ≫ k) :
    denote J P M (.let₂ da db) = denote J P M da ≫ J.map ((M.productIso A B).hom ≫ k) := by
  rw [denote_let₂_pure_tail J P M da db p hp, route, J.map_comp, ← Category.assoc,
    extend_snd_proof J P, J.map_comp, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
theorem denote_par_unpack {a b : Tm ν Φ n} {A B : τ}
    (da : Derivation Φ Γ β a A) (db : Derivation Φ Γ β b B) :
    denote J P M (.par da db) ≫ J.map (M.productIso A B).hom =
      P.par (denote J P M da) (denote J P M db) := by
  simp only [denote, Category.assoc, ← J.map_comp, Iso.inv_hom_id, J.map_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
theorem swap_sound_proof {a b : Tm ν Φ n} {A B : τ}
    (da : Derivation Φ Γ β a A) (db : Derivation Φ Γ β b B) :
    denote J P M (Typing.swap (.par da db)) = denote J P M (.par db da) := by
  let k := (BraidedCategory.braiding (O A) (O B)).hom ≫ (M.productIso B A).inv
  let p := lift (boundVar M (Γ := Γ) (β := .snoc (.snoc β A) B) 0)
    (boundVar M (Γ := Γ) (β := .snoc (.snoc β A) B) 1) ≫ (M.productIso B A).inv
  have route : envPairHom M Γ β A B ≫ p = snd R _ ≫ k := by
    simp only [p, k, ← Category.assoc]
    congr 1
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst]
      change _ = snd R _ ≫ (BraidedCategory.braiding (O A) (O B)).hom ≫ fst (O B) (O A)
      rw [braiding_hom_fst]
      exact envPair_zero M β A B
    · simp only [Category.assoc, lift_snd]
      change _ = snd R _ ≫ (BraidedCategory.braiding (O A) (O B)).hom ≫ snd (O B) (O A)
      rw [braiding_hom_snd]
      exact envPair_one M β A B
  unfold Typing.swap
  rw [denote_let₂_result_map J P M _ _ p (by simp [p, denote, pair_maps_eq_map_lift]) k route]
  rw [J.map_comp, ← Category.assoc, denote_par_unpack J P M da db]
  simp only [k, J.map_comp, ← Category.assoc, P.par_swap, denote]

set_option backward.isDefEq.respectTransparency false in
theorem unitLeft_sound_proof {a : Tm ν Φ n} {A : τ} (d : Derivation Φ Γ β a A) :
    denote J P M (Typing.dropLeft (.par .unit d)) = denote J P M d := by
  unfold Typing.dropLeft
  rw [denote_let₂_result_map J P M _ _ _ (by rfl) (snd (O unit) (O A)) (envPair_zero M β unit A)]
  rw [J.map_comp, ← Category.assoc, denote_par_unpack J P M .unit d]
  rw [← whiskerRight_toUnit_comp_leftUnitor_hom, ← MonoidalCategory.tensorHom_id, J.map_comp,
    ← Category.assoc]
  have h := P.par_postmap (denote J P M (Derivation.unit (Φ := Φ) (Γ := Γ) (β := β)))
    (denote J P M d) (toUnit (O unit)) (𝟙 (O A))
  rw [h]
  simp only [denote, ← J.map_comp, SemiCartesianMonoidalCategory.comp_toUnit, Category.comp_id,
    J.map_id, P.par_unit_left]

set_option backward.isDefEq.respectTransparency false in
theorem unitRight_sound_proof {a : Tm ν Φ n} {A : τ} (d : Derivation Φ Γ β a A) :
    denote J P M (Typing.dropRight (.par d .unit)) = denote J P M d := by
  unfold Typing.dropRight
  rw [denote_let₂_result_map J P M _ _ _ (by rfl) (fst (O A) (O unit)) (envPair_one M β A unit)]
  rw [J.map_comp, ← Category.assoc, denote_par_unpack J P M d .unit]
  rw [← whiskerLeft_toUnit_comp_rightUnitor_hom, ← MonoidalCategory.id_tensorHom, J.map_comp,
    ← Category.assoc]
  have h := P.par_postmap (denote J P M d)
    (denote J P M (Derivation.unit (Φ := Φ) (Γ := Γ) (β := β))) (𝟙 (O A)) (toUnit (O unit))
  rw [h]
  simp only [denote, ← J.map_comp, SemiCartesianMonoidalCategory.comp_toUnit, Category.comp_id,
    J.map_id, P.par_unit_right]

set_option backward.isDefEq.respectTransparency false in
theorem purePair_sound_proof {ε : Type q} [HasEff Φ ε] {pe : ε}
    (pureInstr : ∀ f : Φ, IsPure pe f →
      ∃ p : O (instrSrc f) ⟶ O (instrTrg f),
        InstructionModel.denote (J := J) (M := M) f = J.map p)
    {a b : Tm ν Φ n} {A B : τ} (da : Derivation Φ Γ β a A) (db : Derivation Φ Γ β b B)
    (ha : Pure pe a) (hb : Pure pe b) :
    denote J P M (.par da db) = denote J P M (.pair da db) := by
  obtain ⟨f, hf⟩ := denote_pure_proof J P M pureInstr da ha
  obtain ⟨g, hg⟩ := denote_pure_proof J P M pureInstr db hb
  simp only [denote, hf, hg, P.par_maps, pair_maps_eq_map_lift]

set_option backward.isDefEq.respectTransparency false in
theorem letEta_sound_proof {a : Tm ν Φ n} {A : τ} (da : Derivation Φ Γ β a A) :
    denote J P M (.let₁ da Typing.newest) = denote J P M da := by
  simp only [Typing.newest, denote, LetIter.ProofRelevant.Semantics.Categorical.bind,
    ← J.map_comp, envSnoc_zero, extend_snd_proof J P]

end Silmaril.Isotope.LetParIter.Categorical

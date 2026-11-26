module

public import Silmaril.SSA.Isotope.LetParIter.Equations.Defs
public import Silmaril.Proofs.SSA.Isotope.LetParIter.Categorical.Environment
public import Silmaril.Proofs.SSA.Isotope.LetParIter.Categorical.Renaming
public import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Thms

public section

namespace Silmaril.Isotope.LetParIter.Categorical

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped MonoidalCategory
set_option backward.isDefEq.respectTransparency false
open Parallel (Derivation)
open LetIter.Semantics.Categorical
  (TypeModel InstructionModel envObj envSnocIso boundVar dropSlot envRenameMap_underBinder
    extend_map case_pre_map contextualLoop_pre_map contextualLoop_fixpoint)
open LetIter.ProofRelevant.Semantics.Categorical (caseWithContext contextualLoop extend)

local notation "bindArrow" => LetIter.ProofRelevant.Semantics.Categorical.bind

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
  {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}

private theorem denote_underBinder {A X Y : τ} {b : Tm ν Φ (n + 1)}
    (d : Derivation Φ Γ (.snoc β Y) b A) :
    J.map (envSnocIso M Γ (.snoc β X) Y).hom ≫ denote J P M (Typing.underBinder d) =
      J.map (dropSlot M β X ▷ M.obj Y) ≫ J.map (envSnocIso M Γ β Y).hom ≫ denote J P M d := by
  rw [Typing.underBinder, denote_rename_proof, ← J.map_comp_assoc,
    envRenameMap_underBinder, J.map_comp_assoc]

private theorem iterNewest {b : Tm ν Φ (n + 1)} {A B : τ}
    (db : Derivation Φ Γ (.snoc β A) b (coprod B A)) :
    J.map (envSnocIso M Γ β A).hom ≫ denote J P M (.iter (h := rfl) Typing.newest (Typing.underBinder db)) =
      contextualLoop J (J.map (envSnocIso M Γ β A).hom ≫ denote J P M db ≫
        J.map (M.coprodIso B A).hom) := by
  let s := (envSnocIso M Γ β A).hom
  let q : envObj M Γ (.snoc β A) ⟶ M.obj A := boundVar M 0
  let k := J.map (M.coprodIso B A).hom
  change J.map s ≫ bindArrow J (J.map q) (contextualLoop J
    (J.map (envSnocIso M Γ (.snoc β A) A).hom ≫ denote J P M (Typing.underBinder db) ≫ k)) = _
  rw [← Category.assoc (J.map (envSnocIso M Γ (.snoc β A) A).hom), denote_underBinder,
    Category.assoc, contextualLoop_pre_map]
  unfold Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind
  rw [extend_map, ← J.map_comp_assoc, ← J.map_comp_assoc]
  have rebind : s ≫ lift (𝟙 _) q ≫ (dropSlot M β A ▷ M.obj A) = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [s, dropSlot]
    · simpa [q] using envSnoc_zero (Γ := Γ) M β A
  rw [Category.assoc s, rebind, J.map_id, Category.id_comp, Category.assoc]

theorem iterBind_sound_proof {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)} {A B : τ}
    (da : Derivation Φ Γ β a A) (db : Derivation Φ Γ (.snoc β A) b (coprod B A)) :
    denote J P M (.iter (h := rfl) da db) =
      denote J P M (.let₁ da (.iter (h := rfl) Typing.newest (Typing.underBinder db))) :=
  congrArg (bindArrow J (denote J P M da)) (iterNewest J P M db).symm

theorem iterFixpoint_sound_proof {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)} {A B : τ}
    (da : Derivation Φ Γ β a A) (db : Derivation Φ Γ (.snoc β A) b (coprod B A)) :
    denote J P M (.iter (h := rfl) da db) =
      denote J P M (.let₁ da (.case (h := hasCase) db Typing.newest
        (.iter (h := rfl) Typing.newest (Typing.underBinder (Typing.underBinder db))))) := by
  let δ := β.snoc A
  let R := envObj M Γ β
  let E := R ⊗ M.obj A
  let s := (envSnocIso M Γ β A).hom
  let q : envObj M Γ (.snoc δ B) ⟶ M.obj B := boundVar M 0
  let k := J.map (M.coprodIso B A).hom
  let db' := Typing.underBinder (X := A) db
  let body := J.map s ≫ denote J P M db ≫ k
  change bindArrow J (denote J P M da) (contextualLoop J body) =
    bindArrow J (denote J P M da) (J.map s ≫ caseWithContext J (denote J P M db ≫ k)
      (J.map (envSnocIso M Γ δ B).hom ≫ J.map q)
      (J.map (envSnocIso M Γ δ A).hom ≫ denote J P M
        (.iter (h := rfl) Typing.newest (Typing.underBinder db'))))
  rw [iterNewest, ← case_pre_map, contextualLoop_fixpoint]
  have exitBranch : J.map (s ▷ M.obj B) ≫ J.map (envSnocIso M Γ δ B).hom ≫ J.map q =
      J.map (snd E (M.obj B)) := by
    rw [← J.map_comp, envSnoc_zero, ← J.map_comp, whiskerRight_snd]
  have resume : J.map (s ▷ M.obj A) ≫ contextualLoop J
      (J.map (envSnocIso M Γ δ A).hom ≫ denote J P M db' ≫ k) =
      J.map (fst R (M.obj A) ▷ M.obj A) ≫ contextualLoop J body := by
    rw [← Category.assoc (J.map (envSnocIso M Γ δ A).hom), denote_underBinder,
      Category.assoc, contextualLoop_pre_map, ← J.map_comp_assoc,
      ← MonoidalCategory.comp_whiskerRight]
    have drop : s ≫ dropSlot M β A = fst R (M.obj A) := by simp [s, dropSlot, R]
    rw [drop, Category.assoc]
  rw [exitBranch, resume]

end Silmaril.Isotope.LetParIter.Categorical

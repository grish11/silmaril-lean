module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Blocks.Constructor.Defs

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ConstructorBlockUniformity

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper (TypeCategory)
open Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
open CategoryTheory CategoryTheory.Limits

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "P" => TypeCategory (τ := τ) Φ

set_option backward.isDefEq.respectTransparency false

theorem iterate_coprod_rows {A D B : P}
    (left : A ⟶ (B ⨿ A) ⨿ D) (right : D ⟶ (B ⨿ A) ⨿ D) :
    let tail := iterate right
    let head := iterate (left ≫ coprod.desc (𝟙 (B ⨿ A)) tail)
    iterate (coprod.desc left right ≫ (coprod.associator B A D).hom) =
      coprod.desc head (tail ≫ coprod.desc (𝟙 B) head) := by
  dsimp only
  let a : τ := A
  let d : τ := D
  let iso := sumIso (Φ := Φ) a d
  let step := coprod.desc left right ≫ (coprod.associator B A D).hom
  have copair {Y : P} (l : A ⟶ Y) (r : D ⟶ Y) :
      blockCopair (A := a) (D := d) l r = iso.hom ≫ coprod.desc l r := by
    apply BinaryCofan.IsColimit.hom_ext (sumCofanIsColimit (Φ := Φ) a d)
    · simp [iso, ← Category.assoc, sumCofan_inl_sumIso_hom]
    · simp [iso, ← Category.assoc, sumCofan_inr_sumIso_hom]
  have leftIn : coprod.inl ≫ iso.inv = (sumCofan (Φ := Φ) a d).inl := by
    rw [← sumCofan_inl_sumIso_hom (Φ := Φ) a d, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have rightIn : coprod.inr ≫ iso.inv = (sumCofan (Φ := Φ) a d).inr := by
    rw [← sumCofan_inr_sumIso_hom (Φ := Φ) a d, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have join : joinBlockExits a d B =
      (coprod.associator B A D).hom ≫ coprod.map (𝟙 B) iso.inv := by
    apply coprod.hom_ext
    · apply coprod.hom_ext
      · simp [joinBlockExits, coprod.associator, Category.assoc]
        rw [coprod.inl_desc, coprod.inl_desc]
      · simp [joinBlockExits, coprod.associator, Category.assoc]
        rw [coprod.inl_desc, coprod.inr_desc, ← Category.assoc coprod.inl iso.inv, leftIn]
    · simp [joinBlockExits, coprod.associator, Category.assoc]
      rw [coprod.inr_desc, ← Category.assoc coprod.inr iso.inv, rightIn]
      rfl
  have equation := iterate_join_blocks a d B left right
  dsimp only at equation
  rw [copair, join, Category.assoc iso.hom, ← Category.assoc (coprod.desc left right),
    iterate_roll, copair] at equation
  have simplify : (step ≫ coprod.map (𝟙 B) iso.inv) ≫ coprod.map (𝟙 B) iso.hom = step := by
    rw [Category.assoc, coprod.map_map, Iso.inv_hom_id, Category.id_comp]
    rw [show coprod.map (𝟙 B) (𝟙 (A ⨿ D)) = 𝟙 _ from coprod.map_id_id, Category.comp_id]
  change iso.hom ≫ iterate ((step ≫ coprod.map (𝟙 B) iso.inv) ≫ coprod.map (𝟙 B) iso.hom) = _ at equation
  rw [simplify] at equation
  exact (cancel_epi iso.hom).mp equation

private theorem iterate_rows_uniform {A C D E B : P} {h : A ⟶ C} {k : D ⟶ E}
    (hh : UniformStateMap h) (hk : UniformStateMap k)
    (left : A ⟶ (B ⨿ A) ⨿ D) (right : D ⟶ (B ⨿ A) ⨿ D)
    (left' : C ⟶ (B ⨿ C) ⨿ E) (right' : E ⟶ (B ⨿ C) ⨿ E)
    (ls : left ≫ coprod.map (coprod.map (𝟙 B) h) k = h ≫ left')
    (rs : right ≫ coprod.map (coprod.map (𝟙 B) h) k = k ≫ right') :
    iterate (coprod.desc left right ≫ (coprod.associator B A D).hom) =
      coprod.map h k ≫ iterate (coprod.desc left' right' ≫ (coprod.associator B C E).hom) := by
  let over := coprod.map (𝟙 B) h
  let tail := iterate right
  let tail' := iterate right'
  have tailEq : tail ≫ over = k ≫ tail' := by
    rw [iterate_naturality]
    apply hk
    simpa only [Category.assoc, coprod.map_map, Category.id_comp, Category.comp_id] using rs
  let cut := left ≫ coprod.desc (𝟙 (B ⨿ A)) tail
  let cut' := left' ≫ coprod.desc (𝟙 (B ⨿ C)) tail'
  have combined : coprod.desc (𝟙 (B ⨿ A)) tail ≫ over =
      coprod.map over k ≫ coprod.desc (𝟙 (B ⨿ C)) tail' := by
    rw [coprod.desc_comp, coprod.map_desc, Category.id_comp, Category.comp_id, tailEq]
  have headEq : iterate cut = h ≫ iterate cut' := by
    apply hh
    change (left ≫ coprod.desc (𝟙 (B ⨿ A)) tail) ≫ over =
      h ≫ left' ≫ coprod.desc (𝟙 (B ⨿ C)) tail'
    rw [Category.assoc, combined, ← Category.assoc left, ls, Category.assoc]
  have finish : coprod.desc (𝟙 B) (iterate cut) =
      over ≫ coprod.desc (𝟙 B) (iterate cut') := by
    rw [coprod.map_desc, Category.id_comp, headEq]
  have tailWhole : tail ≫ coprod.desc (𝟙 B) (iterate cut) =
      k ≫ tail' ≫ coprod.desc (𝟙 B) (iterate cut') := by
    rw [finish, ← Category.assoc tail, tailEq, Category.assoc]
  rw [iterate_coprod_rows, iterate_coprod_rows]
  change coprod.desc (iterate cut) (tail ≫ coprod.desc (𝟙 B) (iterate cut)) =
    coprod.map h k ≫ coprod.desc (iterate cut') (tail' ≫ coprod.desc (𝟙 B) (iterate cut'))
  rw [coprod.map_desc, tailWhole, headEq]

theorem iterate_uniformity {A C D E B : P}
    {h : A ⟶ C} {k : D ⟶ E} (hh : UniformStateMap h) (hk : UniformStateMap k)
    (f : A ⨿ D ⟶ B ⨿ (A ⨿ D)) (g : C ⨿ E ⟶ B ⨿ (C ⨿ E))
    (square : f ≫ coprod.map (𝟙 B) (coprod.map h k) = coprod.map h k ≫ g) :
    iterate f = coprod.map h k ≫ iterate g := by
  let frows := f ≫ (coprod.associator B A D).inv
  let grows := g ≫ (coprod.associator B C E).inv
  have ports : coprod.map (𝟙 B) (coprod.map h k) ≫ (coprod.associator B C E).inv =
      (coprod.associator B A D).inv ≫ coprod.map (coprod.map (𝟙 B) h) k := by
    apply coprod.hom_ext
    · simp [coprod.associator]
    · apply coprod.hom_ext <;> simp [coprod.associator]
  have ls : (coprod.inl ≫ frows) ≫ coprod.map (coprod.map (𝟙 B) h) k = h ≫ coprod.inl ≫ grows := by
    simp only [frows, grows, Category.assoc]
    rw [← ports, ← Category.assoc f, square, Category.assoc (coprod.map h k), coprod.inl_map_assoc]
  have rs : (coprod.inr ≫ frows) ≫ coprod.map (coprod.map (𝟙 B) h) k = k ≫ coprod.inr ≫ grows := by
    simp only [frows, grows, Category.assoc]
    rw [← ports, ← Category.assoc f, square, Category.assoc (coprod.map h k), coprod.inr_map_assoc]
  have pack {X Y Z : P} (m : X ⨿ Y ⟶ Z) :
      coprod.desc (coprod.inl ≫ m) (coprod.inr ≫ m) = m := by
    apply coprod.hom_ext <;> simp
  simpa only [pack, frows, grows, Category.assoc, Iso.inv_hom_id, Category.comp_id] using
    iterate_rows_uniform hh hk _ _ _ _ ls rs

theorem constructor_coproduct_uniform {A D : P} {h : A ⟶ D} (tree : ConstructorCoproduct h) :
    UniformStateMap h := by
  induction tree with
  | leaf h => exact iterate_uniformity_ofConstructorReturn h
  | sum _ _ ih ik =>
    intro B f g square
    exact iterate_uniformity ih ik f g square

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ConstructorBlockUniformity

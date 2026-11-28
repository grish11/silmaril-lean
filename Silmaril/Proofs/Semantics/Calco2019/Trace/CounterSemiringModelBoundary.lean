module

public import Silmaril.Semantics.Calco2019.Trace.CounterSemiring.Independence.Thms
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Silmaril.Semantics.Calco2019.Trace.Uniformity.Thms

/-! # The matrix witness fails constructor uniformity -/

public section

universe u v

namespace Silmaril.Calco2019.Proofs.CounterSemiringModelBoundary

open CategoryTheory CategoryTheory.Limits Guardedness
open CounterSemiring.FiniteMatrix

local notation "CP" => coproducts
local notation "I" => conway.toFixpoints

private theorem map_comp {Y A B C : Object.{0}} (f : A ⟶ B) (g : B ⟶ C) :
    (CP).map (𝟙 Y) f ≫ (CP).map (𝟙 Y) g = (CP).map (𝟙 Y) (f ≫ g) := by
  apply (CP).hom_ext <;> simp [Coproducts.map]

/-- The failed square stays failed when its two state objects are replaced by
isomorphic coordinates. -/
theorem not_uniform_of_fold_coordinates {X Z : Object.{0}} (i : (CP).sum one one ≅ Z)
    (u : one ≅ X) (h : Z ⟶ X) (coord : i.hom ≫ h = (CP).desc (𝟙 one) (𝟙 one) ≫ u.hom) :
    ¬ (I).UniformAt h := by
  let fold := (CP).desc (𝟙 one) (𝟙 one)
  let alt := binaryCycleBody (P := coproducts) oneBody
  let small : X ⟶ (CP).sum one X := u.inv ≫ oneBody ≫ (CP).map (𝟙 one) u.hom
  let large : Z ⟶ (CP).sum one Z := i.inv ≫ alt ≫ (CP).map (𝟙 one) i.hom
  have s : u.hom ≫ small = oneBody ≫ (CP).map (𝟙 one) u.hom := by
    dsimp only [small]
    rw [Iso.hom_inv_id_assoc]
  have l : i.hom ≫ large = alt ≫ (CP).map (𝟙 one) i.hom := by
    dsimp only [large]
    rw [Iso.hom_inv_id_assoc]
  have square : h ≫ small = large ≫ (CP).map (𝟙 one) h := by
    apply (cancel_epi i.hom).1
    have base : fold ≫ oneBody = alt ≫ (CP).map (𝟙 one) fold := binaryCycle_fold_square oneBody
    calc
      _ = fold ≫ oneBody ≫ (CP).map (𝟙 one) u.hom := by
        rw [← Category.assoc i.hom h, coord, Category.assoc, s]
      _ = alt ≫ (CP).map (𝟙 one) (fold ≫ u.hom) := by
        rw [← Category.assoc fold, base, Category.assoc, map_comp]
      _ = _ := by
        rw [← coord, ← map_comp, ← Category.assoc alt, ← l, Category.assoc]
  intro uniform
  have comp := congrArg (fun a => i.hom ≫ a) (uniform small large True.intro True.intro square)
  rw [← Category.assoc i.hom h, coord, Category.assoc fold,
    conway.uniform_iso u _ _ True.intro True.intro s,
    conway.uniform_iso i _ _ True.intro True.intro l] at comp
  exact oneBody_fails_binaryCycle comp.symm

/-- The graph of the constant Unit constructor is the folded state map. -/
theorem not_uniform_unit_constructor :
    ¬ (I).UniformAt (relabel (X := (CP).sum one one) (Y := one) (fun _ => ())) := by
  let discard := relabel (X := (CP).sum one one) (Y := one) (fun _ => ())
  have sectionEq (tag : Unit → Unit ⊕ Unit) :
      (𝟙 one : one ⟶ one) = relabel (X := one) (Y := (CP).sum one one) tag ≫ discard := by
    apply Matrix.ext
    intro x y
    refine Eq.trans ?_ (relabel_comp (X := one) (Y := (CP).sum one one) tag discard x y).symm
    cases x
    cases y
    rfl
  have h : (CP).desc (𝟙 one) (𝟙 one) = discard := by
    apply (CP).hom_ext
    · rw [(CP).inl_desc]
      exact sectionEq Sum.inl
    · rw [(CP).inr_desc]
      exact sectionEq Sum.inr
  apply not_uniform_of_fold_coordinates (Iso.refl _) (Iso.refl _) _
  rw [Iso.refl_hom, Iso.refl_hom, Category.id_comp, Category.comp_id, h]

private noncomputable def transportCofan {X Z : Object.{0}} (u : one ≅ X) {l r : X ⟶ Z}
    (colim : IsColimit (BinaryCofan.mk l r)) : IsColimit (BinaryCofan.mk (u.hom ≫ l) (u.hom ≫ r)) := by
  refine BinaryCofan.IsColimit.mk _
    (fun f g => colim.desc (BinaryCofan.mk (u.inv ≫ f) (u.inv ≫ g))) ?_ ?_ ?_
  · intro Y f g
    change (u.hom ≫ l) ≫ _ = f
    rw [Category.assoc, show l ≫ _ = u.inv ≫ f from colim.fac _ ⟨WalkingPair.left⟩,
      Iso.hom_inv_id_assoc]
  · intro Y f g
    change (u.hom ≫ r) ≫ _ = g
    rw [Category.assoc, show r ≫ _ = u.inv ≫ g from colim.fac _ ⟨WalkingPair.right⟩,
      Iso.hom_inv_id_assoc]
  · intro Y f g m hl hr
    change (u.hom ≫ l) ≫ m = f at hl
    change (u.hom ≫ r) ≫ m = g at hr
    apply BinaryCofan.IsColimit.hom_ext colim
    · calc
        l ≫ m = u.inv ≫ f := by rw [← hl, Category.assoc, Iso.inv_hom_id_assoc]
        _ = _ := (colim.fac (BinaryCofan.mk (u.inv ≫ f) (u.inv ≫ g)) ⟨WalkingPair.left⟩).symm
    · calc
        r ≫ m = u.inv ≫ g := by rw [← hr, Category.assoc, Iso.inv_hom_id_assoc]
        _ = _ := (colim.fac (BinaryCofan.mk (u.inv ≫ f) (u.inv ≫ g)) ⟨WalkingPair.right⟩).symm

theorem not_uniform_coproduct_fold {X Z : Object.{0}} (u : one ≅ X) (l r : X ⟶ Z)
    (colim : IsColimit (BinaryCofan.mk l r)) (h : Z ⟶ X)
    (hl : l ≫ h = 𝟙 X) (hr : r ≫ h = 𝟙 X) : ¬ (I).UniformAt h := by
  let t := transportCofan u colim
  let e := ((CP).isColimit one one).coconePointUniqueUpToIso t
  have left : (CP).inl ≫ e.hom = u.hom ≫ l :=
    ((CP).isColimit one one).comp_coconePointUniqueUpToIso_hom t ⟨WalkingPair.left⟩
  have right : (CP).inr ≫ e.hom = u.hom ≫ r :=
    ((CP).isColimit one one).comp_coconePointUniqueUpToIso_hom t ⟨WalkingPair.right⟩
  apply not_uniform_of_fold_coordinates e u
  apply (CP).hom_ext
  · rw [← Category.assoc, left, Category.assoc, hl, Category.comp_id, (CP).inl_desc_assoc,
      Category.id_comp]
  · rw [← Category.assoc, right, Category.assoc, hr, Category.comp_id, (CP).inr_desc_assoc,
      Category.id_comp]

theorem not_uniform_value_fold {V : Type u} [Category.{v} V] [HasBinaryCoproducts V]
    (J : V ⥤ Object.{0}) [PreservesColimitsOfShape (Discrete WalkingPair) J]
    (X : V) (u : one ≅ J.obj X) :
    ¬ (I).UniformAt (J.map (coprod.desc (𝟙 X) (𝟙 X))) := by
  let cf := BinaryCofan.mk (coprod.inl : X ⟶ X ⨿ X) (coprod.inr : X ⟶ X ⨿ X)
  have hc : IsColimit cf := coprodIsCoprod X X
  have preserve : IsColimit (J.mapCocone cf) := isColimitOfPreserves J hc
  refine not_uniform_coproduct_fold u (J.map coprod.inl) (J.map coprod.inr)
    (BinaryCofan.isColimitMapCoconeEquiv (s := cf) preserve) (J.map (coprod.desc (𝟙 X) (𝟙 X))) ?_ ?_
  · rw [← J.map_comp, coprod.inl_desc, J.map_id]
  · rw [← J.map_comp, coprod.inr_desc, J.map_id]

end Silmaril.Calco2019.Proofs.CounterSemiringModelBoundary

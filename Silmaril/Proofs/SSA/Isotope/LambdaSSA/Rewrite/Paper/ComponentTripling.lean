module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Tripling.Components.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Blocks.ThreeCycle.Unit.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ComponentTripling

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper (TypeCategory)
open Paper.TypeCategory
open Paper.TypeCategory.ComponentTripling
open UnitThreeCycle (One Three split reset forget phase_discards)

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "P" => TypeCategory (τ := τ) Φ
local notation "U" => One (Φ := Φ) (τ := τ)
local notation "H" => Three (Φ := Φ) (τ := τ)
local notation "T" => BitState (Φ := Φ) (τ := τ)
local notation "R" => resetPayloads (Φ := Φ) (τ := τ)

set_option backward.isDefEq.respectTransparency false

private noncomputable abbrev first {A : P} : A ⟶ Phases A := coprod.inl
private noncomputable abbrev middle {A : P} : A ⟶ Phases A := coprod.inl ≫ coprod.inr
private noncomputable abbrev last {A : P} : A ⟶ Phases A := coprod.inr ≫ coprod.inr

private noncomputable def enter (tag : U ⟶ Phases U) : T ⟶ H ⨿ H :=
  coprod.map (tag ≫ split.inv) (tag ≫ split.inv)

private noncomputable def leave (tag : U ⟶ T) : H ⟶ Phases T :=
  (split (Φ := Φ) (τ := τ)).hom ≫ coprod.desc (tag ≫ first)
    (coprod.desc (tag ≫ middle) (tag ≫ last))

private noncomputable def regroup : Phases T ≅ H ⨿ H where
  hom := coprod.desc (enter first) (coprod.desc (enter middle) (enter last))
  inv := coprod.desc (leave coprod.inl) (leave coprod.inr)
  hom_inv_id := by
    apply coprod.hom_ext
    · apply coprod.hom_ext <;> simp [enter, leave, Category.assoc]
    · apply coprod.hom_ext
      · apply coprod.hom_ext <;> simp [enter, leave, Category.assoc]
      · apply coprod.hom_ext <;> simp [enter, leave, Category.assoc]
  inv_hom_id := by
    apply coprod.hom_ext
    · apply (cancel_epi (split (Φ := Φ) (τ := τ)).inv).mp
      simp only [leave, Category.comp_id]
      apply coprod.hom_ext
      · simp [enter, Category.assoc]
      · apply coprod.hom_ext <;> simp [enter, Category.assoc]
    · apply (cancel_epi (split (Φ := Φ) (τ := τ)).inv).mp
      simp only [leave, Category.comp_id]
      apply coprod.hom_ext
      · simp [enter, Category.assoc]
      · apply coprod.hom_ext <;> simp [enter, Category.assoc]

private noncomputable abbrev forgetPhases : H ⨿ H ⟶ T := coprod.map forget forget

private theorem enter_forget {tag : U ⟶ Phases U} (h : tag ≫ split.inv ≫ forget = reset) :
    enter tag ≫ forgetPhases = R := by
  rw [enter, coprod.map_map, Category.assoc, h]

theorem triple_at_first {A B : P} (g : A ⟶ B ⨿ A) :
    coprod.inl ≫ iterate (cycle g) = iterate (thenOnRepeat g (thenOnRepeat g g)) := by
  let left : A ⟶ (B ⨿ A) ⨿ (A ⨿ A) := g ≫ coprod.map coprod.inl coprod.inl
  let right : A ⨿ A ⟶ (B ⨿ A) ⨿ (A ⨿ A) :=
    coprod.desc (g ≫ coprod.map coprod.inl coprod.inr) (g ≫ coprod.inl)
  have pack : coprod.desc left right ≫ (coprod.associator B A (A ⨿ A)).hom = cycle g := by
    apply coprod.hom_ext
    · simp only [left, cycle, coprod.inl_desc_assoc, coprod.inl_desc, Category.assoc]
      congr 1
      apply coprod.hom_ext <;> simp [coprod.associator]
    · apply coprod.hom_ext
      · simp only [right, cycle, coprod.inr_desc_assoc, coprod.inr_desc, coprod.inl_desc_assoc,
          coprod.inl_desc, Category.assoc]
        congr 1
        apply coprod.hom_ext <;> simp [coprod.associator]
      · simp only [right, cycle, coprod.inr_desc_assoc, coprod.inr_desc, Category.assoc]
        congr 1
        apply coprod.hom_ext <;> simp [coprod.associator]
  have rightLast : (coprod.inr : A ⟶ A ⨿ A) ≫ iterate right = g := by
    rw [iterate_fixpoint right]
    simp [right]
  have rightMiddle : (coprod.inl : A ⟶ A ⨿ A) ≫ iterate right = thenOnRepeat g g := by
    have row : (coprod.inl : A ⟶ A ⨿ A) ≫ right = g ≫ coprod.map coprod.inl coprod.inr := by
      simp [right]
    conv_lhs => rw [iterate_fixpoint right]
    rw [← Category.assoc, row]
    simp [rightLast]
  have rightEq : iterate right = coprod.desc (thenOnRepeat g g) g :=
    coprod.hom_ext (by simpa using rightMiddle) (by simpa using rightLast)
  rw [← pack, iterate_coprod_rows]
  rw [coprod.inl_desc]
  congr 1
  simp [left, rightEq]

theorem iteration_change {A D B : P} (e : A ≅ D) (f : A ⟶ B ⨿ A) :
    iterate f = e.hom ≫ iterate (e.inv ≫ f ≫ coprod.map (𝟙 B) e.hom) := by
  have eq : f = e.hom ≫ (e.inv ≫ f) := by simp
  conv_lhs => rw [eq, iterate_roll]
  simp only [Category.assoc]

theorem iterate_triple {B : P} (g : T ⟶ B ⨿ T)
    (input : R ≫ g = g) (output : g ≫ coprod.map (𝟙 B) R = g) :
    iterate (thenOnRepeat g (thenOnRepeat g g)) = iterate g := by
  let c := regroup (Φ := Φ) (τ := τ)
  let step := cycle g
  let grouped := c.inv ≫ step ≫ coprod.map (𝟙 B) c.hom
  obtain ⟨p0, p1, p2⟩ := phase_discards (Φ := Φ) (τ := τ)
  have leg0 : first ≫ c.hom ≫ forgetPhases = R := by
    simpa only [first, c, regroup, coprod.inl_desc_assoc] using enter_forget p0
  have leg1 : middle ≫ c.hom ≫ forgetPhases = R := by
    simpa only [middle, c, regroup, Category.assoc, coprod.inr_desc_assoc, coprod.inl_desc_assoc]
      using enter_forget (tag := middle) (by simpa only [Category.assoc] using p1)
  have leg2 : last ≫ c.hom ≫ forgetPhases = R := by
    simpa only [last, c, regroup, Category.assoc, coprod.inr_desc_assoc] using enter_forget (tag := last) (by simpa only [Category.assoc] using p2)
  have square : step ≫ coprod.map (𝟙 B) (c.hom ≫ forgetPhases) = c.hom ≫ forgetPhases ≫ g := by
    have endpoint {i j : T ⟶ Phases T}
        (hi : i ≫ c.hom ≫ forgetPhases = R) (hj : j ≫ c.hom ≫ forgetPhases = R)
        (route : i ≫ step = g ≫ coprod.map (𝟙 B) j) :
        i ≫ (step ≫ coprod.map (𝟙 B) (c.hom ≫ forgetPhases)) = i ≫ (c.hom ≫ forgetPhases ≫ g) := by
      rw [← Category.assoc i, route, Category.assoc g, coprod.map_map, Category.id_comp, hj, output,
        ← Category.assoc c.hom, ← Category.assoc i, hi, input]
    apply coprod.hom_ext
    · exact endpoint leg0 leg1 (by simp [step, cycle])
    · apply coprod.hom_ext
      · simpa only [Category.assoc] using endpoint leg1 leg2 (by simp [step, cycle, middle])
      · simpa only [Category.assoc] using endpoint leg2 leg0 (by simp [step, cycle, last])
  have groupedSquare : grouped ≫ coprod.map (𝟙 B) forgetPhases = forgetPhases ≫ g := by
    change (c.inv ≫ step ≫ coprod.map (𝟙 B) c.hom) ≫ coprod.map (𝟙 B) forgetPhases = _
    rw [Category.assoc c.inv, Category.assoc step, coprod.map_map, Category.id_comp, square,
      Iso.inv_hom_id_assoc]
  have hforget : ConstructorReturn (forget (Φ := Φ) (τ := τ)) := ⟨.unit, .unit, rfl⟩
  have resolved := iterate_uniformity_of_coprod_constructor hforget hforget grouped g groupedSquare
  have native : iterate (cycle g) = c.hom ≫ forgetPhases ≫ iterate g := by
    have h := iteration_change c (cycle g)
    change iterate (cycle g) = c.hom ≫ iterate grouped at h
    rw [h, resolved]
  rw [← triple_at_first, native, ← Category.assoc c.hom, ← Category.assoc first, leg0]
  rw [iterate_fixpoint g, ← Category.assoc, input]

theorem iterate_normalize {B : P} (g : T ⟶ B ⨿ T) :
    iterate (thenOnRepeat (normalize g) (thenOnRepeat (normalize g) (normalize g))) =
      iterate (normalize g) := by
  have resetEq : (reset (Φ := Φ) (τ := τ)) ≫ reset = reset :=
    discard_comp_branchValue (.unit (Γ := [Silmaril.unit]))
  have both : R ≫ R = R := by
    rw [coprod.map_map, resetEq]
  apply iterate_triple
  · simp only [normalize, ← Category.assoc R R, both]
  · simp only [normalize, Category.assoc, coprod.map_map, Category.id_comp, both]

section PhaseInterleave

universe w z
variable {C : Type w} [Category.{z} C] [HasBinaryCoproducts C]

local notation "Copies" A:max => (A ⨿ (A ⨿ A))

@[expose] noncomputable def phaseInterleave (A D : C) : Copies (A ⨿ D) ≅ Copies A ⨿ Copies D where
  hom :=
    coprod.desc (coprod.map coprod.inl coprod.inl)
      (coprod.desc (coprod.map (coprod.inl ≫ coprod.inr) (coprod.inl ≫ coprod.inr))
        (coprod.map (coprod.inr ≫ coprod.inr) (coprod.inr ≫ coprod.inr)))
  inv := coprod.desc (coprod.map coprod.inl (coprod.map coprod.inl coprod.inl))
    (coprod.map coprod.inr (coprod.map coprod.inr coprod.inr))
  hom_inv_id := by
    apply coprod.hom_ext
    · apply coprod.hom_ext <;> simp
    · apply coprod.hom_ext <;> (apply coprod.hom_ext <;> simp)
  inv_hom_id := by
    apply coprod.hom_ext
    · apply coprod.hom_ext
      · simp
      · apply coprod.hom_ext <;> simp
    · apply coprod.hom_ext
      · simp
      · apply coprod.hom_ext <;> simp

theorem phaseInterleave_hom (A D : C) : (phaseInterleave A D).hom =
  coprod.desc (coprod.map coprod.inl coprod.inl)
    (coprod.desc (coprod.map (coprod.inl ≫ coprod.inr) (coprod.inl ≫ coprod.inr))
      (coprod.map (coprod.inr ≫ coprod.inr) (coprod.inr ≫ coprod.inr))) := rfl

theorem phaseInterleave_inv (A D : C) : (phaseInterleave A D).inv =
    coprod.desc (coprod.map coprod.inl (coprod.map coprod.inl coprod.inl))
      (coprod.map coprod.inr (coprod.map coprod.inr coprod.inr)) := rfl

end PhaseInterleave

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ComponentTripling

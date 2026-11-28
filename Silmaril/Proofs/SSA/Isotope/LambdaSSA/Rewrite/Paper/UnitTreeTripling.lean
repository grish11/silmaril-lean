module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Tripling.Components.UnitTree.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Tripling.Components.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnitTreeTripling

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper (TypeCategory)
open Paper.TypeCategory Paper.TypeCategory.ComponentTripling

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "P" => TypeCategory (τ := τ) Φ
local notation "Z" => ofType (Φ := Φ) (Silmaril.empty : τ)
local notation "U" => UnitThreeCycle.One (τ := τ) (Φ := Φ)

set_option backward.isDefEq.respectTransparency false

private inductive Phase
  | first | middle | last

private noncomputable def tag {A : P} : Phase → (A ⟶ Phases A)
  | .first => coprod.inl
  | .middle => coprod.inl ≫ coprod.inr
  | .last => coprod.inr ≫ coprod.inr

private theorem interleave_tag (A D : P) (i : Phase) :
    tag i ≫ (phaseInterleave A D).hom = coprod.map (tag i) (tag i) := by
  cases i <;> simp [phaseInterleave_hom, tag, Category.assoc]

private noncomputable def regroupEmpty : Phases Z ≅ Z where
  hom := coprod.desc (𝟙 Z) (coprod.desc (𝟙 Z) (𝟙 Z))
  inv := coprod.inl
  hom_inv_id := by
    apply coprod.hom_ext
    · exact (emptyIsInitial (Φ := Φ)).hom_ext _ _
    · apply coprod.hom_ext <;> exact (emptyIsInitial (Φ := Φ)).hom_ext _ _
  inv_hom_id := (emptyIsInitial (Φ := Φ)).hom_ext _ _

noncomputable def regroup : (t : UnitTree) → Phases (t.obj (τ := τ) (Φ := Φ)) ≅ t.phaseObj
  | .empty => regroupEmpty
  | .unit => UnitThreeCycle.split.symm
  | .sum l r => phaseInterleave l.obj r.obj ≪≫ coprod.mapIso (regroup l) (regroup r)

private theorem regroup_tag (t : UnitTree) (i : Phase) :
    tag i ≫ (regroup (τ := τ) (Φ := Φ) t).hom ≫ t.forget = t.reset := by
  induction t with
  | empty => exact (emptyIsInitial (Φ := Φ)).hom_ext _ _
  | unit =>
    obtain ⟨p0, p1, p2⟩ := UnitThreeCycle.phase_discards (τ := τ) (Φ := Φ)
    cases i with
    | first => exact p0
    | middle =>
      change ((coprod.inl : U ⟶ U ⨿ U) ≫ coprod.inr) ≫
        UnitThreeCycle.split.inv ≫ UnitThreeCycle.forget = UnitThreeCycle.reset
      rw [Category.assoc, p1]
    | last =>
      change ((coprod.inr : U ⟶ U ⨿ U) ≫ coprod.inr) ≫
        UnitThreeCycle.split.inv ≫ UnitThreeCycle.forget = UnitThreeCycle.reset
      rw [Category.assoc, p2]
  | sum l r hl hr =>
    change tag i ≫ ((phaseInterleave l.obj r.obj).hom ≫ coprod.map (regroup l).hom (regroup r).hom) ≫
      coprod.map l.forget r.forget = coprod.map l.reset r.reset
    rw [Category.assoc, ← Category.assoc (tag i) (phaseInterleave l.obj r.obj).hom, interleave_tag,
      coprod.map_map, coprod.map_map, hl, hr]

theorem forget_tree (t : UnitTree) : ConstructorCoproduct (t.forget (τ := τ) (Φ := Φ)) := by
  induction t with
  | empty => exact .leaf ((constructorReturn_multiplicative (τ := τ) (Φ := Φ)).id_mem _)
  | unit => exact .leaf ⟨.unit, .unit, rfl⟩
  | sum l r hl hr => exact .sum hl hr

theorem reset_idem (t : UnitTree) :
    t.reset (τ := τ) (Φ := Φ) ≫ t.reset = t.reset := by
  induction t with
  | empty => exact Category.id_comp _
  | unit => exact discard_comp_branchValue (.unit (Γ := [Silmaril.unit]))
  | sum l r hl hr =>
    change coprod.map l.reset r.reset ≫ coprod.map l.reset r.reset = coprod.map l.reset r.reset
    rw [coprod.map_map, hl, hr]

theorem iterate_triple (t : UnitTree) {B : P} (g : t.obj ⟶ B ⨿ t.obj)
    (input : t.reset ≫ g = g) (output : g ≫ coprod.map (𝟙 B) t.reset = g) :
    iterate (thenOnRepeat g (thenOnRepeat g g)) = iterate g := by
  let c := regroup (τ := τ) (Φ := Φ) t
  let step := cycle g
  let grouped := c.inv ≫ step ≫ coprod.map (𝟙 B) c.hom
  have square : step ≫ coprod.map (𝟙 B) (c.hom ≫ t.forget) = c.hom ≫ t.forget ≫ g := by
    have endpoint (i j : Phase) (route : tag i ≫ step = g ≫ coprod.map (𝟙 B) (tag j)) :
        tag i ≫ (step ≫ coprod.map (𝟙 B) (c.hom ≫ t.forget)) = tag i ≫ (c.hom ≫ t.forget ≫ g) := by
      rw [← Category.assoc (tag i), route, Category.assoc g, coprod.map_map, Category.id_comp,
        show tag j ≫ c.hom ≫ t.forget = t.reset from regroup_tag t j, output,
        ← Category.assoc c.hom, ← Category.assoc (tag i),
        show tag i ≫ c.hom ≫ t.forget = t.reset from regroup_tag t i, input]
    apply coprod.hom_ext
    · exact endpoint .first .middle (by simp [tag, cycle, step])
    · apply coprod.hom_ext
      · simpa only [tag, Category.assoc] using endpoint .middle .last (by simp [tag, cycle, step])
      · simpa only [tag, Category.assoc] using endpoint .last .first (by simp [tag, cycle, step])
  have groupedSquare : grouped ≫ coprod.map (𝟙 B) t.forget = t.forget ≫ g := by
    change (c.inv ≫ step ≫ coprod.map (𝟙 B) c.hom) ≫ coprod.map (𝟙 B) t.forget = _
    rw [Category.assoc c.inv, Category.assoc step, coprod.map_map, Category.id_comp, square,
      Iso.inv_hom_id_assoc]
  have resolved := (forget_tree (τ := τ) (Φ := Φ) t).uniform grouped g groupedSquare
  have native : iterate (cycle g) = c.hom ≫ t.forget ≫ iterate g := by
    have h := iterate_change_state c (cycle g)
    change iterate (cycle g) = c.hom ≫ iterate grouped at h
    rw [h, resolved]
  rw [← iterate_cycle_at_first, native, ← Category.assoc c.hom, ← Category.assoc coprod.inl,
    show coprod.inl ≫ c.hom ≫ t.forget = t.reset from regroup_tag t .first]
  rw [iterate_fixpoint g, ← Category.assoc, input]

theorem iterate_normalize (t : UnitTree) {B : P} (g : t.obj ⟶ B ⨿ t.obj) :
    iterate (thenOnRepeat (t.normalize g) (thenOnRepeat (t.normalize g) (t.normalize g))) =
      iterate (t.normalize g) := by
  apply iterate_triple
  · simp only [UnitTree.normalize, ← Category.assoc t.reset t.reset, reset_idem]
  · simp only [UnitTree.normalize, Category.assoc, coprod.map_map, Category.id_comp, reset_idem]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnitTreeTripling

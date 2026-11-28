module

public import Silmaril.Semantics.Calco2019.Trace.CounterSemiring.Independence.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Silmaril.Proofs.Semantics.Calco2019.OmegaContinuous

public section

universe u v

namespace Silmaril.Calco2019.Proofs.CounterSemiringIndependence

open CategoryTheory Guardedness
open Silmaril.Calco2019.CounterSemiring
open FiniteMatrix

set_option backward.isDefEq.respectTransparency false

theorem fold_square {K : Type u} [Category.{v} K] {P : Coproducts K} {X Y : K}
    (f : X ⟶ P.sum Y X) :
    P.desc (𝟙 X) (𝟙 X) ≫ f =
      binaryCycleBody f ≫ P.map (𝟙 Y) (P.desc (𝟙 X) (𝟙 X)) := by
  let fold := P.desc (𝟙 X) (𝟙 X)
  have cancel (p : X ⟶ P.sum X X) (h : p ≫ fold = 𝟙 X) :
      P.map (𝟙 Y) p ≫ P.map (𝟙 Y) fold = 𝟙 (P.sum Y X) := by
    apply P.hom_ext
    · simp [Coproducts.map]
    · simp [Coproducts.map, Category.assoc]
      rw [← Category.assoc, h, Category.id_comp]
  have cancelL := cancel P.inl (P.inl_desc _ _)
  have cancelR := cancel P.inr (P.inr_desc _ _)
  apply P.hom_ext
  · simp only [fold, binaryCycleBody, Category.assoc, P.inl_desc_assoc, Category.id_comp,
      cancelR, Category.comp_id]
  · simp only [fold, binaryCycleBody, Category.assoc, P.inr_desc_assoc, Category.id_comp,
      cancelL, Category.comp_id]

theorem iterate_apply {U B : Object.{u}} (f : U ⟶ coproducts.sum B U)
    (i : U.carrier) (b : B.carrier) :
    conway.iterate f True.intro i b = networkDagger (fun x y => f x y) i b := by
  change networkFeedback (fun x y => coproducts.desc f f x y) i b = _
  apply congrArg (fun g : Network U.carrier B.carrier U.carrier => networkFeedback g i b)
  funext x y
  cases x with
  | inl x => exact desc_inl_apply f f x y
  | inr x => exact desc_inr_apply f f x y

private def alternatingRow : (Unit ⊕ Unit) → (Unit ⊕ (Unit ⊕ Unit)) → Scalar
  | _, .inl _ => 1
  | .inl _, .inr (.inr _) | .inr _, .inr (.inl _) => .generator
  | _, _ => 0

private theorem binary_body_apply (x : Unit ⊕ Unit) (y : Unit ⊕ (Unit ⊕ Unit)) :
    binaryCycleBody (P := coproducts) oneBody x y = alternatingRow x y := by
  have map_graph (p : Unit → Unit ⊕ Unit) :
      coproducts.map (𝟙 one) (relabel (X := one) (Y := sum one one) p) =
        relabel (X := sum one one) (Y := sum one (sum one one)) (Sum.map id p) := by
    apply Matrix.ext
    intro a b
    cases a with
    | inl a =>
      rw [Coproducts.map, desc_inl_apply, Category.id_comp]
      rfl
    | inr a =>
      rw [Coproducts.map, desc_inr_apply]
      exact relabel_comp (X := one) (Y := sum one one) p coproducts.inr a b
  have left : coproducts.map (𝟙 one) (coproducts.inr (X := one) (Y := one)) =
      relabel (X := sum one one) (Y := sum one (sum one one)) (Sum.map id Sum.inr) :=
    map_graph Sum.inr
  have right : coproducts.map (𝟙 one) (coproducts.inl (X := one) (Y := one)) =
      relabel (X := sum one one) (Y := sum one (sum one one)) (Sum.map id Sum.inl) :=
    map_graph Sum.inl
  have matrices (p : Unit → Unit ⊕ Unit) (y : Unit ⊕ (Unit ⊕ Unit)) :
      (oneBody ≫ relabel (X := sum one one) (Y := sum one (sum one one)) (Sum.map id p)) () y =
        ∑ j : Unit ⊕ Unit, if Sum.map id p j = y then singleLoop () j else 0 :=
    comp_relabel (X := one) (Y := sum one one) (Z := sum one (sum one one))
      oneBody (Sum.map (id : Unit → Unit) p) () y
  rcases x with ⟨⟩ | ⟨⟩
  · rw [binaryCycleBody, desc_inl_apply, left, matrices]
    rcases y with ⟨⟩ | (⟨⟩ | ⟨⟩) <;> decide +revert
  · rw [binaryCycleBody, desc_inr_apply, right, matrices]
    rcases y with ⟨⟩ | (⟨⟩ | ⟨⟩) <;> decide +revert

theorem fails_oneBody_cycle :
    conway.iterate (binaryCycleBody oneBody) True.intro ≠
      coproducts.desc (𝟙 one) (𝟙 one) ≫ conway.iterate oneBody True.intro := by
  intro e
  have value := congrArg (fun f : sum one one ⟶ one => f (.inl ()) ()) e
  change conway.iterate (binaryCycleBody oneBody) True.intro (.inl ()) () =
    (coproducts.desc (𝟙 one) (𝟙 one) ≫ conway.iterate oneBody True.intro) (.inl ()) () at value
  have lhs : conway.iterate (binaryCycleBody oneBody) True.intro (.inl ()) () = .both := by
    refine (iterate_apply (binaryCycleBody oneBody) (.inl ()) ()).trans ?_
    have hbody : (fun x y => binaryCycleBody (P := coproducts) oneBody x y) = alternatingRow :=
      funext fun x => funext fun y => binary_body_apply x y
    exact (congrArg (fun g : (Unit ⊕ Unit) → (Unit ⊕ (Unit ⊕ Unit)) → Scalar =>
      networkDagger g (.inl ()) ()) hbody).trans (by decide)
  have fold : coproducts.desc (𝟙 one) (𝟙 one) =
      relabel (X := sum one one) (Y := one) (fun _ => ()) := by
    apply Matrix.ext
    intro x y
    rcases x with x | x <;> cases y <;> simp [relabel]
    all_goals exact Subsingleton.elim (α := Unit) _ _
  have rhs : (coproducts.desc (𝟙 one) (𝟙 one) ≫ conway.iterate oneBody True.intro) (.inl ()) () =
      .overflow := by
    rw [fold, relabel_comp]
    exact (iterate_apply oneBody () ()).trans singleLoop_solution
  exact (by decide : Scalar.both ≠ Scalar.overflow) (lhs.symm.trans (value.trans rhs))

theorem fails_oneBody_doubling :
    conway.iterate (oneBody ≫ coproducts.desc coproducts.inl oneBody) True.intro ≠
      conway.iterate oneBody True.intro := by
  let twice : Unit → Unit ⊕ Unit → Scalar := fun _ y =>
    match y with
    | .inl _ => .both
    | .inr _ => 1
  have body : (fun x y => (oneBody ≫ coproducts.desc coproducts.inl oneBody) x y) = twice := by
    funext x y
    cases x
    rw [comp_apply]
    change (∑ z : Unit ⊕ Unit,
      oneBody () z * coproducts.desc coproducts.inl oneBody z y) = twice () y
    rw [Fintype.sum_sum_type, Fintype.sum_unique, Fintype.sum_unique, desc_inl_apply, desc_inr_apply]
    cases y <;> decide +revert
  intro e
  have value := congrArg (fun h : one ⟶ one => h () ()) e
  change conway.iterate (oneBody ≫ coproducts.desc coproducts.inl oneBody) True.intro () () =
    conway.iterate oneBody True.intro () () at value
  have lhs := (iterate_apply (oneBody ≫ coproducts.desc coproducts.inl oneBody) () ()).trans
    (congrArg (fun (g : Unit → Unit ⊕ Unit → Scalar) => networkDagger g () ()) body)
  have rhs := (iterate_apply oneBody () ()).trans singleLoop_solution
  exact (by decide : networkDagger twice () () ≠ .overflow) (lhs.symm.trans (value.trans rhs))

theorem fails_cycle : ¬ conway.{0}.toFixpoints.BinaryCycleIdentity :=
  fun h => fails_oneBody_cycle (h oneBody True.intro True.intro)

end Silmaril.Calco2019.Proofs.CounterSemiringIndependence

namespace Silmaril.Calco2019.Proofs.CounterSemiringIndependence

open OmegaCompletePartialOrder Silmaril.Semantics.Domain

theorem standard_cycle {D : Type u} [OmegaCompletePartialOrder D] [OrderBot D] (f : D →𝒄 D) :
    fix (PointedCpo.alternating f) = fun _ => fix f := by
  let diagonal : D →𝒄 (Bool → D) := ContinuousHom.mk
    ⟨fun d _ => d, fun _ _ h _ => h⟩ (fun _ => rfl)
  exact (OmegaContinuous.fusion (F := f) (G := PointedCpo.alternating f)
    diagonal.ωScottContinuous rfl (fun _ => rfl)).symm

end Silmaril.Calco2019.Proofs.CounterSemiringIndependence

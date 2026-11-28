module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Blocks.Alternating.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Laws.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.StructuralValues.Freyd.Iteration.Elgot.Projection.HiddenBit.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Replay.Operand.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.EntryLet.Obstruction.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Coproducts.Thms

/-! # Exact quotient reduction for an alternating fold square -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.AlternatingFold

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.Extension.Singleton
open Paper.Extension.Singleton.Alternating (step)
open Paper.WithCaseReturns.StructuralValues.HiddenBit (alternating_fold_iff_double_of_seed)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

local notation "Q" => TypeCategory Seed
local notation "P" => Paper.TypeCategory (τ := τ) Φ
local notation "J" => projection Seed
local notation "I" => iterateChosen Seed

private theorem observed_eq {A B D : Q}
    (h : A ⟶ D) (f : A ⟶ B ⨿ A) (g : D ⟶ B ⨿ D)
    (square : f ≫ coprod.map (𝟙 B) h = h ≫ g)
    (enter leave : D ⟶ A) (entry : enter ≫ h = 𝟙 D) (again : leave ≫ h = 𝟙 D)
    (row : D ⟶ B ⨿ D) (routing : enter ≫ f = row ≫ coprod.map (𝟙 B) leave) : row = g := by
  have e := congrArg (fun k => enter ≫ k) square
  rw [← Category.assoc, routing, Category.assoc, coprod.map_map, Category.id_comp, again,
    coprod.map_id_id, Category.comp_id, ← Category.assoc, entry, Category.id_comp] at e
  exact e

theorem fold_iff_double {A B D : Q}
    (split : D ⨿ D ≅ A) (h : A ⟶ D) (f : A ⟶ B ⨿ A) (g left right : D ⟶ B ⨿ D)
    (hl : (coprod.inl ≫ split.hom) ≫ h = 𝟙 D)
    (hr : (coprod.inr ≫ split.hom) ≫ h = 𝟙 D)
    (routeLeft : (coprod.inl ≫ split.hom) ≫ f = left ≫ coprod.map (𝟙 B) (coprod.inr ≫ split.hom))
    (routeRight : (coprod.inr ≫ split.hom) ≫ f = right ≫ coprod.map (𝟙 B) (coprod.inl ≫ split.hom))
    (square : f ≫ coprod.map (𝟙 B) h = h ≫ g) :
    I f = h ≫ I g ↔ I (g ≫ coprod.desc coprod.inl g) = I g := by
  have leftEq := observed_eq Seed h f g square _ _ hl hr left routeLeft
  have rightEq := observed_eq Seed h f g square _ _ hr hl right routeRight
  have coordinates : step g g ≫ coprod.map (𝟙 B) split.hom = split.hom ≫ f := by
    apply coprod.hom_ext
    · rw [step, coprod.inl_desc_assoc, Category.assoc, coprod.map_map, Category.id_comp,
        ← Category.assoc, routeLeft, leftEq]
    · rw [step, coprod.inr_desc_assoc, Category.assoc, coprod.map_map, Category.id_comp,
        ← Category.assoc, routeRight, rightEq]
  have foldEq : split.hom ≫ h = coprod.desc (𝟙 D) (𝟙 D) := by
    apply coprod.hom_ext
    · rw [← Category.assoc, hl, coprod.inl_desc]
    · rw [← Category.assoc, hr, coprod.inr_desc]
  rw [← alternating_fold_iff_double_of_seed Seed g]
  change _ ↔ I (step g g) = _
  rw [uniformity_of_iso Seed split _ _ coordinates, ← foldEq, Category.assoc, cancel_epi]

set_option backward.isDefEq.respectTransparency false in
theorem projectStep_double {D B : P} (g : D ⟶ B ⨿ D) :
    projectStep Seed (g ≫ coprod.desc coprod.inl g) =
      projectStep Seed g ≫ coprod.desc coprod.inl (projectStep Seed g) := by
  let c := PreservesColimitPair.iso (J) B D
  change (J).map (g ≫ coprod.desc coprod.inl g) ≫ c.inv =
    ((J).map g ≫ c.inv) ≫ coprod.desc coprod.inl ((J).map g ≫ c.inv)
  rw [(J).map_comp, Category.assoc, Category.assoc]
  apply congrArg ((J).map g ≫ ·)
  apply (cancel_epi c.hom).1
  rw [Iso.hom_inv_id_assoc]
  have first : coprod.inl ≫ c.hom = (J).map (coprod.inl : B ⟶ B ⨿ D) :=
    inl_coprodComparison (J) B D
  have second : coprod.inr ≫ c.hom = (J).map (coprod.inr : D ⟶ B ⨿ D) :=
    inr_coprodComparison (J) B D
  apply coprod.hom_ext
  · simp only [coprod.inl_desc, ← Category.assoc]
    rw [first, ← (J).map_comp, coprod.inl_desc, ← first, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  · simp only [coprod.inr_desc, ← Category.assoc]
    rw [second, ← (J).map_comp, coprod.inr_desc]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.AlternatingFold

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.AlternatingFold.Example

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.TypeCategory
open Paper.Extension.Singleton (projection projectStep iterateChosen iterateChosen_projectStep
  projection_map_desc_congr)
open Paper.Extension.Singleton.Alternating (step)
open Paper.EntryLetObstruction (U flatRequest movedRequest flatRequest_typed movedRequest_typed
  flatRequest_arrow_ne_moved)
open SequencingObstruction (Instruction)

private abbrev X := ofType (Φ := Instruction) U
private abbrev D := ofType (Φ := Instruction) (Silmaril.coprod U U)
private abbrev zero : X ⟶ D := (sumCofan U U).inl
private abbrev one : X ⟶ D := (sumCofan U U).inr
private abbrev flat : X ⟶ X := ofRegion flatRequest_typed
private abbrev moved : X ⟶ X := ofRegion movedRequest_typed

private theorem zero_sumIso : zero ≫ (sumIso U U).hom = (coprod.inl : X ⟶ X ⨿ X) :=
  sumCofan_inl_sumIso_hom U U

private theorem one_sumIso : one ≫ (sumIso U U).hom = (coprod.inr : X ⟶ X ⨿ X) :=
  sumCofan_inr_sumIso_hom U U

-- The zero payload runs forever, switching its outer tag at each step.
-- The one payload makes a visible request and exits immediately.
private noncomputable def row (run : X ⟶ X) : D ⟶ X ⨿ D :=
  (sumIso U U).hom ≫ coprod.desc (zero ≫ coprod.inr) (run ≫ coprod.inl)

private theorem row_zero (run : X ⟶ X) : zero ≫ row run = zero ≫ coprod.inr := by
  rw [row, ← Category.assoc, zero_sumIso, coprod.inl_desc]

private theorem row_one (run : X ⟶ X) : one ≫ row run = run ≫ coprod.inl := by
  rw [row, ← Category.assoc, one_sumIso, coprod.inr_desc]

private theorem double_row (run : X ⟶ X) :
    row run ≫ coprod.desc coprod.inl (row run) = row run := by
  apply BinaryCofan.IsColimit.hom_ext (sumCofanIsColimit U U)
  · change zero ≫ (row run ≫ coprod.desc coprod.inl (row run)) = zero ≫ row run
    rw [← Category.assoc, row_zero, Category.assoc, coprod.inr_desc, row_zero]
  · change one ≫ (row run ≫ coprod.desc coprod.inl (row run)) = one ≫ row run
    rw [← Category.assoc, row_one, Category.assoc, coprod.inl_desc]

example : row moved ≠ row flat := by
  intro h
  have eq := congrArg (fun a => one ≫ a) h
  rw [row_one, row_one] at eq
  let endExit : X ⨿ D ⟶ X := coprod.desc (𝟙 X) (discardArrow _)
  have e := congrArg (fun a => a ≫ endExit) eq
  apply flatRequest_arrow_ne_moved
  have remove : (coprod.inl : X ⟶ X ⨿ D) ≫ endExit = 𝟙 X := coprod.inl_desc _ _
  simpa only [Category.assoc, remove, Category.comp_id] using e.symm

private abbrev Seed := Paper.WithEntryLet.Step (τ := Ty Empty) (Φ := Instruction)

local notation "J" => projection Seed
local notation "I" => iterateChosen Seed

private theorem corrected_request : (J).map moved = (J).map flat := by
  have move : Paper.WithEntryLet.Site.here.move flatRequest = some movedRequest := rfl
  exact ((Paper.Extension.Singleton.ofRegion_eq_iff Seed flatRequest_typed movedRequest_typed).2
    (Paper.WithEntryLet.Site.move_sound .here flatRequest_typed move).2).symm

private noncomputable abbrev left := projectStep Seed (row moved)
private noncomputable abbrev right := projectStep Seed (row flat)

private theorem corrected_rows : left = right := by
  unfold left right row
  change (J).map (_ ≫ _) ≫ _ = (J).map (_ ≫ _) ≫ _
  rw [(J).map_comp, (J).map_comp]
  congr 2
  apply projection_map_desc_congr Seed
  · rfl
  · rw [(J).map_comp, (J).map_comp, corrected_request]

private noncomputable abbrev hideTag : (J).obj D ⨿ (J).obj D ⟶ (J).obj D :=
  coprod.desc (𝟙 _) (𝟙 _)

private theorem square :
    step left right ≫ coprod.map (𝟙 ((J).obj X)) hideTag = hideTag ≫ right := by
  apply coprod.hom_ext
  · rw [step, coprod.inl_desc_assoc, Category.assoc, coprod.map_map, Category.id_comp,
      coprod.inr_desc, coprod.map_id_id, Category.comp_id, coprod.inl_desc_assoc, Category.id_comp,
      corrected_rows]
  · rw [step, coprod.inr_desc_assoc, Category.assoc, coprod.map_map, Category.id_comp,
      coprod.inl_desc, coprod.map_id_id, Category.comp_id, coprod.inr_desc_assoc, Category.id_comp]

example : I (step left right) = hideTag ≫ I right := by
  have reduction := fold_iff_double Seed (Iso.refl ((J).obj D ⨿ (J).obj D)) hideTag
    (step left right) right left right
    (by simpa only [Iso.refl_hom, Category.comp_id] using coprod.inl_desc (𝟙 ((J).obj D)) (𝟙 _))
    (by simpa only [Iso.refl_hom, Category.comp_id] using coprod.inr_desc (𝟙 ((J).obj D)) (𝟙 _))
    (by simp only [Iso.refl_hom, Category.comp_id, step, coprod.inl_desc])
    (by simp only [Iso.refl_hom, Category.comp_id, step, coprod.inr_desc]) square
  apply reduction.mpr
  rw [← projectStep_double Seed, iterateChosen_projectStep, iterateChosen_projectStep, double_row]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.AlternatingFold.Example

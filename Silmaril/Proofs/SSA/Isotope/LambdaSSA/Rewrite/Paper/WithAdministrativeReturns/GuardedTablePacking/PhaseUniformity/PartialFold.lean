module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Rounds
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Coproducts.Finite.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Thms

/-! # Uniformity along a partial fold, from the total fold

The untouched state is cut into the exit of the block that is folded. The
total-fold seed applies to that block alone. Elimination of the block in
default Paper reassembles the two entries.
-/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity (Step)
open Paper.Extension.Singleton (projection iterateChosen projectStep iterateChosen_projectStep
  sumCofan sumCofanIsColimit)
open Paper.TypeCategory (ofType iterate phaseType phaseFold sumIso)
open SingletonPhases (system fold_eq)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.PhaseIteration (eliminate_both)

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

set_option hygiene false in
local notation "N" => Step (τ := τ) (Φ := Φ) pe
set_option hygiene false in
local notation "π" => projection (Step (τ := τ) (Φ := Φ) pe)

set_option backward.isDefEq.respectTransparency false

/-- The projection of a default Paper loop depends on the projection of its step. -/
theorem iterate_congr {X Y : Paper.TypeCategory (τ := τ) Φ} {s t : X ⟶ Y ⨿ X}
    (h : (π).map s = (π).map t) : (π).map (iterate s) = (π).map (iterate t) := by
  rw [← iterateChosen_projectStep N s, ← iterateChosen_projectStep N t]
  exact congrArg (iterateChosen N) (congrArg (· ≫ _) h)

/-- The projection of a copair depends on the projections of its legs. -/
theorem desc_congr {U X T : τ} (u : ofType (Φ := Φ) U ⟶ ofType T) {x y : ofType (Φ := Φ) X ⟶ ofType T}
    (h : (π).map x = (π).map y) :
    (π).map (coprod.desc u x) = (π).map (coprod.desc u y) := by
  have exact (z : ofType (Φ := Φ) X ⟶ ofType T) :
      coprod.desc u z = (sumIso U X).inv ≫ ((sumIso U X).hom ≫ coprod.desc u z) := by
    rw [Iso.inv_hom_id_assoc]
  have il (z : ofType (Φ := Φ) X ⟶ ofType T) :
      (Paper.TypeCategory.sumCofan U X).inl ≫ ((sumIso U X).hom ≫ coprod.desc u z) = u :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ coprod.desc u z) (Paper.TypeCategory.sumCofan_inl_sumIso_hom U X)).trans
        (coprod.inl_desc _ _))
  have ir (z : ofType (Φ := Φ) X ⟶ ofType T) :
      (Paper.TypeCategory.sumCofan U X).inr ≫ ((sumIso U X).hom ≫ coprod.desc u z) = z :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ coprod.desc u z) (Paper.TypeCategory.sumCofan_inr_sumIso_hom U X)).trans
        (coprod.inr_desc _ _))
  have legs : (π).map ((sumIso U X).hom ≫ coprod.desc u x) =
      (π).map ((sumIso U X).hom ≫ coprod.desc u y) := by
    apply BinaryCofan.IsColimit.hom_ext (sumCofanIsColimit N U X)
    · exact ((π).map_comp _ _).symm.trans
        ((congrArg (π).map ((il x).trans (il y).symm)).trans ((π).map_comp _ _))
    · exact ((π).map_comp _ _).symm.trans ((congrArg (π).map (ir x)).trans
        (h.trans ((congrArg (π).map (ir y)).symm.trans ((π).map_comp _ _))))
  exact (congrArg (π).map (exact x)).trans (((π).map_comp _ _).trans
    ((congrArg ((π).map (sumIso U X).inv ≫ ·) legs).trans
      (((π).map_comp _ _).symm.trans (congrArg (π).map (exact y).symm))))

variable (A : τ) (k : Nat) {Y : τ}

set_option hygiene false in
local notation "S" => system (Φ := Φ) A

/-- A state row that exits or enters the block, joined with a block that
exits, returns to the state, or stays in the block. -/
noncomputable abbrev joined (a : ofType (Φ := Φ) A ⟶ ofType Y ⨿ ofType (phaseType A k))
    (c : ofType (Φ := Φ) (phaseType A k) ⟶ (ofType Y ⨿ ofType A) ⨿ ofType (phaseType A k)) :
    ofType (Φ := Φ) (phaseType A (k + 1)) ⟶ ofType Y ⨿ ofType (phaseType A (k + 1)) :=
  (S).desc k (a ≫ coprod.map (𝟙 _) ((S).inr k))
    (c ≫ coprod.desc (coprod.map (𝟙 _) ((S).inl k)) ((S).inr k ≫ coprod.inr))

variable (a : ofType (Φ := Φ) A ⟶ ofType Y ⨿ ofType (phaseType A k))
  (c : ofType (Φ := Φ) (phaseType A k) ⟶ (ofType Y ⨿ ofType A) ⨿ ofType (phaseType A k))
  (a' : ofType (Φ := Φ) A ⟶ ofType Y ⨿ ofType A)
  (c' : ofType (Φ := Φ) A ⟶ (ofType Y ⨿ ofType A) ⨿ ofType A)
  (entry : a ≫ coprod.map (𝟙 _) (phaseFold A k) = a')
  (block : c ≫ coprod.map (𝟙 _) (phaseFold A k) = phaseFold A k ≫ c')

include block in
theorem block_loop : (π).map (iterate c) = (π).map (phaseFold A k ≫ iterate c') :=
  fold_uniform pe k c c' block

include entry block in
/-- Entered at the untouched state. -/
theorem partial_state :
    (π).map ((S).inl k ≫ iterate (joined A k a c)) = (π).map ((S).inl 0 ≫ iterate (joined A 0 a' c')) := by
  have left := (eliminate_both (S) k a c).1
  have right := (eliminate_both (S) 0 a' c').1
  have inner := block_loop pe A k c c' block
  have step : (π).map (a ≫ coprod.desc coprod.inl (iterate c)) =
      (π).map (a' ≫ coprod.desc coprod.inl (iterate c')) := by
    have moved : a ≫ coprod.desc coprod.inl (phaseFold A k ≫ iterate c') =
        a' ≫ coprod.desc coprod.inl (iterate c') := by
      rw [← entry, Category.assoc]
      congr 1
      apply coprod.hom_ext <;> simp
    rw [← moved, Functor.map_comp, Functor.map_comp]
    exact congrArg ((π).map a ≫ ·) (desc_congr pe coprod.inl inner)
  exact (congrArg (π).map left).trans ((iterate_congr pe step).trans (congrArg (π).map right).symm)

include entry block in
/-- Entered in the block. -/
theorem partial_block :
    (π).map ((S).inr k ≫ iterate (joined A k a c)) =
      (π).map (phaseFold A k ≫ (S).inr 0 ≫ iterate (joined A 0 a' c')) := by
  have left := (eliminate_both (S) k a c).2
  have right := (eliminate_both (S) 0 a' c').2
  have inner := block_loop pe A k c c' block
  have state := partial_state pe A k a c a' c' entry block
  calc
    (π).map ((S).inr k ≫ iterate (joined A k a c)) =
        (π).map (iterate c) ≫ (π).map (coprod.desc (𝟙 _) ((S).inl k ≫ iterate (joined A k a c))) :=
      (congrArg (π).map left).trans ((π).map_comp _ _)
    _ = (π).map (phaseFold A k ≫ iterate c') ≫
        (π).map (coprod.desc (𝟙 _) ((S).inl 0 ≫ iterate (joined A 0 a' c'))) :=
      congrArg₂ (· ≫ ·) inner (desc_congr pe (𝟙 (ofType Y)) state)
    _ = (π).map (phaseFold A k ≫ (S).inr 0 ≫ iterate (joined A 0 a' c')) := by
      rw [← Functor.map_comp, Category.assoc]
      exact congrArg (fun z => (π).map (phaseFold A k ≫ z)) right.symm

include entry block in
/-- Uniformity along the partial fold. -/
theorem partial_uniform :
    (π).map (iterate (joined A k a c)) =
      (π).map ((S).desc k ((S).inl 0) (phaseFold A k ≫ (S).inr 0) ≫ iterate (joined A 0 a' c')) := by
  have il : (Paper.TypeCategory.sumCofan (Φ := Φ) A (phaseType A k)).inl = (S).inl k :=
    ((Iso.comp_inv_eq _).2 (Paper.TypeCategory.sumCofan_inl_sumIso_hom A (phaseType A k)).symm).symm
  have ir : (Paper.TypeCategory.sumCofan (Φ := Φ) A (phaseType A k)).inr = (S).inr k :=
    ((Iso.comp_inv_eq _).2 (Paper.TypeCategory.sumCofan_inr_sumIso_hom A (phaseType A k)).symm).symm
  apply BinaryCofan.IsColimit.hom_ext (sumCofanIsColimit N A (phaseType A k))
  · refine ((π).map_comp _ _).symm.trans ((congrArg (fun z => (π).map (z ≫ iterate (joined A k a c))) il).trans
      ((partial_state pe A k a c a' c' entry block).trans ?_))
    refine Eq.trans ?_ ((congrArg (fun z => (π).map (z ≫ (S).desc k ((S).inl 0) (phaseFold A k ≫ (S).inr 0) ≫
      iterate (joined A 0 a' c'))) il).symm.trans ((π).map_comp _ _))
    exact congrArg (π).map ((congrArg (· ≫ iterate (joined A 0 a' c')) ((S).inl_desc k _ _).symm).trans
      (Category.assoc _ _ _))
  · refine ((π).map_comp _ _).symm.trans ((congrArg (fun z => (π).map (z ≫ iterate (joined A k a c))) ir).trans
      ((partial_block pe A k a c a' c' entry block).trans ?_))
    refine Eq.trans ?_ ((congrArg (fun z => (π).map (z ≫ (S).desc k ((S).inl 0) (phaseFold A k ≫ (S).inr 0) ≫
      iterate (joined A 0 a' c'))) ir).symm.trans ((π).map_comp _ _))
    exact congrArg (π).map (((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ iterate (joined A 0 a' c')) ((S).inr_desc k _ _).symm)).trans (Category.assoc _ _ _))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity

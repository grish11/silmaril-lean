module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonBlocks
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Laws.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Values.Discard.Coproducts.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Coproducts.Finite.Thms

/-! # The projection onto a contextual extension preserves sums and blocks -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonProjection

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.Extension.Singleton (projection iterateChosen projectStep iterateChosen_projectStep
  sumCofan sumCofanIsColimit)
open Paper.Extension.Singleton.ValueCoproducts (exactCopair)
open Paper.TypeCategory (ofType iterate sumIso sumInl sumInr blockStep sumMap)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

set_option hygiene false in
local notation "π" => projection Seed

set_option backward.isDefEq.respectTransparency false

/-- Copairing at the exact sum goes to the quotient's exact copair. -/
theorem map_copair {A B T : τ} (f : ofType (Φ := Φ) A ⟶ ofType T) (g : ofType (Φ := Φ) B ⟶ ofType T) :
    (π).map ((sumIso A B).hom ≫ coprod.desc f g) = exactCopair Seed ((π).map f) ((π).map g) := by
  have il : (Paper.TypeCategory.sumCofan A B).inl ≫ ((sumIso A B).hom ≫ coprod.desc f g) = f :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ coprod.desc f g) (Paper.TypeCategory.sumCofan_inl_sumIso_hom A B)).trans
        (coprod.inl_desc _ _))
  have ir : (Paper.TypeCategory.sumCofan A B).inr ≫ ((sumIso A B).hom ≫ coprod.desc f g) = g :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ coprod.desc f g) (Paper.TypeCategory.sumCofan_inr_sumIso_hom A B)).trans
        (coprod.inr_desc _ _))
  apply BinaryCofan.IsColimit.hom_ext (sumCofanIsColimit Seed A B)
  · exact ((π).map_comp _ _).symm.trans ((congrArg (π).map il).trans
      ((sumCofanIsColimit Seed A B).fac (BinaryCofan.mk ((π).map f) ((π).map g)) ⟨WalkingPair.left⟩).symm)
  · exact ((π).map_comp _ _).symm.trans ((congrArg (π).map ir).trans
      ((sumCofanIsColimit Seed A B).fac (BinaryCofan.mk ((π).map f) ((π).map g)) ⟨WalkingPair.right⟩).symm)

/-- Copairing at Paper's chosen coproduct, through the comparison with the exact sum. -/
theorem map_desc {A B T : τ} (f : ofType (Φ := Φ) A ⟶ ofType T) (g : ofType (Φ := Φ) B ⟶ ofType T) :
    (π).map (coprod.desc f g) = (π).map (sumIso A B).inv ≫ exactCopair Seed ((π).map f) ((π).map g) := by
  rw [← map_copair, ← Functor.map_comp, Iso.inv_hom_id_assoc]

theorem desc_congr {A B T : τ} {f f' : ofType (Φ := Φ) A ⟶ ofType T} {g g' : ofType (Φ := Φ) B ⟶ ofType T}
    (hf : (π).map f = (π).map f') (hg : (π).map g = (π).map g') :
    (π).map (coprod.desc f g) = (π).map (coprod.desc f' g') := by
  rw [map_desc, map_desc, hf, hg]

theorem iterate_congr {X Y : Paper.TypeCategory (τ := τ) Φ} {s t : X ⟶ Y ⨿ X}
    (h : (π).map s = (π).map t) : (π).map (iterate s) = (π).map (iterate t) := by
  rw [← iterateChosen_projectStep Seed s, ← iterateChosen_projectStep Seed t]
  exact congrArg (iterateChosen Seed) (congrArg (· ≫ _) h)

variable (R : τ) {D E Y : τ}

/-- The loop of a joined step goes to the exact copair of its two entries,
each given by block elimination. -/
theorem map_blockStep (r : ofType (Φ := Φ) R ⟶ (ofType Y ⨿ ofType R) ⨿ ofType D)
    (c : ofType (Φ := Φ) D ⟶ (ofType Y ⨿ ofType R) ⨿ ofType D) :
    (π).map (iterate (blockStep R D r c)) =
      exactCopair Seed ((π).map (iterate (r ≫ coprod.desc (𝟙 _) (iterate c))))
        ((π).map (iterate c ≫ coprod.desc (𝟙 _) (sumInl R D ≫ iterate (blockStep R D r c)))) := by
  have bek := SingletonBlocks.bekic R D r c
  exact (congrArg (π).map (SingletonBlocks.sum_decomp R D (iterate (blockStep R D r c)))).trans
    ((map_copair Seed _ _).trans
      (congrArg₂ (exactCopair Seed) (congrArg (π).map bek.1) (congrArg (π).map bek.2)))

/-- Uniformity of the right block alone lifts to the joined step, along
`id_R + h`. The left block may repeat into itself. -/
theorem right_block (h : ofType (Φ := Φ) D ⟶ ofType E)
    (r : ofType (Φ := Φ) R ⟶ (ofType Y ⨿ ofType R) ⨿ ofType D)
    (c : ofType (Φ := Φ) D ⟶ (ofType Y ⨿ ofType R) ⨿ ofType D)
    (r' : ofType (Φ := Φ) R ⟶ (ofType Y ⨿ ofType R) ⨿ ofType E)
    (c' : ofType (Φ := Φ) E ⟶ (ofType Y ⨿ ofType R) ⨿ ofType E)
    (row : r ≫ coprod.map (𝟙 _) h = r')
    (inner : (π).map (iterate c) = (π).map (h ≫ iterate c')) :
    (π).map (sumInl R D ≫ iterate (blockStep R D r c)) =
        (π).map (sumInl R E ≫ iterate (blockStep R E r' c')) ∧
    (π).map (sumInr R D ≫ iterate (blockStep R D r c)) =
        (π).map (h ≫ sumInr R E ≫ iterate (blockStep R E r' c')) ∧
    (π).map (iterate (blockStep R D r c)) =
        (π).map (sumMap R h ≫ iterate (blockStep R E r' c')) := by
  have bekD := SingletonBlocks.bekic R D r c
  have bekE := SingletonBlocks.bekic R E r' c'
  have moved : r ≫ coprod.desc (𝟙 _) (h ≫ iterate c') = r' ≫ coprod.desc (𝟙 _) (iterate c') := by
    rw [← row, Category.assoc]
    congr 1
    apply coprod.hom_ext <;> simp
  have step : (π).map (r ≫ coprod.desc (𝟙 _) (iterate c)) =
      (π).map (r' ≫ coprod.desc (𝟙 _) (iterate c')) := by
    rw [← moved, Functor.map_comp, Functor.map_comp]
    exact congrArg ((π).map r ≫ ·) (desc_congr Seed rfl inner)
  have state : (π).map (sumInl R D ≫ iterate (blockStep R D r c)) =
      (π).map (sumInl R E ≫ iterate (blockStep R E r' c')) :=
    (congrArg (π).map bekD.1).trans ((iterate_congr Seed step).trans (congrArg (π).map bekE.1).symm)
  have block : (π).map (sumInr R D ≫ iterate (blockStep R D r c)) =
      (π).map (h ≫ sumInr R E ≫ iterate (blockStep R E r' c')) :=
    calc
      (π).map (sumInr R D ≫ iterate (blockStep R D r c)) =
          (π).map (iterate c) ≫
            (π).map (coprod.desc (𝟙 _) (sumInl R D ≫ iterate (blockStep R D r c))) :=
        (congrArg (π).map bekD.2).trans ((π).map_comp _ _)
      _ = (π).map (h ≫ iterate c') ≫
            (π).map (coprod.desc (𝟙 _) (sumInl R E ≫ iterate (blockStep R E r' c'))) :=
        congrArg₂ (· ≫ ·) inner (desc_congr Seed rfl state)
      _ = (π).map (h ≫ sumInr R E ≫ iterate (blockStep R E r' c')) := by
        rw [← Functor.map_comp, Category.assoc]
        exact congrArg (fun z => (π).map (h ≫ z)) bekE.2.symm
  refine ⟨state, block, ?_⟩
  have folded : sumMap R h ≫ iterate (blockStep R E r' c') =
      (sumIso R D).hom ≫ coprod.desc (sumInl R E ≫ iterate (blockStep R E r' c'))
        (h ≫ sumInr R E ≫ iterate (blockStep R E r' c')) := by
    unfold sumMap
    rw [Category.assoc]
    congr 1
    apply coprod.hom_ext <;> simp
  exact (congrArg (π).map (SingletonBlocks.sum_decomp R D (iterate (blockStep R D r c)))).trans
    ((map_copair Seed _ _).trans ((congrArg₂ (exactCopair Seed) state block).trans
      ((map_copair Seed _ _).symm.trans (congrArg (π).map folded.symm))))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonProjection

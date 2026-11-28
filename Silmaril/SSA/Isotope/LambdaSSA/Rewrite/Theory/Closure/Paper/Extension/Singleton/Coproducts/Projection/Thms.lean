module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Bekic.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Laws.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Values.Discard.Coproducts.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Coproducts.Finite.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonProjection

/-! # The projection onto a contextual extension preserves sums and blocks

For any seed. The exact-sum injections of the quotient are the projected
injections by definition. Copairing and block iteration are transported
here. Squares may then be checked in default Paper and used in the
quotient.
-/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LambdaSSA (VCtx LCtx)
open ValueCoproducts (exactCopair)
open Paper.TypeCategory (iterate sumInl sumInr blockStep sumMap)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

local notation "Obj" => Paper.TypeCategory.ofType (Φ := Φ)

theorem projection_sumCofan_inl (A B : τ) :
    (projection Seed).map (Paper.TypeCategory.sumCofan (Φ := Φ) A B).inl = (sumCofan Seed A B).inl := rfl

theorem projection_sumCofan_inr (A B : τ) :
    (projection Seed).map (Paper.TypeCategory.sumCofan (Φ := Φ) A B).inr = (sumCofan Seed A B).inr := rfl

/-- Copairing at the exact sum goes to the quotient's exact copair. -/
theorem projection_copair {A B T : τ} (f : Obj A ⟶ Obj T) (g : Obj B ⟶ Obj T) :
    (projection Seed).map ((Paper.TypeCategory.sumIso A B).hom ≫ coprod.desc f g) =
      exactCopair Seed ((projection Seed).map f) ((projection Seed).map g) :=
  SingletonProjection.map_copair Seed f g

/-- Copairing at Paper's chosen coproduct, through its comparison with the exact sum. -/
theorem projection_desc {A B T : τ} (f : Obj A ⟶ Obj T) (g : Obj B ⟶ Obj T) :
    (projection Seed).map (coprod.desc f g) =
      (projection Seed).map (Paper.TypeCategory.sumIso A B).inv ≫
        exactCopair Seed ((projection Seed).map f) ((projection Seed).map g) :=
  SingletonProjection.map_desc Seed f g

/-- The projection of a copair depends only on the projections of its legs. -/
theorem projection_desc_congr {A B T : τ} {f f' : Obj A ⟶ Obj T} {g g' : Obj B ⟶ Obj T}
    (hf : (projection Seed).map f = (projection Seed).map f')
    (hg : (projection Seed).map g = (projection Seed).map g') :
    (projection Seed).map (coprod.desc f g) = (projection Seed).map (coprod.desc f' g') :=
  SingletonProjection.desc_congr Seed hf hg

/-- The projection of a loop depends only on the projection of its step. -/
theorem projection_iterate_congr {X Y : Paper.TypeCategory (τ := τ) Φ} {s t : X ⟶ Y ⨿ X}
    (h : (projection Seed).map s = (projection Seed).map t) :
    (projection Seed).map (iterate s) = (projection Seed).map (iterate t) :=
  SingletonProjection.iterate_congr Seed h

variable (R : τ) {D E Y : τ}

/-- The loop of a joined step goes to the exact copair of its two entries,
each computed by block elimination. -/
theorem projection_blockStep (r : Obj R ⟶ (Obj Y ⨿ Obj R) ⨿ Obj D)
    (c : Obj D ⟶ (Obj Y ⨿ Obj R) ⨿ Obj D) :
    (projection Seed).map (iterate (blockStep R D r c)) =
      exactCopair Seed ((projection Seed).map (iterate (r ≫ coprod.desc (𝟙 _) (iterate c))))
        ((projection Seed).map
          (iterate c ≫ coprod.desc (𝟙 _) (sumInl R D ≫ iterate (blockStep R D r c)))) :=
  SingletonProjection.map_blockStep Seed R r c

/-- Uniformity of the right block alone, with the left block among its
exits, lifts to the joined step along `id_R + h`. The left block may
repeat into itself. The premise `row` is an equation of default Paper. The
premise `inner` is an equation of the quotient. -/
theorem projection_right_block (h : Obj D ⟶ Obj E)
    (r : Obj R ⟶ (Obj Y ⨿ Obj R) ⨿ Obj D) (c : Obj D ⟶ (Obj Y ⨿ Obj R) ⨿ Obj D)
    (r' : Obj R ⟶ (Obj Y ⨿ Obj R) ⨿ Obj E) (c' : Obj E ⟶ (Obj Y ⨿ Obj R) ⨿ Obj E)
    (row : r ≫ coprod.map (𝟙 _) h = r')
    (inner : (projection Seed).map (iterate c) = (projection Seed).map (h ≫ iterate c')) :
    (projection Seed).map (sumInl R D ≫ iterate (blockStep R D r c)) =
        (projection Seed).map (sumInl R E ≫ iterate (blockStep R E r' c')) ∧
    (projection Seed).map (sumInr R D ≫ iterate (blockStep R D r c)) =
        (projection Seed).map (h ≫ sumInr R E ≫ iterate (blockStep R E r' c')) ∧
    (projection Seed).map (iterate (blockStep R D r c)) =
        (projection Seed).map (sumMap R h ≫ iterate (blockStep R E r' c')) :=
  SingletonProjection.right_block Seed R h r c r' c' row inner

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton

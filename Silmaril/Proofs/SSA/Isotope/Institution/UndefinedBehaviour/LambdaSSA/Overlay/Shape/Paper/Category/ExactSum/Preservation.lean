module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Category.Thms
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.ExactSum.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Coproducts.Finite.Thms
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Continuation.Values
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Category.Representatives

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Category.ExactSum

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics (extend)
open Silmaril.Isotope.Morphism.SSAIter (envOfBound envOfBound_agrees)
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape (ValueTyped)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category (arrow_ext sumInl sumInr sumDesc single)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Paper (singletonInterpretation singletonInterpretation_map_ofRegion)
open Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory (ofType sumCofan sumCofan_inl sumCofan_inr sumCofanIsColimit)
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Continuation (Ops PureValue)

universe u v w x

variable {Φ : Type u} {κ : Type v} [HasTy Φ (Ty κ)] {A B : Ty κ}

private abbrev ops (M : Shape.Model.{u,v,w,x} Φ ([] : List (Ty κ))) : Ops Φ M.raw.α M.raw.σ :=
  ⟨M.raw.instr, M.raw.faults, M.raw.prim⟩

private theorem denote_pure_branch (M : Shape.Model.{u,v,w,x} Φ ([] : List (Ty κ)))
    {a b : Value M.raw.α} (ha : ValueTyped M.atomType a A) {t : LambdaSSA.Tm Φ} (ht : t.HasType [A] B)
    (pure : PureValue (ops M) (extend (envOfBound M.raw.bound) a) t b) (s : M.raw.σ) :
    Shape.denote (.native (⟨.br 0 t, .br (ℓ := 0) rfl ht⟩ : UB.Typed (Φ := Φ) [A] [B])) (M.extend ha) s =
      ↑({Outcome.ret 0 b s} : Set (Outcome 1 M.raw.α M.raw.σ)) := by
  exact congrArg WithTop.some
    (Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Category.branch_outcomes
      (M.extend ha).raw ((envOfBound_agrees M.raw.bound).extend a) ht pure s)

theorem map_sumInl (M : Shape.Model.{u,v,w,x} Φ ([] : List (Ty κ))) (A B : Ty κ) :
    (singletonInterpretation M).map (sumCofan (Φ := Φ) A B).inl = sumInl A B := by
  rw [sumCofan_inl]
  apply arrow_ext
  intro i a s
  have hi : i = (0 : Fin 1) := Fin.eq_zero i
  subst i
  refine (singletonInterpretation_map_ofRegion M (.br (ℓ := 0) rfl (.inl (.var (i := 0) rfl)))
    a.property s).trans ?_
  exact denote_pure_branch M a.property (.inl (.var (i := 0) rfl))
    ((PureValue.var (O := ops M) (env := extend (envOfBound M.raw.bound) a.val) 0).inl) s

theorem map_sumInr (M : Shape.Model.{u,v,w,x} Φ ([] : List (Ty κ))) (A B : Ty κ) :
    (singletonInterpretation M).map (sumCofan (Φ := Φ) A B).inr = sumInr A B := by
  rw [sumCofan_inr]
  apply arrow_ext
  intro i b s
  have hi : i = (0 : Fin 1) := Fin.eq_zero i
  subst i
  refine (singletonInterpretation_map_ofRegion M (.br (ℓ := 0) rfl (.inr (.var (i := 0) rfl)))
    b.property s).trans ?_
  exact denote_pure_branch M b.property (.inr (.var (i := 0) rfl))
    ((PureValue.var (O := ops M) (env := extend (envOfBound M.raw.bound) b.val) 0).inr) s

variable (M : Shape.Model.{u,v,w,x} Φ ([] : List (Ty κ)))

local notation "F" => singletonInterpretation M

set_option backward.isDefEq.respectTransparency false in
theorem map_sumDesc {D : Ty κ} (f : ofType (Φ := Φ) A ⟶ ofType D) (g : ofType B ⟶ ofType D) :
    (F).map ((sumCofanIsColimit A B).desc (BinaryCofan.mk f g)) = sumDesc ((F).map f) ((F).map g) := by
  apply Shape.Category.sum_hom_ext
  · rw [Shape.Category.sumInl_desc, ← map_sumInl M, ← Functor.map_comp]
    exact congrArg (F).map ((sumCofanIsColimit A B).fac (BinaryCofan.mk f g) ⟨WalkingPair.left⟩)
  · rw [Shape.Category.sumInr_desc, ← map_sumInr M, ← Functor.map_comp]
    exact congrArg (F).map ((sumCofanIsColimit A B).fac (BinaryCofan.mk f g) ⟨WalkingPair.right⟩)

theorem map_emptyElim (A : Ty κ) :
    (F).map ((Region.Paper.TypeCategory.emptyIsInitial (Φ := Φ) (τ := Ty κ)).to (ofType A)) =
      Shape.Category.emptyElim (single A) :=
  Shape.Category.empty_hom_ext _ _

set_option backward.isDefEq.respectTransparency false in
noncomputable def map_sumCofan_isColimit (A B : Ty κ) :
    IsColimit ((F).mapCocone (sumCofan (Φ := Φ) A B)) := by
  let e : IsColimit ((F).mapCocone (sumCofan (Φ := Φ) A B)) ≃
      IsColimit ((sumCofan (Φ := Φ) A B).map (F)) := BinaryCofan.isColimitMapCoconeEquiv
  refine e.symm ?_
  change IsColimit (BinaryCofan.mk ((F).map (sumCofan A B).inl) ((F).map (sumCofan A B).inr))
  rw [map_sumInl M, map_sumInr M]
  exact Shape.Category.sumIsColimit A B

theorem preservesBinary : PreservesColimitsOfShape (Discrete WalkingPair) (F) where
  preservesColimit := by
    intro K
    let A : Ty κ := K.obj ⟨WalkingPair.left⟩
    let B : Ty κ := K.obj ⟨WalkingPair.right⟩
    have : PreservesColimit (pair (K.obj ⟨WalkingPair.left⟩) (K.obj ⟨WalkingPair.right⟩)) (F) :=
      preservesColimit_of_preserves_colimit_cocone
        (sumCofanIsColimit (Φ := Φ) A B) (map_sumCofan_isColimit M A B)
    exact preservesColimit_of_iso_diagram (F) (diagramIsoPair K).symm

theorem preservesFinite : PreservesFiniteCoproducts (F) where
  preserves n := by
    have := preservesBinary M
    have : PreservesColimit (Functor.empty.{0} (Region.Paper.TypeCategory (τ := Ty κ) Φ)) (F) :=
      preservesColimit_of_preserves_colimit_cocone
        (Region.Paper.TypeCategory.emptyIsInitial (Φ := Φ) (τ := Ty κ))
        ((isColimitMapCoconeEmptyCoconeEquiv (F) _).symm Shape.Category.emptyIsInitial)
    have := preservesColimitsOfShape_pempty_of_preservesInitial (F)
    exact PreservesFiniteCoproducts.of_preserves_binary_and_initial (F) (Fin n)

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Category.ExactSum

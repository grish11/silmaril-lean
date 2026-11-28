module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.CfgReadback.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.UnusedSummand.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution.KnownTag.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummand

/-! # Exact CFG denotation on a common left-tag dispatcher -/

public section

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open UnusedSummand
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  {κ : Type u} (M : TypeModel (Ty κ) V) {Φ : Type v} [HasTy Φ (Ty κ)] [InstructionModel J M Φ]

/-- Compare a common left-tag dispatcher with a wide one whose exits also
carry a pure payload map. The local equations are taken on the original
witnesses. Their feedback states may have different types. -/
theorem CfgDenotesAt.postmap_of_taken_tag_squares {k : Nat} {P : Fin (k + 1) → Ty κ}
    {K : LCtx (Ty κ)} {Γ : VCtx (Ty κ)} (D : Fin (k + 1) → Ty κ) {K' : LCtx (Ty κ)}
    (out : (labelObj M K) ⟶ labelObj M K')
    {entry entry' : Region Φ} {rows rows' : Fin (k + 1) → Region Φ}
    (entryRoute : ∀ ⦃ts : entry.HasType Γ (List.ofFn P ++ K)⦄
      ⦃tw : entry'.HasType Γ (List.ofFn (family P (some D)) ++ K')⦄
      ⦃a : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M (List.ofFn P ++ K))⦄
      ⦃b : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M (List.ofFn (family P (some D)) ++ K'))⦄,
      RegionDenotes J M ts a → RegionDenotes J M tw b →
      b ≫ J.map (labelAppendSplit M (List.ofFn (family P (some D))) K') =
        a ≫ J.map (labelAppendSplit M (List.ofFn P) K) ≫
          J.map (coprod.map out (embedLabels M P D)))
    (rowRoutes : ∀ i
      ⦃ts : (rows i).HasType (P i :: Γ) (List.ofFn P ++ K)⦄
      ⦃tw : (rows' i).HasType (family P (some D) i :: Γ) (List.ofFn (family P (some D)) ++ K')⦄
      ⦃a : J.obj (ctxObj M (P i :: Γ)) ⟶ J.obj (labelObj M (List.ofFn P ++ K))⦄
      ⦃b : J.obj (ctxObj M (family P (some D) i :: Γ)) ⟶ J.obj (labelObj M (List.ofFn (family P (some D)) ++ K'))⦄,
      RegionDenotes J M ts a → RegionDenotes J M tw b →
      J.map (ctxObj M Γ ◁ (coprod.inl ≫ (M.coprodIso (P i) (D i)).inv)) ≫
        b ≫ J.map (labelAppendSplit M (List.ofFn (family P (some D))) K') =
          a ≫ J.map (labelAppendSplit M (List.ofFn P) K) ≫
            J.map (coprod.map out (embedLabels M P D)))
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M K)}
    {g : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M K')}
    (small : CfgDenotesAt J M P entry rows f)
    (wide : CfgDenotesAt J M (family P (some D)) entry' rows' g) : g = f ≫ J.map out :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandProof.taken_tag_postmap
    J M D out entryRoute rowRoutes small wide

/-- The common left-tag dispatcher only needs the entry and row equations
of the actual graphs. This form allows a row with its own native CFG. -/
theorem CfgDenotesAt.eq_of_taken_tag_squares {k : Nat} {P : Fin (k + 1) → Ty κ}
    {K : LCtx (Ty κ)} {Γ : VCtx (Ty κ)} (D : Fin (k + 1) → Ty κ)
    {entry entry' : Region Φ} {rows rows' : Fin (k + 1) → Region Φ}
    (entryRoute : ∀ ⦃ts : entry.HasType Γ (List.ofFn P ++ K)⦄
      ⦃tw : entry'.HasType Γ (List.ofFn (family P (some D)) ++ K)⦄
      ⦃a : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M (List.ofFn P ++ K))⦄
      ⦃b : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M (List.ofFn (family P (some D)) ++ K))⦄,
      RegionDenotes J M ts a → RegionDenotes J M tw b →
      b ≫ J.map (labelAppendSplit M (List.ofFn (family P (some D))) K) =
        a ≫ J.map (labelAppendSplit M (List.ofFn P) K) ≫
          J.map (coprod.map (𝟙 (labelObj M K)) (embedLabels M P D)))
    (rowRoutes : ∀ i
      ⦃ts : (rows i).HasType (P i :: Γ) (List.ofFn P ++ K)⦄
      ⦃tw : (rows' i).HasType (family P (some D) i :: Γ) (List.ofFn (family P (some D)) ++ K)⦄
      ⦃a : J.obj (ctxObj M (P i :: Γ)) ⟶ J.obj (labelObj M (List.ofFn P ++ K))⦄
      ⦃b : J.obj (ctxObj M (family P (some D) i :: Γ)) ⟶ J.obj (labelObj M (List.ofFn (family P (some D)) ++ K))⦄,
      RegionDenotes J M ts a → RegionDenotes J M tw b →
      J.map (ctxObj M Γ ◁ (coprod.inl ≫ (M.coprodIso (P i) (D i)).inv)) ≫
        b ≫ J.map (labelAppendSplit M (List.ofFn (family P (some D))) K) =
          a ≫ J.map (labelAppendSplit M (List.ofFn P) K) ≫
            J.map (coprod.map (𝟙 (labelObj M K)) (embedLabels M P D)))
    {f g : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M K)}
    (small : CfgDenotesAt J M P entry rows f)
    (wide : CfgDenotesAt J M (family P (some D)) entry' rows' g) : f = g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandProof.taken_tag_of_squares
    J M D entryRoute rowRoutes small wide

/-- Compare actual CFG witnesses when substituting the left-tag embedding
for each wide block parameter prunes its row to the common typed row,
with a left tag on every local transfer. The entry uses the same routing
and the outward label list is fixed. The comparison uses the existing
pure uniformity field of the supplied strong Elgot Freyd model. -/
theorem CfgDenotesAt.eq_of_taken_tag {k : Nat} {P : Fin (k + 1) → Ty κ}
    {K : LCtx (Ty κ)} {Γ : VCtx (Ty κ)}
    (D : Fin (k + 1) → Ty κ) (entry : Row (Φ := Φ) P K Γ)
    (rows : ∀ i, Row (Φ := Φ) P K (P i :: Γ)) (raw : Fin (k + 1) → Region Φ)
    (prune : ∀ i, Region.PruneConstructorTests
      ((raw i).substVars (Tm.replaceNewest (.inl (.var 0)))) ((rows i).region true id))
    {f g : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M K)}
    (small : CfgDenotesAt J M P (entry.region false id) (fun i => (rows i).region false id) f)
    (wide : CfgDenotesAt J M (family P (some D)) (entry.region true id) raw g) : f = g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandProof.taken_tag_agreement
    J M D entry rows raw prune small wide

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical

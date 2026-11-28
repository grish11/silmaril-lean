module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.CfgReadback.SlotMaps.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummand

/-! # Assemble componentwise state squares for exact CFG witnesses -/

public section

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

section Labels

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  {κ : Type u} (M : TypeModel (Ty κ) V)

/-- The componentwise state map uses the same index on both sides. -/
@[reassoc] theorem mapSlotLabels_inject {n : Nat} {P Q : Fin n → Ty κ}
    (slot : ∀ i, M.obj (P i) ⟶ M.obj (Q i)) (i : Fin n)
    (hi : At (List.ofFn P) i (P i)) (hj : At (List.ofFn Q) i (Q i)) :
    labelInject M i hi ≫ mapSlotLabels M slot = slot i ≫ labelInject M i hj :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandProof.mapSlot_inject M P slot i hi hj

@[reassoc] theorem mapLabelHead_zero {A B : Ty κ} (L : LCtx (Ty κ)) (h : M.obj A ⟶ M.obj B) :
    labelInject M 0 (rfl : At (A :: L) 0 A) ≫ mapLabelHead M L h =
      h ≫ labelInject M 0 (rfl : At (B :: L) 0 B) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandProof.mapHead_zero M L h

@[reassoc] theorem mapLabelHead_succ {A B T : Ty κ} (L : LCtx (Ty κ)) (h : M.obj A ⟶ M.obj B)
    {i : Nat} (hi : At L i T) :
    labelInject M (i + 1) (show At (A :: L) (i + 1) T from hi) ≫ mapLabelHead M L h =
      labelInject M (i + 1) (show At (B :: L) (i + 1) T from hi) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandProof.mapHead_succ M L h hi

end Labels

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  {κ : Type u} (M : TypeModel (Ty κ) V) {Φ : Type v} [HasTy Φ (Ty κ)] [InstructionModel J M Φ]

/-- Assemble a square on the exact CFG dispatchers from an entry square and
one square per corresponding row. Each state payload uses its own pure map.
The result follows from the existing pure uniformity and exit naturality. -/
theorem CfgDenotesAt.postmap_of_slot_squares {k : Nat} {P Q : Fin (k + 1) → Ty κ}
    {Γ : VCtx (Ty κ)} {K : LCtx (Ty κ)}
    (slot : ∀ i, M.obj (P i) ⟶ M.obj (Q i)) {K' : LCtx (Ty κ)}
    (out : labelObj M K ⟶ labelObj M K')
    {entry entry' : Region Φ} {rows rows' : Fin (k + 1) → Region Φ}
    (entryRoute : ∀ ⦃ts : entry.HasType Γ (List.ofFn P ++ K)⦄
      ⦃tw : entry'.HasType Γ (List.ofFn Q ++ K')⦄
      ⦃a : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M (List.ofFn P ++ K))⦄
      ⦃b : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M (List.ofFn Q ++ K'))⦄,
      RegionDenotes J M ts a → RegionDenotes J M tw b →
      b ≫ J.map (labelAppendSplit M (List.ofFn Q) K') =
        a ≫ J.map (labelAppendSplit M (List.ofFn P) K) ≫
          J.map (coprod.map out (mapSlotLabels M slot)))
    (rowRoutes : ∀ i
      ⦃ts : (rows i).HasType (P i :: Γ) (List.ofFn P ++ K)⦄
      ⦃tw : (rows' i).HasType (Q i :: Γ) (List.ofFn Q ++ K')⦄
      ⦃a : J.obj (ctxObj M (P i :: Γ)) ⟶ J.obj (labelObj M (List.ofFn P ++ K))⦄
      ⦃b : J.obj (ctxObj M (Q i :: Γ)) ⟶ J.obj (labelObj M (List.ofFn Q ++ K'))⦄,
      RegionDenotes J M ts a → RegionDenotes J M tw b →
      J.map (ctxObj M Γ ◁ (slot i)) ≫
        b ≫ J.map (labelAppendSplit M (List.ofFn Q) K') =
          a ≫ J.map (labelAppendSplit M (List.ofFn P) K) ≫
            J.map (coprod.map out (mapSlotLabels M slot)))
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M K)}
    {g : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M K')}
    (small : CfgDenotesAt J M P entry rows f)
    (wide : CfgDenotesAt J M Q entry' rows' g) : g = f ≫ J.map out :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandProof.slot_postmap
    J M slot out entryRoute rowRoutes small wide

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical

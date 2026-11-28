module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Categorical.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.PackedLabels
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.PackedDispatch

/-! # Categorical inversion of the linked packed-exit interface -/

public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA.Region (packedExitType packedExitArg unpackExits)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open CategoryTheory.CartesianMonoidalCategory (snd)

section Value

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)

/-- Packing sends each label injection to its own position in the nested sum. -/
@[reassoc] theorem labelInject_packLabel {L : LCtx τ} {i : Nat} {A : τ} (hi : At L i A) :
    labelInject M i hi ≫ packLabel M L = packedLabelInject M i hi :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.labelInject_packLabel M hi

theorem packLabel_unpackLabel (L : LCtx τ) : packLabel M L ≫ unpackLabel M L = 𝟙 _ :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.packLabel_unpackLabel M L

theorem unpackLabel_packLabel (L : LCtx τ) : unpackLabel M L ≫ packLabel M L = 𝟙 _ :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.unpackLabel_packLabel M L

/-- The interpretation of the written nested sum in the original label order. -/
@[expose] noncomputable def packLabelIso (L : LCtx τ) : labelObj M L ≅ M.obj (packedExitType L) where
  hom := packLabel M L
  inv := unpackLabel M L
  hom_inv_id := packLabel_unpackLabel M L
  inv_hom_id := unpackLabel_packLabel M L

@[simp]
theorem packLabelExit_unpackLabelExit (L : LCtx τ) :
    packLabelExit M L ≫ unpackLabelExit M L = 𝟙 _ :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.packLabelExit_unpackLabelExit M L

@[simp]
theorem unpackLabelExit_packLabelExit (L : LCtx τ) :
    unpackLabelExit M L ≫ packLabelExit M L = 𝟙 _ :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.unpackLabelExit_packLabelExit M L

end Value

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]

omit [FreydCategory.CentralUnit J] in
/-- The literal tag constructor denotes the injection for the original label. -/
theorem Denotes.packedExitArg {Γ : VCtx τ} {L : LCtx τ} {i : Nat} {A : τ} {a : Tm Φ}
    (hi : At L i A) {ha : Tm.HasType Γ a A} {f : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj A)}
    (da : Denotes J M ha f) :
    ∃ h : Tm.HasType Γ (packedExitArg i a) (packedExitType L),
      Denotes J M h (f ≫ J.map (packedLabelInject M i hi)) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.packedExitArg_denotes J M hi da

/-- The native decoder has the pure categorical denotation of unpacking the
most recent variable. For zero exits the interpreted payload is initial. -/
theorem RegionDenotes.unpackExits (Γ : VCtx τ) (L : LCtx τ) :
    ∃ h : Region.HasType (packedExitType L :: Γ) (unpackExits L : Region Φ) L,
      RegionDenotes J M h (J.map (snd (ctxObj M Γ) _ ≫ unpackLabel M L)) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.unpackExits_denotes J M Γ L

variable [RegionTypingCoherent (Φ := Φ) J M]

/-- Linking the native tag constructors onto a region packs its categorical
exit interface. The region may have arbitrary effectful branches or CFGs. -/
theorem denoteRegion_linkPackExits {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    (hr : Region.HasType Γ r L)
    (hs : Region.HasType Γ (r.linkExits L (fun i => .br 0 (packedExitArg i (.var 0)))) [packedExitType L]) :
    denoteRegion J M hs = denoteRegion J M hr ≫ J.map (packLabelExit M L) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.denoteRegion_link_payload J M hr hs _
    (Proofs.SSA.Isotope.LambdaSSA.Rewrite.packContinuation_denotes J M Γ L)

/-- Linking the actual decoder to a typed singleton exit applies the
categorical decoding map to the payload. -/
theorem denoteRegion_linkUnpackExits {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    (hr : Region.HasType Γ r [packedExitType L])
    (hs : Region.HasType Γ (r.linkExits [packedExitType L] (fun _ => unpackExits L)) L) :
    denoteRegion J M hs = denoteRegion J M hr ≫ J.map (unpackLabelExit M L) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.denoteRegion_link_payload J M hr hs _
    (Proofs.SSA.Isotope.LambdaSSA.Rewrite.unpackContinuation_denotes J M Γ L)

/-- Nested links that pack and then decode preserve the original denotation. -/
theorem denoteRegion_linkPackUnpack {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    (hr : Region.HasType Γ r L)
    (hp : Region.HasType Γ (r.linkExits L (fun i => .br 0 (packedExitArg i (.var 0)))) [packedExitType L])
    (hd : Region.HasType Γ
      ((r.linkExits L (fun i => .br 0 (packedExitArg i (.var 0)))).linkExits [packedExitType L]
        (fun _ => unpackExits L)) L) :
    denoteRegion J M hd = denoteRegion J M hr := by
  rw [denoteRegion_linkUnpackExits J M hp, denoteRegion_linkPackExits J M hr, Category.assoc,
    ← J.map_comp, packLabelExit_unpackLabelExit, J.map_id, Category.comp_id]

/-- Nested links that decode and then pack preserve the singleton-exit denotation. -/
theorem denoteRegion_linkUnpackPack {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    (hr : Region.HasType Γ r [packedExitType L])
    (hd : Region.HasType Γ (r.linkExits [packedExitType L] (fun _ => unpackExits L)) L)
    (hp : Region.HasType Γ
      ((r.linkExits [packedExitType L] (fun _ => unpackExits L)).linkExits L
        (fun i => .br 0 (packedExitArg i (.var 0)))) [packedExitType L]) :
    denoteRegion J M hp = denoteRegion J M hr := by
  rw [denoteRegion_linkPackExits J M hd, denoteRegion_linkUnpackExits J M hr, Category.assoc,
    ← J.map_comp, unpackLabelExit_packLabelExit, J.map_id, Category.comp_id]

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical

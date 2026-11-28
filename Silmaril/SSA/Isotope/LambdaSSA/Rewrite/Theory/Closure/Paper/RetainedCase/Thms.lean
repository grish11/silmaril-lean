module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedCase.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedLet.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RetainedCase

/-! # Literal case in the singleton paper category -/

public section

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CfgEta.TypeCategory
open CfgEta.TypeCategory.Retained (distributorRegion distributorRegion_typed)
open Paper.RetainedLet (returnOnce returnOnce_typed diagonal diagonal_typed unpackBody unpackBody_typed)
open Silmaril.DeBruijn (lift)

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedCase

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {X A B D : τ} {a : Tm Φ} {l r : Region Φ}

/-- Distribute and dispatch the packed input, then remove the constructor packing at each arm. -/
theorem route_normalizes (hl : ValueBranches [A, X] l [D]) (hr : ValueBranches [B, X] r [D]) :
    Paper.Eqv [Silmaril.product X (Silmaril.coprod A B)]
      (routeCase l r) (unpackBody (boundCase l r)) [D] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RetainedCase.route_normalizes
    hl hr

/-- The single-bind scrutinee form reduces to a let followed by case on the bound sum. -/
theorem single_bind_case (ha : Tm.HasType [X] a (Silmaril.coprod A B))
    (hl : ValueBranches [A, X] l [D]) (hr : ValueBranches [B, X] r [D]) :
    Paper.Eqv [X] (assembleCase (returnOnce a) l r) (.let₁ a (boundCase l r)) [D] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RetainedCase.single_bind_case
    ha hl hr

/-- The retagging scrutinee form reduces to literal case for any exactly typed scrutinee. -/
theorem literal_case (ha : Tm.HasType [X] a (Silmaril.coprod A B))
    (hl : ValueBranches [A, X] l [D]) (hr : ValueBranches [B, X] r [D]) :
    Paper.Eqv [X] (assembleCase (returnSum a) l r) (.case a l r) [D] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RetainedCase.literal_case
    ha hl hr

section Semantics

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (caseWithContext)

universe u₁ u₂ v₁ v₂

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

/-- The semantic case-bind law moves a scrutinee bind into the case without
any premise on the scrutinee or the regions in its arms. -/
theorem denote_boundCase_let {Γ : VCtx τ} {L : LCtx τ} (ha : Tm.HasType Γ a (Silmaril.coprod A B))
    (hl : HasType (A :: Γ) l L) (hr : HasType (B :: Γ) r L) :
    denoteRegion J M (.let₁ ha (boundCase_hasType hl hr)) = denoteRegion J M (.case ha hl hr) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RetainedCase.denote_boundCase_let
    J M ha hl hr

variable [FreydCategory.CentralUnit J]

/-- Case and immediate retagging preserve the arbitrary scrutinee's
denotation, including its effects. -/
theorem returnSum_denotation (ha : Tm.HasType [X] a (Silmaril.coprod A B))
    {f : J.obj (ctxObj M [X]) ⟶ J.obj (M.obj (Silmaril.coprod A B))}
    (d : Denotes J M ha f) :
    denoteSingletonRegion J M (returnSum_typed ha).hasType =
      J.map ((λ_ (M.obj X)).inv : M.obj X ⟶ ctxObj M [X]) ≫ f :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RetainedCase.returnSum_denotation
    J M ha d

/-- The full assembled case for the single-bind representative has the
denotation of the literal case on the original arbitrary scrutinee. -/
theorem denote_single_bind_case
    (shared : ∀ E S : V, ∃ h : J.obj E ⊗ J.obj S = J.obj (E ⊗ S),
      Functor.StrongPremonoidal.tensorIso (J := J) E S = eqToIso h)
    (ha : Tm.HasType [X] a (Silmaril.coprod A B))
    (hl : ValueBranches [A, X] l [D]) (hr : ValueBranches [B, X] r [D]) :
    denoteRegion J M (assembleCase_typed (returnOnce_typed ha) hl hr).hasType =
      denoteRegion J M (.case ha hl.hasType hr.hasType) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RetainedCase.denote_single_bind_case
    J M shared ha hl hr

end Semantics

section Quotient

open CategoryTheory

theorem assembleCase_ofRegion {p : Region Φ} (hp : ValueBranches [X] p [Silmaril.coprod A B])
    (hl : ValueBranches [A, X] l [D]) (hr : ValueBranches [B, X] r [D]) :
    assembledCaseArrow hp hl hr = Paper.TypeCategory.ofRegion (assembleCase_typed hp hl hr) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RetainedCase.assembleCase_ofRegion
    hp hl hr

theorem single_bind_case_ofRegion (ha : Tm.HasType [X] a (Silmaril.coprod A B))
    (hl : ValueBranches [A, X] l [D]) (hr : ValueBranches [B, X] r [D]) :
    assembledCaseArrow (returnOnce_typed ha) hl hr = Paper.TypeCategory.ofRegion (.let₁ ha (boundCase_typed hl hr)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RetainedCase.single_bind_case_ofRegion
    ha hl hr

/-- The retagging form gives the exact literal case arrow in the singleton paper quotient. -/
theorem literal_case_ofRegion (ha : Tm.HasType [X] a (Silmaril.coprod A B))
    (hl : ValueBranches [A, X] l [D]) (hr : ValueBranches [B, X] r [D]) :
    assembledCaseArrow (returnSum_typed ha) hl hr = Paper.TypeCategory.ofRegion (.case ha hl hr) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RetainedCase.literal_case_ofRegion
    ha hl hr

/-- The literal comparison for the single-bind form reduces to the explicit case-hoisting equation. -/
theorem single_bind_case_eq_literal_iff (ha : Tm.HasType [X] a (Silmaril.coprod A B))
    (hl : ValueBranches [A, X] l [D]) (hr : ValueBranches [B, X] r [D]) :
    assembledCaseArrow (returnOnce_typed ha) hl hr = Paper.TypeCategory.ofRegion (.case ha hl hr) ↔
      Paper.Eqv [X] (.let₁ a (boundCase l r)) (.case a l r) [D] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RetainedCase.single_bind_case_eq_literal_iff
    ha hl hr

theorem single_bind_case_ofRegion_value (ha : Tm.BranchValue [X] a (Silmaril.coprod A B))
    (hl : ValueBranches [A, X] l [D]) (hr : ValueBranches [B, X] r [D]) :
    assembledCaseArrow (returnOnce_typed ha.hasType) hl hr = Paper.TypeCategory.ofRegion (.case ha.hasType hl hr) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RetainedCase.single_bind_case_ofRegion_value
    ha hl hr

theorem routeCase_ofRegion (hl : ValueBranches [A, X] l [D]) (hr : ValueBranches [B, X] r [D]) :
    Paper.TypeCategory.ofRegion (τ := τ) (distributorRegion_typed X A B) ≫
      Paper.TypeCategory.ofRegion (τ := τ) (packedArms_typed hl hr) =
        Paper.TypeCategory.ofRegion (unpackBody_typed (boundCase_typed hl hr)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RetainedCase.routeCase_ofRegion
    hl hr

end Quotient

section Transport

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (caseWithContext extend)

universe u₁ v₁

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  (J : V ⥤ Paper.TypeCategory (τ := τ) Φ) (M : TypeModel τ V)
  (objIso : ∀ T : τ, J.obj (M.obj T) ≅ Paper.TypeCategory.ofType (Φ := Φ) T)
  {Y Z : τ}

variable [SymmetricCategory V]
  [PremonoidalCategory (Paper.TypeCategory (τ := τ) Φ)]
  [SymmetricPremonoidalCategory (Paper.TypeCategory (τ := τ) Φ)]
  [HasFiniteCoproducts (Paper.TypeCategory (τ := τ) Φ)]
  [DistributiveTensor V] [DistributivePremonoidalCategory (Paper.TypeCategory (τ := τ) Φ)]
  [DistributiveFreydCategory J]

/-- The literal case comparison in a Paper quotient model reduces to the
retained scrutinee, the packed arms and the explicit distributor square. -/
theorem literal_case_transport
    (ha : Tm.HasType [X] a (Silmaril.coprod A B))
    (hl : ValueBranches [A, X] l [D]) (hr : ValueBranches [B, X] r [D])
    (f : J.obj (M.obj X) ⟶ J.obj (M.obj (Silmaril.coprod A B)))
    (g : J.obj (M.obj (Silmaril.product X A)) ⟶ J.obj (M.obj D))
    (h : J.obj (M.obj (Silmaril.product X B)) ⟶ J.obj (M.obj D))
    (hRetained : reindexHom J M objIso
      (extend J f ≫ J.map (M.productIso X (Silmaril.coprod A B)).inv) =
      Paper.TypeCategory.ofRegion (τ := τ) (diagonal_typed X) ≫
        Paper.TypeCategory.whiskerLeft (τ := τ) (Paper.TypeCategory.ofType (Φ := Φ) X)
          (Paper.TypeCategory.ofRegion (τ := τ) (returnSum_typed ha)))
    (hDistributor : reindexHom J M objIso (J.map (CfgEta.TypeCategory.Retained.packedDistributor M X A B)) =
      Paper.TypeCategory.ofRegion (τ := τ) (distributorRegion_typed X A B))
    (hArms : reindexHom J M objIso (CfgEta.TypeCategory.Retained.packedCopair J M g h) =
      Paper.TypeCategory.ofRegion (τ := τ) (packedArms_typed hl hr)) :
    reindexHom J M objIso (caseWithContext J (f ≫ J.map (M.coprodIso A B).hom)
      (J.map (M.productIso X A).inv ≫ g) (J.map (M.productIso X B).inv ≫ h)) =
        Paper.TypeCategory.ofRegion (.case ha hl hr) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RetainedCase.literal_case_transport
    J M objIso ha hl hr f g h hRetained hDistributor hArms

end Transport

end Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedCase

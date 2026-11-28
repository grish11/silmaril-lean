module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedLet.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Retained.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Iteration.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Tensor.Thms

/-! # Representatives of a retained-context case -/

@[expose] public section

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CfgEta.TypeCategory
open CfgEta.TypeCategory.Retained (distributorRegion distributorRegion_typed)
open Paper.RetainedLet (returnOnce returnOnce_typed diagonal diagonal_typed unpackBody unpackBody_typed)
open Silmaril.DeBruijn (lift)

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedCase

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {X A B D : τ} {a : Tm Φ} {l r : Region Φ}

/-- Case on the newly bound sum, preserving the original environment in its arms. -/
def boundCase (l r : Region Φ) : Region Φ :=
  .case (.var 0) (l.renameVars (lift Nat.succ)) (r.renameVars (lift Nat.succ))

theorem boundCase_typed {Γ : VCtx τ} {L : LCtx τ}
    (hl : ValueBranches (A :: Γ) l L) (hr : ValueBranches (B :: Γ) r L) :
    ValueBranches (Silmaril.coprod A B :: Γ) (boundCase l r) L :=
  .case (.var (i := 0) rfl)
    (hl.renameVars ((Ren.wk Γ (Silmaril.coprod A B)).lift A))
    (hr.renameVars ((Ren.wk Γ (Silmaril.coprod A B)).lift B))

theorem boundCase_hasType {Γ : VCtx τ} {L : LCtx τ}
    (hl : HasType (A :: Γ) l L) (hr : HasType (B :: Γ) r L) :
    HasType (Silmaril.coprod A B :: Γ) (boundCase l r) L :=
  .case (.var (i := 0) rfl)
    (hl.renameVars ((Ren.wk Γ (Silmaril.coprod A B)).lift A))
    (hr.renameVars ((Ren.wk Γ (Silmaril.coprod A B)).lift B))

/-- A case on the tagged pair, dispatching to arms expecting their packed input. -/
def packedArms (l r : Region Φ) : Region Φ :=
  boundCase (unpackBody l) (unpackBody r)

theorem packedArms_typed (hl : ValueBranches [A, X] l [D]) (hr : ValueBranches [B, X] r [D]) :
    ValueBranches [Silmaril.coprod (Silmaril.product X A) (Silmaril.product X B)] (packedArms l r) [D] :=
  caseValueBranches (unpackBody_typed hl) (unpackBody_typed hr)

/-- Compose redistribution of the retained input with the packed arms. -/
def routeCase (l r : Region Φ) : Region Φ :=
  compLSubst (fun _ => distributorRegion) (fun _ => packedArms l r) 0

theorem routeCase_typed (hl : ValueBranches [A, X] l [D]) (hr : ValueBranches [B, X] r [D]) :
    ValueBranches [Silmaril.product X (Silmaril.coprod A B)] (routeCase l r) [D] :=
  seqValueBranches (distributorRegion_typed X A B) (packedArms_typed hl hr)

/-- Retain the input through the scrutinee, then route to a packed arm. -/
def assembleCase (p l r : Region Φ) : Region Φ :=
  compLSubst
    (compLSubst
      (compLSubst (fun _ => diagonal) (fun _ => whiskerLeftRegion p))
      (fun _ => distributorRegion))
    (fun _ => packedArms l r) 0

theorem assembleCase_typed {p : Region Φ} (hp : ValueBranches [X] p [Silmaril.coprod A B])
    (hl : ValueBranches [A, X] l [D]) (hr : ValueBranches [B, X] r [D]) :
    ValueBranches [X] (assembleCase p l r) [D] :=
  seqValueBranches
    (seqValueBranches
      (seqValueBranches (diagonal_typed X) (whiskerLeftRegion_typed X hp))
      (distributorRegion_typed X A B))
    (packedArms_typed hl hr)

/-- Evaluate the scrutinee once and forward its selected tag and payload. -/
def returnSum (a : Tm Φ) : Region Φ :=
  .case a (.br 0 (.inl (.var 0))) (.br 0 (.inr (.var 0)))

theorem returnSum_typed (ha : Tm.HasType [X] a (Silmaril.coprod A B)) :
    ValueBranches [X] (returnSum a) [Silmaril.coprod A B] :=
  .case ha (.br rfl (.inl (.var (i := 0) rfl))) (.br rfl (.inr (.var (i := 0) rfl)))

section Quotient

open CategoryTheory

/-- The singleton computation assembled from an arbitrary represented scrutinee. -/
def assembledCaseArrow {p : Region Φ} (hp : ValueBranches [X] p [Silmaril.coprod A B])
    (hl : ValueBranches [A, X] l [D]) (hr : ValueBranches [B, X] r [D]) :
    Paper.TypeCategory.ofType (Φ := Φ) X ⟶ Paper.TypeCategory.ofType D :=
  let f := Paper.TypeCategory.ofRegion (τ := τ) hp
  ((Paper.TypeCategory.ofRegion (τ := τ) (diagonal_typed X) ≫
    Paper.TypeCategory.whiskerLeft (τ := τ) (Paper.TypeCategory.ofType (Φ := Φ) X) f) ≫
    Paper.TypeCategory.ofRegion (τ := τ) (distributorRegion_typed X A B)) ≫
    Paper.TypeCategory.ofRegion (τ := τ) (packedArms_typed hl hr)

end Quotient

section Transport

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel)

universe u₁ v₁

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  (J : V ⥤ Paper.TypeCategory (τ := τ) Φ) (M : TypeModel τ V)
  (objIso : ∀ T : τ, J.obj (M.obj T) ≅ Paper.TypeCategory.ofType (Φ := Φ) T)
  {Y Z : τ}

/-- Reindex the interpreted type objects at the singleton paper interfaces. -/
def reindexHom (f : J.obj (M.obj Y) ⟶ J.obj (M.obj Z)) :
    Paper.TypeCategory.ofType (Φ := Φ) Y ⟶ Paper.TypeCategory.ofType Z :=
  (objIso Y).inv ≫ f ≫ (objIso Z).hom

end Transport

end Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedCase

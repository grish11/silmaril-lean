module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Generation.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseAndUnaryReturns.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.BinaryLet.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedCase.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Coproducts.Finite.Thms

/-! # Generation certificates at the exact guarded singleton interface -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory
open CfgEta.TypeCategory (returnRegion_typed seqValueBranches caseValueBranches
  whiskerLeftRegion_typed whiskerRightRegion_typed productFstBranches productSndBranches)
open Paper.RetainedLet (returnOnce_typed unpackBody_typed)
open Paper.SingletonReification.BinaryLet (applyPackedPair_typed returnPair_typed)
open Paper.RetainedCase (returnSum_typed)
open Paper.Extension.Singleton (ofRegion ofType productSnd emptyIsInitial)
open Paper.Extension.Singleton.ValueCoproducts (exactCopair)
open CfgEta.TypeCategory.Retained (distributorRegion_typed)
open Paper.Extension.Singleton.Generation (Generated)

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

set_option hygiene false in
local notation "T" => Step (τ := τ) (Φ := Φ) pe

/-- The producers and bodies keep their actual guarded representatives.
The packed bodies supply a captured region with its exact input product.
Positive-arity feedback uses the exact-sum loop representative. -/
inductive GuardedFragment : {X D : τ} → {r : Region Φ} → ValueBranches [X] r [D] → Prop where
  | initial {D : τ} {r : Region Φ} (hr : ValueBranches [Silmaril.empty] r [D]) : GuardedFragment hr
  | branch {X D : τ} {a : Tm Φ} (ha : Tm.BranchValue [X] a D) :
      GuardedFragment (.br (ℓ := 0) rfl ha)
  | returned {X D : τ} {a : Tm Φ} {ha : Tm.HasType [X] a D} :
      Paper.WithCaseAndUnaryReturns.ReturnFragment pe ha → GuardedFragment (returnRegion_typed ha)
  | fst (A B : τ) : GuardedFragment (productFstBranches A B)
  | snd (A B : τ) : GuardedFragment (productSndBranches A B)
  | seq {X A D : τ} {r s : Region Φ} {hr : ValueBranches [X] r [A]} {hs : ValueBranches [A] s [D]} :
      GuardedFragment hr → GuardedFragment hs → GuardedFragment (seqValueBranches hr hs)
  | left (X : τ) {A D : τ} {r : Region Φ} {hr : ValueBranches [A] r [D]} :
      GuardedFragment hr → GuardedFragment (whiskerLeftRegion_typed X hr)
  | right (X : τ) {A D : τ} {r : Region Φ} {hr : ValueBranches [A] r [D]} :
      GuardedFragment hr → GuardedFragment (whiskerRightRegion_typed X hr)
  | let₁ {X A D : τ} {a : Tm Φ} {r : Region Φ} {ha : Tm.HasType [X] a A}
      {hr : ValueBranches [A, X] r [D]} :
      GuardedFragment (returnOnce_typed ha) → GuardedFragment (unpackBody_typed hr) →
      GuardedFragment (.let₁ ha hr)
  | let₂ {X A B D : τ} {a : Tm Φ} {p : Region Φ} {ha : Tm.HasType [X] a (product A B)}
      {hp : ValueBranches [product X (product A B)] p [D]} :
      GuardedFragment (returnPair_typed ha) → GuardedFragment hp →
      GuardedFragment (.let₂ ha (applyPackedPair_typed hp))
  | caseInput {A B D : τ} {l r : Region Φ} {hl : ValueBranches [A] l [D]}
      {hr : ValueBranches [B] r [D]} :
      GuardedFragment hl → GuardedFragment hr → GuardedFragment (caseValueBranches hl hr)
  | caseRetained {X A B D : τ} {a : Tm Φ} {l r : Region Φ}
      {ha : Tm.HasType [X] a (coprod A B)}
      {hl : ValueBranches [A, X] l [D]} {hr : ValueBranches [B, X] r [D]} :
      GuardedFragment (returnSum_typed ha) →
      GuardedFragment (unpackBody_typed hl) → GuardedFragment (unpackBody_typed hr) →
      GuardedFragment (.case ha hl hr)
  | cfgZero {X D : τ} {e : Region Φ} {he : ValueBranches [X] e [D]} (blocks : Fin 0 → Region Φ) :
      GuardedFragment he →
      GuardedFragment (.cfg Fin.elim0 he (fun i => i.elim0) : ValueBranches [X] (.cfg e 0 blocks) [D])
  | iterate {X D : τ} {r : Region Φ} {hr : ValueBranches [X] r [coprod D X]} :
      GuardedFragment hr → GuardedFragment (SyntacticCategory.iterateRegion_valueBranches hr)
  | eqv {X D : τ} {r s : Region Φ} {hr : ValueBranches [X] r [D]} {hs : ValueBranches [X] s [D]} :
      Eqv pe [X] r s [D] → GuardedFragment hr → GuardedFragment hs

/-- The one-result scrutinee generated as a term return must still agree
with the literal single binder used by the retained unary-region rule. -/
@[expose] def OnceReturnAgreement : Prop :=
  ∀ {X A : τ} {a : Tm Φ} (ha : Tm.HasType [X] a A),
    ofRegion T (returnRegion_typed ha) = ofRegion T (returnOnce_typed ha)

set_option hygiene false in
local notation "Obj" => ofType T

/-- Assemble the generated local rows in their label-list order. The
distributor gives each row the same captured input and its own payload. -/
@[expose] noncomputable def capturedDispatcher (X : τ) {D : τ} :
    (L : LCtx τ) → (∀ i : Fin L.length, Obj (product X (L.get i)) ⟶ Obj D) →
      (Obj (product X (packedExitType L)) ⟶ Obj D)
  | [], _ => productSnd T X Silmaril.empty ≫ (emptyIsInitial T).to (Obj D)
  | A :: L, rows =>
    ofRegion T (distributorRegion_typed X A (packedExitType L)) ≫
      exactCopair T (rows 0) (capturedDispatcher X L (fun i => rows i.succ))

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling

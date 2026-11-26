module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.PackedBody.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedLet.Generation.PackedTerm.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseAndUnaryReturns.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.ReturnFusion.Thms

/-! # Packed return bodies in the unary-forwarding extension -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RetainedLetGeneration

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.RetainedLet (returnOnce returnOnce_typed unpackBody unpackBody_typed diagonal_typed)
open Paper.PackedBody (applyPacked applyPackedTerm applyPackedTerm_typed unpack_applyPacked)
open Paper.Extension.Singleton (diagonalArrow ofRegion ofRegion_eq_iff ofType whiskerLeftFunctor)
open CfgEta.TypeCategory (returnRegion returnRegion_typed returnRegion_rename seqValueBranches)
open Silmaril.DeBruijn (lift)
open CategoryTheory

universe u v w

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)
  (includeUnary : ∀ {Γ : VCtx τ} {r s : Region Φ} {L : LCtx τ},
    Paper.UnaryReturn.Step Γ r s L → Seed Γ r s L)
  {X A D : τ} {c : Tm Φ}

section Syntax

set_option hygiene false in
local notation "Lit" => ofRegion Seed

set_option hygiene false in
local notation "P" => Paper.Extension.Singleton.projection Seed

set_option backward.isDefEq.respectTransparency false in
include includeUnary in
theorem literalLet_eq_copy_whisker_unpack {r : Region Φ} {a : Tm Φ} (ha : Tm.HasType [X] a A)
    (hr : ValueBranches [A, X] r [D]) :
    Lit (.let₁ ha hr) =
      (diagonalArrow Seed (ofType Seed X) ≫ (whiskerLeftFunctor Seed (ofType Seed X)).map
        (Lit (returnRegion_typed ha))) ≫ Lit (unpackBody_typed hr) := by
  have h : Lit (returnRegion_typed ha) = Lit (returnOnce_typed ha) :=
    (ofRegion_eq_iff Seed _ _).2 (Paper.UnaryReturn.returnRegion_eq_returnOnce (includeUnary) ha)
  let diag := diagonal_typed (Φ := Φ) X
  let scrutinee := returnOnce_typed ha
  let retained := CfgEta.TypeCategory.whiskerLeftRegion_typed X scrutinee
  let pack := unpackBody_typed hr
  let sequenced := seqValueBranches diag retained
  let body := seqValueBranches sequenced pack
  have eq : Lit body = Lit (.let₁ ha hr) :=
    (ofRegion_eq_iff Seed body (.let₁ ha hr)).2 (.paper (Paper.RetainedLet.literal_let ha hr.hasType))
  rw [← eq, h]
  change (P).map (Paper.TypeCategory.ofRegion body) = _
  rw [← Paper.TypeCategory.ofRegion_comp sequenced pack body,
    ← Paper.TypeCategory.ofRegion_comp diag retained sequenced,
    ← Paper.TypeCategory.whiskerLeft_ofRegion X scrutinee, (P).map_comp, (P).map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
include includeUnary in
theorem unpack_return_applyPackedTerm (hc : Tm.HasType [product X A] c D) :
    ofRegion Seed (unpackBody_typed (returnRegion_typed (applyPackedTerm_typed hc))) =
      ofRegion Seed (returnRegion_typed hc) := by
  apply (ofRegion_eq_iff Seed _ _).2
  let decode := ((Ren.wk ([] : VCtx τ) (product X A)).lift X).lift A
  have opened := Paper.UnaryReturn.returnRegion_eq_returnOnce includeUnary (applyPackedTerm_typed hc)
  have throughUnpack : Paper.Extension.Eqv Seed [product X A]
      (unpackBody (returnRegion (applyPackedTerm c))) (unpackBody (applyPacked (returnOnce c))) [D] :=
    .let₂ (.var (i := 0) rfl) (opened.renameVars decode)
  exact throughUnpack.trans ((Paper.Extension.Eqv.paper (unpack_applyPacked (returnOnce_typed hc))).trans
    (Paper.UnaryReturn.returnRegion_eq_returnOnce includeUnary hc).symm)

end Syntax

section Denotation

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (duplicate)

universe u₁ u₂ v₁ v₂

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J] (M : TypeModel τ V)
  [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

set_option backward.isDefEq.respectTransparency false in
theorem unpack_return_let₂_denotation
    (copyCentral : ∀ E : V, PremonoidalCategory.IsCentral (J.map (duplicate E) ≫
      (Functor.StrongPremonoidal.tensorIso (J := J) E E).inv))
    {X A D : τ} {b : Tm Φ} (hb : Tm.HasType [A, X] b D) :
    denoteRegion J M (unpackBody_typed (returnRegion_typed hb)).hasType =
      denoteRegion J M (returnRegion_typed (.let₂ (.var (i := 0) rfl)
        (hb.rename (((Ren.wk [] (product X A)).lift X).lift A)))).hasType := by
  let ren := ((Ren.wk ([] : VCtx τ) (product X A)).lift X).lift A
  let hp : Tm.HasType [product X A] (.var 0 : Tm Φ) (product X A) := .var rfl
  have shape : unpackBody (returnRegion b) =
      .let₂ (.var 0) (returnRegion (b.rename (lift (lift Nat.succ)))) :=
    congrArg (Region.let₂ (.var 0)) (returnRegion_rename b _).symm
  have same {r s : Region Φ} (eq : r = s) (hr : HasType [product X A] r [D]) (hs : HasType [product X A] s [D]) :
      denoteRegion J M hr = denoteRegion J M hs := by
    subst s
    rfl
  exact (same shape _ (.let₂ hp (returnRegion_typed (hb.rename ren)).hasType)).trans
    (denote_let₂_returnRegion_fusion J M copyCentral hp (hb.rename ren))

end Denotation

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RetainedLetGeneration

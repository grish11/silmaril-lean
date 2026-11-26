module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.PackedBody.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedLet.Generation.PackedTerm.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseAndUnaryReturns.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RetainedLetGeneration

/-! # Generating retained unary returns from packed bodies -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedLet

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory
open Paper.PackedBody (applyPackedTerm_typed)
open CfgEta.TypeCategory (returnRegion_typed)
open Paper.Extension.Singleton (diagonalArrow ofRegion ofType whiskerLeftFunctor)
open Paper.Extension.Singleton.Generation (Generated)

universe u v w

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)
  (includeUnary : ∀ {Γ : VCtx τ} {r s : Region Φ} {L : LCtx τ},
    UnaryReturn.Step Γ r s L → Seed Γ r s L)
  {X A D : τ} {a b c : Tm Φ}

set_option hygiene false in
local notation "Lit" => ofRegion Seed

include includeUnary in
/-- Opening a returning packed term with the two variables and then decoding
the input gives the original arrow. Unary forwarding handles lowered lets
inside the body, and guarded product η handles the constructor pair. -/
theorem unpack_return_applyPackedTerm (hc : Tm.HasType [product X A] c D) :
    Lit (unpackBody_typed (returnRegion_typed (applyPackedTerm_typed hc))) =
      Lit (returnRegion_typed hc) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RetainedLetGeneration.unpack_return_applyPackedTerm Seed
    includeUnary hc

variable {ε : Type w} [HasEff Φ ε] (pe : ε)
  (contains : ∀ {Γ : VCtx τ} {r s : Region Φ} {L : LCtx τ},
    WithCaseAndUnaryReturns.Step pe Γ r s L → Seed Γ r s L)

include contains in
/-- The retaining binder copies only its input and computes its scrutinee once.
Its final arrow sees the original input on the left and the bound result on the right. -/
theorem returnLet_eq_copy_whisker_unpack (ha : Tm.HasType [X] a A) (hb : Tm.HasType [A, X] b D) :
    Lit (returnRegion_typed (.let₁ ha hb)) =
      (diagonalArrow Seed (ofType Seed X) ≫ (whiskerLeftFunctor Seed (ofType Seed X)).map
        (Lit (returnRegion_typed ha))) ≫ Lit (unpackBody_typed (returnRegion_typed hb)) :=
  (WithCaseAndUnaryReturns.returnLet_eq_let pe Seed contains ha hb).trans
    (Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RetainedLetGeneration.literalLet_eq_copy_whisker_unpack
      Seed (fun step => contains (.inl step)) ha (returnRegion_typed hb))

include contains in
/-- A packed body can use both fields of the retained product. -/
theorem returnLet_eq_copy_whisker_return (ha : Tm.HasType [X] a A) (hc : Tm.HasType [product X A] c D) :
    Lit (returnRegion_typed (.let₁ ha (applyPackedTerm_typed hc))) =
      (diagonalArrow Seed (ofType Seed X) ≫ (whiskerLeftFunctor Seed (ofType Seed X)).map
        (Lit (returnRegion_typed ha))) ≫ Lit (returnRegion_typed hc) :=
  (returnLet_eq_copy_whisker_unpack Seed pe contains ha (applyPackedTerm_typed hc)).trans
    (congrArg ((diagonalArrow Seed (ofType Seed X) ≫ (whiskerLeftFunctor Seed (ofType Seed X)).map
      (Lit (returnRegion_typed ha))) ≫ ·)
      (unpack_return_applyPackedTerm Seed (fun step => contains (.inl step)) hc))

include contains in
/-- Generation of the scrutinee and the packed term gives generation of
the unary return with the two inputs supplied to its body. -/
theorem generated_packed_returnLet (ha : Tm.HasType [X] a A) (hc : Tm.HasType [product X A] c D)
    (ga : Generated Seed (Lit (returnRegion_typed ha))) (gc : Generated Seed (Lit (returnRegion_typed hc))) :
    Generated Seed (Lit (returnRegion_typed (.let₁ ha (applyPackedTerm_typed hc)))) :=
  (returnLet_eq_copy_whisker_return Seed pe contains ha hc).symm ▸ .comp (.comp (.copy X) (.left X ga)) gc

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

/-- Decoding an arbitrary returned body as a region binder or as a returning
term binder gives the same denotation. -/
theorem unpack_return_let₂_denotation
    (copyCentral : ∀ E : V, PremonoidalCategory.IsCentral (J.map (duplicate E) ≫
      (Functor.StrongPremonoidal.tensorIso (J := J) E E).inv))
    {X A D : τ} {b : Tm Φ} (hb : Tm.HasType [A, X] b D) :
    denoteRegion J M (unpackBody_typed (returnRegion_typed hb)).hasType =
      denoteRegion J M (returnRegion_typed (.let₂ (.var (i := 0) rfl)
        (hb.rename (((Ren.wk [] (product X A)).lift X).lift A)))).hasType :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RetainedLetGeneration.unpack_return_let₂_denotation J M copyCentral hb

end Denotation

end Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedLet

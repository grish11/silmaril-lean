module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.SumCase.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Family.Substitution.Thms

/-! # Recursively selected sum cases and typed outward leaves -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.Intrinsic

open Silmaril Silmaril.Isotope.LambdaSSA
open Semantics.Categorical
open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (caseWithContext)
open scoped MonoidalCategory

universe u v m n x y

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- The chosen sum injection at a selected outward return. -/
inductive ExitTag : τ → τ → Type u where
  | inl (A B : τ) : ExitTag A (coprod A B)
  | inr (A B : τ) : ExitTag B (coprod A B)

/-- A finite selected case tree. A recursive arm keeps the incoming context
together with its new payload. Leaves return an intrinsic program or tag a term result. -/
inductive CaseTree (Φ : Type v) [HasTy Φ τ] : τ → LCtx τ → Type (max u v) where
  | exit {X D : τ} {L : LCtx τ} (slot : Nat) : At L slot D → Program Φ X D → CaseTree Φ X L
  | taggedExit {X A D : τ} {L : LCtx τ} (slot : Nat) : At L slot D →
      ExitTag A D → Term Φ X A → CaseTree Φ X L
  | case {X : τ} {L : LCtx τ} (A B : τ) : Term Φ X (coprod A B) →
      CaseTree Φ (product X A) L → CaseTree Φ (product X B) L → CaseTree Φ X L

/-- Supplying the input and payload preserves guarded branches at every outward label. -/
theorem applyPacked_typed_exits {X A : τ} {L : LCtx τ} {r : Region Φ}
    (h : ValueBranches [product X A] r L) : ValueBranches [A, X] (PackedBody.applyPacked r) L :=
  h.substVars (fun {i _} hi => match i with
    | 0 => Option.some.inj hi ▸ .pair (.var (i := 1) rfl) (.var (i := 0) rfl)
    | _ + 1 => by simp [At] at hi)

/-- Elaborate every node to a native case. Substitute the retained context
and payload into each recursive arm, and retarget each leaf's singleton exit. -/
def CaseTree.elaborate {X : τ} {L : LCtx τ} : CaseTree Φ X L → {r : Region Φ // ValueBranches [X] r L}
  | .exit slot h body =>
      ⟨body.elaborate.val.renameLabels (fun _ => slot), by
        rw [renameLabels_eq_lsubst]
        exact body.elaborate.property.lsubst
          (fun _ _ hi => .br (singletonExitRen h hi) (.var (i := 0) rfl))⟩
  | .taggedExit _ h (.inl _ _) a =>
      ⟨_, .let₁ a.elaborate.property (.br h (.inl (.var (i := 0) rfl)))⟩
  | .taggedExit _ h (.inr _ _) a =>
      ⟨_, .let₁ a.elaborate.property (.br h (.inr (.var (i := 0) rfl)))⟩
  | .case _ _ a left right =>
      ⟨_, .case a.elaborate.property
        (applyPacked_typed_exits left.elaborate.property) (applyPacked_typed_exits right.elaborate.property)⟩

/-- The one-case presentation gives a tree with two leaves. -/
def SumCase.toTree {X : τ} {L : LCtx τ} (p : SumCase Φ X L) : CaseTree Φ X L :=
  .case p.leftType p.rightType p.discriminator
    (.exit p.onLeft.exit p.onLeft.atExit p.onLeft.body)
    (.exit p.onRight.exit p.onRight.atExit p.onRight.body)

variable {V : Type m} {C : Type n} [Category.{x} V] [Category.{y} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C) [DistributiveFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]

/-- Interpret the selected injection using the model's sum comparison. -/
noncomputable def ExitTag.valueMap {A D : τ} : ExitTag A D → (M.obj A ⟶ M.obj D)
  | .inl A B => coprod.inl ≫ (M.coprodIso A B).inv
  | .inr A B => coprod.inr ≫ (M.coprodIso A B).inv

/-- Fold the selected tree into contextual cases, packing the input and
payload at each edge and using the recorded label injection at each leaf. -/
noncomputable def CaseTree.targetArrow {X : τ} {L : LCtx τ} :
    CaseTree Φ X L → (J.obj (M.obj X) ⟶ J.obj (labelObj M L))
  | .exit slot h body => body.targetArrow J M ≫ J.map (labelInject M slot h)
  | .taggedExit slot h tag body =>
      body.targetArrow J M ≫ J.map (tag.valueMap M ≫ labelInject M slot h)
  | .case A B a left right =>
      caseWithContext J (a.targetArrow J M ≫ J.map (M.coprodIso A B).hom)
        (J.map (M.productIso X A).inv ≫ left.targetArrow)
        (J.map (M.productIso X B).inv ≫ right.targetArrow)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.Intrinsic

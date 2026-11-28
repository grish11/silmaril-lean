module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Outward.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Values.Thms
public import Silmaril.Semantics.Categories.Freyd.CentralUnit.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ReturnFusion

/-! # Denotational fusion for exactly typed λSSA returns -/

public section

universe u v u₁ v₁ u₂ v₂

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (duplicate)
open Region.CfgEta.TypeCategory (returnRegion_typed)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J]
  {τ : Type u} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type v} [HasTy Φ τ] [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

/-- A returned binary-let expression has the denotation of a region binder followed by a return. -/
theorem denote_let₂_boundReturn_fusion {Γ : VCtx τ} {L : LCtx τ} {i : Nat}
    {A B D : τ} {a b : Tm Φ} (hi : At L i D)
    (ha : Tm.HasType Γ a (product A B)) (hb : Tm.HasType (B :: A :: Γ) b D) :
    denoteRegion J M (.let₂ ha (.let₁ hb (.br hi (.var (i := 0) rfl)))) =
      denoteRegion J M (.let₁ (.let₂ ha hb) (.br hi (.var (i := 0) rfl))) :=
  ReturnFusion.denote_let₂_boundReturn_fusion J M hi ha hb

/-- Returning the selected case body has the same denotation as returning the term-level case. -/
theorem denote_case_boundReturn_fusion {Γ : VCtx τ} {L : LCtx τ} {i : Nat}
    {A B D : τ} {e l r : Tm Φ} (hi : At L i D)
    (he : Tm.HasType Γ e (coprod A B)) (hl : Tm.HasType (A :: Γ) l D)
    (hr : Tm.HasType (B :: Γ) r D) :
    denoteRegion J M (.case he (.let₁ hl (.br hi (.var (i := 0) rfl)))
      (.let₁ hr (.br hi (.var (i := 0) rfl)))) =
        denoteRegion J M (.let₁ (.case he hl hr) (.br hi (.var (i := 0) rfl))) :=
  ReturnFusion.denote_case_boundReturn_fusion J M hi he hl hr

/-- A returned pair evaluates the left expression and then the right in the original context. -/
theorem denote_pair_boundReturn_sequencing {Γ : VCtx τ} {L : LCtx τ} {i : Nat}
    {A B : τ} {a b : Tm Φ} (hi : At L i (product A B))
    (ha : Tm.HasType Γ a A) (hb : Tm.HasType Γ b B) :
    denoteRegion J M (.let₁ (.pair ha hb) (.br hi (.var (i := 0) rfl))) =
      denoteRegion J M (.let₁ ha (.let₁ (hb.rename (Ren.wk Γ A))
        (.br hi (.pair (.var (i := 1) rfl) (.var (i := 0) rfl))))) :=
  ReturnFusion.denote_pair_boundReturn_sequencing J M hi ha hb

/-- Evaluate the payload once before injecting it into the left summand at the same exit. -/
theorem denote_inl_boundReturn_sequencing {Γ : VCtx τ} {L : LCtx τ} {i : Nat}
    {A B : τ} {a : Tm Φ} (hi : At L i (coprod A B)) (ha : Tm.HasType Γ a A) :
    denoteRegion J M (.let₁ (.inl ha) (.br hi (.var (i := 0) rfl))) =
      denoteRegion J M (.let₁ ha (.br hi (.inl (.var (i := 0) rfl)))) :=
  ReturnFusion.denote_inl_boundReturn_sequencing J M hi ha

/-- Evaluate the payload once before injecting it into the right summand at the same exit. -/
theorem denote_inr_boundReturn_sequencing {Γ : VCtx τ} {L : LCtx τ} {i : Nat}
    {A B : τ} {a : Tm Φ} (hi : At L i (coprod A B)) (ha : Tm.HasType Γ a B) :
    denoteRegion J M (.let₁ (.inr ha) (.br hi (.var (i := 0) rfl))) =
      denoteRegion J M (.let₁ ha (.br hi (.inr (.var (i := 0) rfl)))) :=
  ReturnFusion.denote_inr_boundReturn_sequencing J M hi ha

/-- Evaluate the empty-typed operand once before applying the pure empty
eliminator at the supplied exit interface. -/
theorem denote_abort_boundReturn_sequencing {Γ : VCtx τ} {L : LCtx τ} {i : Nat}
    {D : τ} {a : Tm Φ} (hi : At L i D) (ha : Tm.HasType Γ a empty) :
    denoteRegion J M (.let₁ (.abort ha) (.br hi (.var (i := 0) rfl))) =
      denoteRegion J M (.let₁ ha (.let₁ (.abort (.var (i := 0) rfl)) (.br hi (.var (i := 0) rfl)))) :=
  ReturnFusion.denote_abort_boundReturn_sequencing J M hi ha

/-- Return lowering by singleton label substitution agrees with evaluating the expression once. -/
theorem denote_returnRegion_boundReturn
    (copyCentral : ∀ E : V, PremonoidalCategory.IsCentral (J.map (duplicate E) ≫
      (Functor.StrongPremonoidal.tensorIso (J := J) E E).inv))
    {Γ : VCtx τ} {D : τ} {a : Tm Φ} (ht : Tm.HasType Γ a D) :
    denoteRegion J M (returnRegion_typed ht).hasType =
      denoteRegion J M (.let₁ ht (.br (L := [D]) (ℓ := 0) rfl (.var (i := 0) rfl))) :=
  ReturnFusion.denote_returnRegion_boundReturn J M copyCentral ht

/-- A primitive consumes the value computed by its operand. An explicit unary
binder followed by applying the primitive to the new variable has the same
denotation, including when computing the operand has effects. -/
theorem denote_op_boundReturn_sequencing {Γ : VCtx τ} {L : LCtx τ} {i : Nat}
    {a : Tm Φ} (p : Φ) (hi : At L i (instrTrg p)) (ha : Tm.HasType Γ a (instrSrc p)) :
    denoteRegion J M (.let₁ (.op ha) (.br hi (.var (i := 0) rfl))) =
      denoteRegion J M (.let₁ (.let₁ ha (.op (f := p) (.var (i := 0) rfl))) (.br hi (.var (i := 0) rfl))) :=
  ReturnFusion.denote_op_boundReturn_sequencing J M p hi ha

section LoweredReturns

variable (copyCentral : ∀ E : V, PremonoidalCategory.IsCentral (J.map (duplicate E) ≫
    (Functor.StrongPremonoidal.tensorIso (J := J) E E).inv))

include copyCentral

/-- Semantic soundness of sequencing a computed primitive argument in the
ordinary lowered return syntax. -/
theorem denote_op_returnRegion_sequencing {Γ : VCtx τ} {a : Tm Φ}
    (p : Φ) (ha : Tm.HasType Γ a (instrSrc p)) :
    denoteRegion J M (returnRegion_typed (.op ha)).hasType =
      denoteRegion J M (returnRegion_typed (.let₁ ha (.op (f := p) (.var (i := 0) rfl)))).hasType :=
  (denote_returnRegion_boundReturn J M copyCentral (.op ha)).trans
    ((denote_op_boundReturn_sequencing J M p (i := 0) (L := [instrTrg p]) rfl ha).trans
      (denote_returnRegion_boundReturn J M copyCentral (.let₁ ha (.op (f := p) (.var (i := 0) rfl)))).symm)

/-- Binary-let return fusion for the existing return lowering, including nested expression lets. -/
theorem denote_let₂_returnRegion_fusion {Γ : VCtx τ} {A B D : τ} {a b : Tm Φ}
    (ha : Tm.HasType Γ a (product A B)) (hb : Tm.HasType (B :: A :: Γ) b D) :
    denoteRegion J M (.let₂ ha (returnRegion_typed hb).hasType) =
      denoteRegion J M (returnRegion_typed (.let₂ ha hb)).hasType :=
  ReturnFusion.denote_let₂_returnRegion_fusion J M copyCentral ha hb

/-- Case return fusion for the existing return lowering, including nested expression lets. -/
theorem denote_case_returnRegion_fusion {Γ : VCtx τ} {A B D : τ} {a l r : Tm Φ}
    (ha : Tm.HasType Γ a (coprod A B))
    (hl : Tm.HasType (A :: Γ) l D) (hr : Tm.HasType (B :: Γ) r D) :
    denoteRegion J M (.case ha (returnRegion_typed hl).hasType (returnRegion_typed hr).hasType) =
      denoteRegion J M (returnRegion_typed (.case ha hl hr)).hasType :=
  ReturnFusion.denote_case_returnRegion_fusion J M copyCentral ha hl hr

end LoweredReturns

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical

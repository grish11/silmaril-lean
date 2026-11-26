module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProductDestructureReturns.Generation.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Generation.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturns.Defs

/-! # Intrinsically typed product returns in the guarded singleton category -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.Intrinsic

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory
open CfgEta.TypeCategory (returnRegion_typed)
open Paper.PackedBody (applyPackedTerm_typed)
open Paper.RetainedLet (unpackTerm_typed)
open Paper.SingletonReification.BinaryLet (applyPackedPair_typed)
open Paper.Extension.Singleton (ofType ofRegion pairArrows discardArrow productFst productSnd
  diagonalArrow whiskerLeftFunctor)
open Paper.Extension.Singleton.Generation (primitive)

universe u v w

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- A Type-valued fragment of returned terms with a single input. Product
constructors retain both operand result types. Destructuring records the two
factor types and supplies the body with their packed record. -/
inductive Term (Φ : Type v) [HasTy Φ τ] : τ → τ → Type (max u v) where
  | input {X : τ} : Term Φ X X
  | unit {X : τ} : Term Φ X Silmaril.unit
  | call {X : τ} (p : Φ) : Term Φ X (instrSrc p) → Term Φ X (instrTrg p)
  | pair {X A B : τ} : Term Φ X A → Term Φ X B → Term Φ X (product A B)
  | seq {X A D : τ} : Term Φ X A → Term Φ A D → Term Φ X D
  | fst (A B : τ) : Term Φ (product A B) A
  | snd (A B : τ) : Term Φ (product A B) B
  | destructure (A B : τ) {D : τ} :
      Term Φ (product A B) D → Term Φ (product A B) D

/-- Elaborate the selected term with its exact singleton typing. -/
def Term.elaborate {X D : τ} : Term Φ X D → {t : Tm Φ // Tm.HasType [X] t D}
  | .input => ⟨_, .var (i := 0) rfl⟩
  | .unit => ⟨_, .unit⟩
  | .call p a => ⟨_, .op (f := p) a.elaborate.property⟩
  | .pair a b => ⟨_, .pair a.elaborate.property b.elaborate.property⟩
  | @seq _ _ _ _ X A _ a b =>
    ⟨_, .let₁ a.elaborate.property (b.elaborate.property.rename ((Ren.wk [] X).lift A))⟩
  | .fst A B => ⟨_, WithProjectionReturns.fstTerm A B⟩
  | .snd A B => ⟨_, WithProjectionReturns.sndTerm A B⟩
  | .destructure _ _ body => ⟨_, unpackTerm_typed (applyPackedTerm_typed body.elaborate.property)⟩

/-- A guarded return or a native binary let. The binary let retains the
original input and supplies both bound fields to the packed body. -/
inductive Program (Φ : Type v) [HasTy Φ τ] : τ → τ → Type (max u v) where
  | returned {X D : τ} : Term Φ X D → Program Φ X D
  | branchInput {X : τ} : Program Φ X X
  | let₂ {X D : τ} (A B : τ) :
      Term Φ X (product A B) → Program Φ (product X (product A B)) D → Program Φ X D

/-- Elaborate directly to a region with constructor-valued branch arguments. -/
def Program.elaborate {X D : τ} : Program Φ X D → {r : Region Φ // ValueBranches [X] r [D]}
  | .returned t => ⟨_, returnRegion_typed t.elaborate.property⟩
  | .branchInput => ⟨_, .br (ℓ := 0) rfl (.var (i := 0) rfl)⟩
  | .let₂ _ _ a body => ⟨_, .let₂ a.elaborate.property (applyPackedPair_typed body.elaborate.property)⟩

variable (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

set_option hygiene false in
local notation "Obj" => ofType Seed

/-- Interpret the term directly in the guarded generators. Pairing uses
left-to-right order and the called primitive consumes its operand once. -/
noncomputable def Term.generatorArrow {X D : τ} : Term Φ X D → (Obj X ⟶ Obj D)
  | .input => 𝟙 (Obj X)
  | .unit => discardArrow Seed X
  | .call p a => a.generatorArrow ≫ primitive Seed p
  | .pair a b => pairArrows Seed (a.generatorArrow) (b.generatorArrow)
  | .seq a b => a.generatorArrow ≫ b.generatorArrow
  | .fst A B => productFst Seed A B
  | .snd A B => productSnd Seed A B
  | .destructure _ _ body => body.generatorArrow

/-- Interpret a native product let by copying the input, evaluating the
producer with the input retained, and entering the packed body. -/
noncomputable def Program.generatorArrow {X D : τ} : Program Φ X D → (Obj X ⟶ Obj D)
  | .returned t => t.generatorArrow Seed
  | .branchInput => 𝟙 (Obj X)
  | .let₂ _ _ a body =>
    (diagonalArrow Seed (Obj X) ≫ (whiskerLeftFunctor Seed (Obj X)).map (a.generatorArrow Seed)) ≫
      body.generatorArrow

variable {ε : Type w} [HasEff Φ ε] (pe : ε)

/-- The actual guarded arrow obtained by elaborating a program in the opt-in quotient. -/
def Program.arrow {X D : τ} (p : Program Φ X D) :
    ofType (JoinedStep (τ := τ) (Φ := Φ) pe) X ⟶ ofType (JoinedStep (τ := τ) (Φ := Φ) pe) D :=
  ofRegion (JoinedStep (τ := τ) (Φ := Φ) pe) p.elaborate.property

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.Intrinsic

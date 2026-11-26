module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.Generation.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.BinaryLet.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedCase.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Iteration.Defs

/-! # The guarded singleton representative grammar -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProductDestructureReturns

open Silmaril Silmaril.Isotope.LambdaSSA
open CfgEta.TypeCategory (returnRegion_typed seqValueBranches caseValueBranches
  whiskerLeftRegion_typed whiskerRightRegion_typed)
open Paper.PackedBody (applyPacked_typed)
open Paper.SingletonReification.BinaryLet (applyPackedPair_typed returnPair)
open Paper.RetainedLet (returnOnce)
open Paper.RetainedCase (returnSum_typed)
open Paper.WithPairReturns (ReturnFragmentWithRules)

universe u v w

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- A product producer with a native destructure-and-rebuild equation. -/
inductive ConstructorProduct : {X A B : τ} → {a : Tm Φ} →
    Tm.HasType [X] a (product A B) → Prop where
  | var {X A B : τ} {i : Nat} (hi : At [X] i (product A B)) :
      ConstructorProduct (.var hi)
  | pair {X A B : τ} {a b : Tm Φ}
      (ha : Tm.BranchValue [X] a A) (hb : Tm.BranchValue [X] b B) :
      ConstructorProduct (.pair ha.hasType hb.hasType)

/-- The exact quotient comparison used by native binary lets on computed products. -/
abbrev ProductProducerAgreement (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop) : Prop :=
  ∀ {X A B : τ} {a : Tm Φ}, Tm.HasType [X] a (product A B) →
    Paper.Extension.Eqv Seed [X] (returnPair a) (returnOnce a) [product A B]

variable {ε : Type w} [HasEff Φ ε] (pe : ε)

/-- The binary-let scrutinee is a constructor product or, when enabled,
a product already covered by the recursive returned-term grammar. -/
abbrev ProductScrutinee (computedProducts : Bool)
    {X A B : τ} {a : Tm Φ} (ha : Tm.HasType [X] a (product A B)) : Prop :=
  if computedProducts then ConstructorProduct ha ∨ ReturnFragmentWithRules pe true true ha
  else ConstructorProduct ha

/-- A grammar of actual typed singleton representatives. Captured bodies are
supplied by opening a guarded packed representative. A retained case also
requires a representative of its scrutinee with the original tag returned.
Feedback uses the canonical exact-sum one-block representative. The flag
enables a native binary let whose scrutinee belongs to the returned-term
fragment. -/
inductive GuardedFragmentWithProducts (computedProducts : Bool) :
    {X D : τ} → {r : Region Φ} → ValueBranches [X] r [D] → Prop where
  | initial {D : τ} {r : Region Φ} (hr : ValueBranches [Silmaril.empty] r [D]) :
      GuardedFragmentWithProducts computedProducts hr
  | branch {X D : τ} {a : Tm Φ} (ha : Tm.BranchValue [X] a D) :
      GuardedFragmentWithProducts computedProducts (.br (ℓ := 0) rfl ha)
  | returned {X D : τ} {a : Tm Φ} {ha : Tm.HasType [X] a D} :
      ReturnFragmentWithRules pe true true ha → GuardedFragmentWithProducts computedProducts (returnRegion_typed ha)
  | seq {X A D : τ} {r s : Region Φ} {hr : ValueBranches [X] r [A]} {hs : ValueBranches [A] s [D]} :
      GuardedFragmentWithProducts computedProducts hr → GuardedFragmentWithProducts computedProducts hs →
      GuardedFragmentWithProducts computedProducts (seqValueBranches hr hs)
  | left (X : τ) {A D : τ} {r : Region Φ} {hr : ValueBranches [A] r [D]} :
      GuardedFragmentWithProducts computedProducts hr → GuardedFragmentWithProducts computedProducts (whiskerLeftRegion_typed X hr)
  | right (X : τ) {A D : τ} {r : Region Φ} {hr : ValueBranches [A] r [D]} :
      GuardedFragmentWithProducts computedProducts hr → GuardedFragmentWithProducts computedProducts (whiskerRightRegion_typed X hr)
  | let₁ {X A D : τ} {a : Tm Φ} {p : Region Φ} {ha : Tm.HasType [X] a A}
      {hp : ValueBranches [product X A] p [D]} :
      ReturnFragmentWithRules pe true true ha → GuardedFragmentWithProducts computedProducts hp →
      GuardedFragmentWithProducts computedProducts (.let₁ ha (applyPacked_typed hp))
  | let₂ {X A B D : τ} {a : Tm Φ} {p : Region Φ} {ha : Tm.HasType [X] a (product A B)}
      {hp : ValueBranches [product X (product A B)] p [D]} :
      ProductScrutinee pe computedProducts ha → GuardedFragmentWithProducts computedProducts hp →
      GuardedFragmentWithProducts computedProducts (.let₂ ha (applyPackedPair_typed hp))
  | caseInput {A B D : τ} {l r : Region Φ} {hl : ValueBranches [A] l [D]}
      {hr : ValueBranches [B] r [D]} :
      GuardedFragmentWithProducts computedProducts hl → GuardedFragmentWithProducts computedProducts hr →
      GuardedFragmentWithProducts computedProducts (caseValueBranches hl hr)
  | tagLeft {X A B : τ} {a : Tm Φ} {ha : Tm.HasType [X] a A} :
      ReturnFragmentWithRules pe true true ha →
      GuardedFragmentWithProducts computedProducts (returnSum_typed (.inl ha : Tm.HasType [X] (.inl a) (coprod A B)))
  | tagRight {X A B : τ} {a : Tm Φ} {ha : Tm.HasType [X] a B} :
      ReturnFragmentWithRules pe true true ha →
      GuardedFragmentWithProducts computedProducts (returnSum_typed (.inr ha : Tm.HasType [X] (.inr a) (coprod A B)))
  | caseRetained {X A B D : τ} {a : Tm Φ} {l r : Region Φ}
      (ha : Tm.HasType [X] a (coprod A B))
      {hl : ValueBranches [product X A] l [D]} {hr : ValueBranches [product X B] r [D]} :
      GuardedFragmentWithProducts computedProducts (returnSum_typed ha) →
      GuardedFragmentWithProducts computedProducts hl → GuardedFragmentWithProducts computedProducts hr →
      GuardedFragmentWithProducts computedProducts (.case ha (applyPacked_typed hl) (applyPacked_typed hr))
  | cfgZero {X D : τ} {r : Region Φ} {hr : ValueBranches [X] r [D]} (blocks : Fin 0 → Region Φ) :
      GuardedFragmentWithProducts computedProducts hr →
      GuardedFragmentWithProducts computedProducts (.cfg Fin.elim0 hr (fun i => i.elim0) : ValueBranches [X] (.cfg r 0 blocks) [D])
  | iterate {X D : τ} {r : Region Φ} {hr : ValueBranches [X] r [coprod D X]} :
      GuardedFragmentWithProducts computedProducts hr →
      GuardedFragmentWithProducts computedProducts (SyntacticCategory.iterateRegion_valueBranches hr)

variable {pe} in
/-- Use the returned-term grammar to supply a computed binary-let scrutinee. -/
theorem GuardedFragmentWithProducts.let₂Computed {X A B D : τ} {a : Tm Φ} {p : Region Φ}
    {ha : Tm.HasType [X] a (product A B)} {hp : ValueBranches [product X (product A B)] p [D]}
    (producer : ReturnFragmentWithRules pe true true ha) (body : GuardedFragmentWithProducts pe true hp) :
    GuardedFragmentWithProducts pe true (.let₂ ha (applyPackedPair_typed hp)) :=
  .let₂ (.inr producer) body

/-- The guarded grammar for the product-destructure join. -/
abbrev GuardedFragment {X D : τ} {r : Region Φ} (hr : ValueBranches [X] r [D]) :=
  GuardedFragmentWithProducts pe false hr

namespace GuardedFragment

variable {pe}

abbrev initial := @GuardedFragmentWithProducts.initial τ _ Φ _ ε _ pe false
abbrev branch := @GuardedFragmentWithProducts.branch τ _ Φ _ ε _ pe false
abbrev returned := @GuardedFragmentWithProducts.returned τ _ Φ _ ε _ pe false
abbrev seq := @GuardedFragmentWithProducts.seq τ _ Φ _ ε _ pe false
abbrev left := @GuardedFragmentWithProducts.left τ _ Φ _ ε _ pe false
abbrev right := @GuardedFragmentWithProducts.right τ _ Φ _ ε _ pe false
abbrev let₁ := @GuardedFragmentWithProducts.let₁ τ _ Φ _ ε _ pe false
abbrev let₂ := @GuardedFragmentWithProducts.let₂ τ _ Φ _ ε _ pe false
abbrev caseInput := @GuardedFragmentWithProducts.caseInput τ _ Φ _ ε _ pe false
abbrev tagLeft := @GuardedFragmentWithProducts.tagLeft τ _ Φ _ ε _ pe false
abbrev tagRight := @GuardedFragmentWithProducts.tagRight τ _ Φ _ ε _ pe false
abbrev caseRetained := @GuardedFragmentWithProducts.caseRetained τ _ Φ _ ε _ pe false
abbrev cfgZero := @GuardedFragmentWithProducts.cfgZero τ _ Φ _ ε _ pe false
abbrev iterate := @GuardedFragmentWithProducts.iterate τ _ Φ _ ε _ pe false

end GuardedFragment

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProductDestructureReturns

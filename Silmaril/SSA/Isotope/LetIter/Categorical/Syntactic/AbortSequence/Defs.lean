module

public import Silmaril.SSA.Isotope.LetIter.AbortSequence.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.Defs
public import Silmaril.SSA.Isotope.Bridge.Thms
public import Silmaril.SSA.Thesis.SyntacticCategory.Packing.Defs

/-! # The native abort extension on thesis syntax and syntactic homs -/

@[expose] public section

universe u

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic

open CategoryTheory
open Silmaril.Isotope.LetIter.LocallyNameless (AbortEquiv Refinement)
open Silmaril.Thesis.LambdaIter.Syn (Carrier El SynCat)

variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]

local notation "ThesisTm" => Thesis.LambdaIter.LocallyNameless.Tm
local notation "ThesisHasType" => Thesis.LambdaIter.LocallyNameless.HasType
local notation "ThesisEqv" => Thesis.LambdaIter.LocallyNameless.Eqv

local instance : Thesis.LambdaIter.TypeFormers τ := Bridge.thesisTypeFormers τ
local instance : Thesis.LambdaIter.HasTy Φ τ := Bridge.thesisHasTy Φ τ
local instance : Thesis.LambdaIter.HasEff Φ ε := Bridge.thesisHasEff Φ ε

variable (pe : ε)

local notation "S" => signature (τ := τ) (Φ := Φ) pe

/-- Native abort equivalence pulled back along the term translation, with empty free context. -/
abbrev RepairedEqv {n : Nat} (β : BoundCtx τ n) (a b : ThesisTm Empty Φ n) (A : τ) : Prop :=
  AbortEquiv pe (Ctx.nil : Ctx Empty τ) β (Bridge.ofThesis a) (Bridge.ofThesis b) A

/-- Old thesis equations are included in the pullback. -/
theorem RepairedEqv.of_eqv {n : Nat} {β : BoundCtx τ n}
    {a b : ThesisTm Empty Φ n} {A : τ}
    (h : ThesisEqv pe .nil (Bridge.BoundCtx.toThesis β) a b A) :
    RepairedEqv pe β a b A := by
  apply Refinement.equiv
  apply (Bridge.equiv_iff (Bridge.TypeCompat.canonical τ) (Bridge.InstrCompat.canonical Φ τ)
    (Bridge.EffCompat.canonical Φ ε) pe).mpr
  simpa only [Bridge.Ctx.toThesis, Bridge.toThesis_ofThesis] using h

/-- The abort-extended setoid on exactly typed thesis terms. -/
def repairedSetoid {n : Nat} (β : BoundCtx τ n) (A : τ) :
    Setoid (Carrier S (Bridge.BoundCtx.toThesis β) A) where
  r a b := RepairedEqv pe β a.1 b.1 A
  iseqv := ⟨fun a => a.2.elim fun h => RepairedEqv.of_eqv pe (.refl h),
    AbortEquiv.symm, Refinement.trans⟩

/-- Map an exact term class to its class for the abort extension. -/
def repairedClass {n : Nat} {β : BoundCtx τ n} {A : τ}
    (t : El S (Bridge.BoundCtx.toThesis β) A) : Quotient (repairedSetoid (Φ := Φ) pe β A) :=
  Quotient.map id (fun _ _ h => RepairedEqv.of_eqv pe h) t

/-- The abort-extended hom setoid on the one-variable syntactic representatives. -/
abbrev repairedHomSetoid (X Y : SynCat S) :
    Setoid (Carrier S (.snoc .nil X.ty) Y.ty) :=
  repairedSetoid pe (.snoc .nil X.ty) Y.ty

/-- The repaired class of an exact syntactic arrow. -/
def repairedHomClass {X Y : SynCat S} (f : X ⟶ Y) : Quotient (repairedHomSetoid pe X Y) :=
  repairedClass (β := .snoc .nil X.ty) pe f

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic

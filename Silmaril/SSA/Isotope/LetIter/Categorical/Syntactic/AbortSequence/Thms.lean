module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Defs
public import Silmaril.SSA.Thesis.SyntacticCategory.Packing.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Packing

/-! # Substitution and packing in the repaired LetIter homs -/

public section

universe u

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic

open CategoryTheory
open Silmaril.Thesis.LambdaIter.Syn (mk)
open Silmaril.Thesis.LambdaIter.Syn.SynCat

variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]

local notation "ThesisTm" => Thesis.LambdaIter.LocallyNameless.Tm
local notation "ThesisHasType" => Thesis.LambdaIter.LocallyNameless.HasType

local instance : Thesis.LambdaIter.TypeFormers τ := Bridge.thesisTypeFormers τ
local instance : Thesis.LambdaIter.HasTy Φ τ := Bridge.thesisHasTy Φ τ
local instance : Thesis.LambdaIter.HasEff Φ ε := Bridge.thesisHasEff Φ ε

variable (pe : ε)

local notation "modelSig" => signature (τ := τ) (Φ := Φ) pe
local notation "toThesisCtx" => Bridge.BoundCtx.toThesis

/-- Exactly typed, pure thesis substitutions preserve the pullback of native abort equivalence. -/
theorem RepairedEqv.bsubst {n m : Nat} {β : BoundCtx τ n} {δ : BoundCtx τ m}
    {a b : ThesisTm Empty Φ n} {A : τ} {σ : Fin n → ThesisTm Empty Φ m}
    (h : RepairedEqv pe β a b A)
    (s : Thesis.LambdaIter.LocallyNameless.PureTypedSubst (Γ := .nil) (pureEff := pe)
      (toThesisCtx β) (toThesisCtx δ) σ) :
    RepairedEqv pe δ (Thesis.LambdaIter.LocallyNameless.Tm.bsubst σ a)
      (Thesis.LambdaIter.LocallyNameless.Tm.bsubst σ b) A :=
  AbortSequenceProofs.repaired_bsubst pe h s

/-- The projection substitution that packs a context respects the repaired relation. -/
theorem RepairedEqv.packedTerm {n : Nat} {β : BoundCtx τ n}
    {a b : ThesisTm Empty Φ n} {A : τ} (h : RepairedEqv pe β a b A) :
    RepairedEqv pe (.snoc .nil (packType (S := modelSig) (toThesisCtx β)))
      (packedTerm (S := modelSig) (toThesisCtx β) a) (packedTerm (S := modelSig) (toThesisCtx β) b) A :=
  AbortSequenceProofs.repaired_packedTerm pe h

/-- Substituting the tuple of the original variables respects the repaired relation. -/
theorem RepairedEqv.unpackedTerm {n : Nat} (β : BoundCtx τ n)
    {a b : ThesisTm Empty Φ 1} {A : τ}
    (h : RepairedEqv pe (.snoc .nil (packType (S := modelSig) (toThesisCtx β))) a b A) :
    RepairedEqv pe β (unpackedTerm (S := modelSig) (toThesisCtx β) a)
      (unpackedTerm (S := modelSig) (toThesisCtx β) b) A :=
  AbortSequenceProofs.repaired_unpackedTerm pe β h

/-- Packing and unpacking induce inverse maps on the repaired quotient. -/
noncomputable def repairedPackedHomEquiv {n : Nat} (β : BoundCtx τ n) (A : τ) :
    Quotient (repairedSetoid (Φ := Φ) pe β A) ≃
      Quotient (repairedHomSetoid pe (of (S := modelSig) (packType (S := modelSig) (toThesisCtx β)))
        (of (S := modelSig) A)) :=
  AbortSequenceProofs.repairedPackedHomEquiv_proof pe β A

/-- Packing on the repaired quotient agrees with projecting the old packed arrow. -/
theorem repairedPackedHomEquiv_mk {n : Nat} {β : BoundCtx τ n} {a : ThesisTm Empty Φ n}
    {A : τ} (ha : ThesisHasType Φ .nil (toThesisCtx β) a A) :
    repairedPackedHomEquiv pe β A (repairedClass pe (mk (S := modelSig) ha)) =
      repairedHomClass pe (packedArrow (S := modelSig) ha) :=
  AbortSequenceProofs.repairedPackedHomEquiv_mk_proof pe ha

/-- Equality of repaired packed classes reflects and preserves the repaired term relation. -/
theorem repairedHomClass_packedArrow_eq_iff {n : Nat} {β : BoundCtx τ n}
    {a b : ThesisTm Empty Φ n} {A : τ}
    (ha : ThesisHasType Φ .nil (toThesisCtx β) a A)
    (hb : ThesisHasType Φ .nil (toThesisCtx β) b A) :
    repairedHomClass pe (packedArrow (S := modelSig) ha) =
      repairedHomClass pe (packedArrow (S := modelSig) hb) ↔ RepairedEqv pe β a b A :=
  AbortSequenceProofs.repaired_packedArrow_eq_iff pe ha hb

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic

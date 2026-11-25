module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Defs
public import Silmaril.SSA.Thesis.SyntacticCategory.Packing.Thms

/-! # Packing respects the abort-extended presentation -/

public section

universe u

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic
namespace AbortSequenceProofs

open CategoryTheory
open Silmaril.Isotope.LetIter.LocallyNameless (AbortEquiv HasType PureTypedSubst Tm)
open Silmaril.Thesis.LambdaIter.Syn (Carrier mk)
open Silmaril.Thesis.LambdaIter.Syn.SynCat

variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]

local notation "ThesisTm" => Thesis.LambdaIter.LocallyNameless.Tm
local notation "ThesisHasType" => Thesis.LambdaIter.LocallyNameless.HasType

local instance repairedPackingProofThesisTypeFormers : Thesis.LambdaIter.TypeFormers τ :=
  Bridge.thesisTypeFormers τ
local instance repairedPackingProofThesisHasTy : Thesis.LambdaIter.HasTy Φ τ :=
  Bridge.thesisHasTy Φ τ
local instance repairedPackingProofThesisHasEff : Thesis.LambdaIter.HasEff Φ ε :=
  Bridge.thesisHasEff Φ ε

variable (pe : ε)

local notation "modelSig" => signature (τ := τ) (Φ := Φ) pe
local notation "βᵀ" => Bridge.BoundCtx.toThesis

private theorem nativeTyping {n : Nat} {β : BoundCtx τ n} {t : ThesisTm Empty Φ n} {A : τ}
    (h : ThesisHasType Φ .nil (βᵀ β) t A) :
    HasType Φ (Ctx.nil : Ctx Empty τ) β (Bridge.ofThesis t) A := by
  apply (Bridge.hasType_iff (Bridge.TypeCompat.canonical τ)
    (Bridge.InstrCompat.canonical Φ τ)).mpr
  simpa only [Bridge.Ctx.toThesis, Bridge.toThesis_ofThesis] using Nonempty.intro h

private theorem ofThesis_bsubst {n m : Nat} (σ : Fin n → ThesisTm Empty Φ m)
    (t : ThesisTm Empty Φ n) :
    Bridge.ofThesis (Thesis.LambdaIter.LocallyNameless.Tm.bsubst σ t) =
      Tm.bsubst (fun i => Bridge.ofThesis (σ i)) (Bridge.ofThesis t) := by
  have h := Bridge.toThesis_bsubst (fun i => Bridge.ofThesis (σ i)) (Bridge.ofThesis t)
  simpa only [Bridge.toThesis_ofThesis, Bridge.ofThesis_toThesis] using
    (congrArg Bridge.ofThesis h).symm

theorem repaired_bsubst {n m : Nat} {β : BoundCtx τ n} {δ : BoundCtx τ m}
    {a b : ThesisTm Empty Φ n} {A : τ} {σ : Fin n → ThesisTm Empty Φ m}
    (h : RepairedEqv pe β a b A)
    (s : Thesis.LambdaIter.LocallyNameless.PureTypedSubst (Γ := .nil) (pureEff := pe) (βᵀ β) (βᵀ δ) σ) :
    RepairedEqv pe δ (Thesis.LambdaIter.LocallyNameless.Tm.bsubst σ a) (Thesis.LambdaIter.LocallyNameless.Tm.bsubst σ b) A := by
  let native : PureTypedSubst pe (Ctx.nil : Ctx Empty τ) β δ
      (fun i => Bridge.ofThesis (σ i)) := {
    typed := fun i => by
      rw [← Bridge.BoundCtx.get_toThesis β i]
      exact nativeTyping (s.typed i)
    pure := fun i => (Bridge.pure_iff (Bridge.EffCompat.canonical Φ ε) pe).mpr
      (by simpa only [Bridge.toThesis_ofThesis] using s.pure i)
  }
  simpa only [RepairedEqv, ofThesis_bsubst] using AbortEquiv.bsubst h native

theorem repaired_packedTerm {n : Nat} {β : BoundCtx τ n}
    {a b : ThesisTm Empty Φ n} {A : τ} (h : RepairedEqv pe β a b A) :
    RepairedEqv pe (.snoc .nil (packType (S := modelSig) (βᵀ β)))
      (packedTerm (S := modelSig) (βᵀ β) a) (packedTerm (S := modelSig) (βᵀ β) b) A :=
  repaired_bsubst pe h
    ⟨projectTyping (S := modelSig) (βᵀ β) Thesis.LambdaIter.LocallyNameless.HasType.newest,
      fun i => packedTerm_pure (S := modelSig) (βᵀ β) (t := .bv i) .bv⟩

theorem repaired_unpackedTerm {n : Nat} (β : BoundCtx τ n)
    {a b : ThesisTm Empty Φ 1} {A : τ}
    (h : RepairedEqv pe (.snoc .nil (packType (S := modelSig) (βᵀ β))) a b A) :
    RepairedEqv pe β (unpackedTerm (S := modelSig) (βᵀ β) a) (unpackedTerm (S := modelSig) (βᵀ β) b) A :=
  repaired_bsubst pe h
    ⟨fun i => Fin.cases (packTermTyping (S := modelSig) (βᵀ β)) (fun j => j.elim0) i,
      fun _ => packTerm_pure (S := modelSig) (βᵀ β)⟩

theorem repaired_packedArrow_eq_iff {n : Nat} {β : BoundCtx τ n}
    {a b : ThesisTm Empty Φ n} {A : τ}
    (ha : ThesisHasType Φ .nil (βᵀ β) a A)
    (hb : ThesisHasType Φ .nil (βᵀ β) b A) :
    repairedHomClass pe (packedArrow (S := modelSig) ha) =
      repairedHomClass pe (packedArrow (S := modelSig) hb) ↔ RepairedEqv pe β a b A := by
  constructor
  · intro h
    have packed : RepairedEqv pe (.snoc .nil (packType (S := modelSig) (βᵀ β)))
        (packedTerm (S := modelSig) (βᵀ β) a) (packedTerm (S := modelSig) (βᵀ β) b) A := Quotient.exact h
    have lhs := RepairedEqv.of_eqv pe (β := β) (unpacked_packed (S := modelSig) ha)
    have rhs := RepairedEqv.of_eqv pe (β := β) (unpacked_packed (S := modelSig) hb)
    exact (AbortEquiv.symm lhs).trans ((repaired_unpackedTerm pe β packed).trans rhs)
  · intro h
    exact Quotient.sound (repaired_packedTerm pe h)

def repairedPackedHomEquiv_proof {n : Nat} (β : BoundCtx τ n) (A : τ) :
    Quotient (repairedSetoid (Φ := Φ) pe β A) ≃
      Quotient (repairedHomSetoid pe (of (S := modelSig) (packType (S := modelSig) (βᵀ β)))
        (of (S := modelSig) A)) where
  toFun := Quotient.map
    (fun a => ⟨packedTerm (S := modelSig) (βᵀ β) a.1,
      a.2.map (packedTyping (S := modelSig))⟩)
    (fun _ _ h => repaired_packedTerm pe h)
  invFun := Quotient.map
    (fun a => ⟨unpackedTerm (S := modelSig) (βᵀ β) a.1,
      a.2.map (fun h => h.bsubst
        (fun i => Fin.cases (packTermTyping (S := modelSig) (βᵀ β)) (fun j => j.elim0) i))⟩)
    (fun _ _ h => repaired_unpackedTerm pe β h)
  left_inv := by
    intro x
    induction x using Quotient.ind with
    | _ a =>
      obtain ⟨h⟩ := a.2
      exact Quotient.sound (RepairedEqv.of_eqv pe (β := β) (unpacked_packed h))
  right_inv := by
    intro x
    induction x using Quotient.ind with
    | _ a =>
      obtain ⟨h⟩ := a.2
      exact Quotient.sound (RepairedEqv.of_eqv pe (packed_unpacked (S := modelSig) (βᵀ β) h))

theorem repairedPackedHomEquiv_mk_proof {n : Nat} {β : BoundCtx τ n} {a : ThesisTm Empty Φ n}
    {A : τ} (ha : ThesisHasType Φ .nil (βᵀ β) a A) :
    repairedPackedHomEquiv_proof pe β A (repairedClass pe (mk (S := modelSig) ha)) =
      repairedHomClass pe (packedArrow (S := modelSig) ha) := by rfl

end AbortSequenceProofs
end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic

module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Operations.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.Packing.Thms

/-! # Reifying native LetIter derivations in the abort-extended presentation -/

public section

universe u

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic.ReificationProofs

open CategoryTheory
open Silmaril.Isotope.LetIter.LocallyNameless (AbortEquiv Derivation Tm)
open Silmaril.Thesis.LambdaIter.Syn (mk)
open Silmaril.Thesis.LambdaIter.Syn.SynCat

variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]

local instance reificationThesisTypeFormers : Thesis.LambdaIter.TypeFormers τ :=
  Bridge.thesisTypeFormers τ
local instance reificationThesisHasTy : Thesis.LambdaIter.HasTy Φ τ :=
  Bridge.thesisHasTy Φ τ
local instance reificationThesisHasEff : Thesis.LambdaIter.HasEff Φ ε :=
  Bridge.thesisHasEff Φ ε

variable (pe : ε)

local notation "modelSig" => signature (τ := τ) (Φ := Φ) pe
local notation "classOf" => repairedHomClass (τ := τ) (Φ := Φ) pe
local notation "ThesisTyping" => Thesis.LambdaIter.LocallyNameless.HasType

private def emptyElim (A : τ) : of (S := modelSig) (empty : τ) ⟶ of A :=
  mk (Thesis.LambdaIter.LocallyNameless.HasType.abort (C := A)
    Thesis.LambdaIter.LocallyNameless.HasType.newest)

private theorem packedNative_abort {n : Nat} {β : BoundCtx τ n} {t : Tm Empty Φ n}
    (A : τ) (d : Derivation Φ (Ctx.nil : Ctx Empty τ) β t (empty : τ)) :
    packedNative pe (.abort (C := A) d) = packedNative pe d ≫ emptyElim (Φ := Φ) pe A := by
  let J := values modelSig
  let e := J.map ((typeModel (Φ := Φ) pe).emptyIsInitial.to (valueObj pe A))
  have he : e = emptyElim (Φ := Φ) pe A := fromEmpty_unique (S := modelSig) (of A) e _
  change J.map (packedEnvIso (Φ := Φ) pe β).inv ≫ denoteInSyntax pe d ≫ e = _
  rw [he]
  exact (Category.assoc _ _ _).symm

/-- The repaired short sequencing equation on a packed, possibly effectful scrutinee. -/
private theorem packedArrow_abort_repaired {n : Nat} {β : BoundCtx τ n} {t : Tm Empty Φ n}
    (A : τ) (h : ThesisTyping Φ .nil
      (Bridge.BoundCtx.toThesis β) (Bridge.toThesis t) (empty : τ)) :
    classOf (packedArrow (S := modelSig) h ≫ emptyElim (Φ := Φ) pe A) =
      classOf (packedArrow (S := modelSig) (.abort (C := A) h)) := by
  have nativeTyping : LocallyNameless.HasType Φ (Ctx.nil : Ctx Empty τ)
      (.snoc .nil (packType (S := modelSig) (Bridge.BoundCtx.toThesis β)))
      (Bridge.ofThesis (packedTerm (S := modelSig) (Bridge.BoundCtx.toThesis β) (Bridge.toThesis t)))
      (empty : τ) := by
    apply (Bridge.hasType_iff (Bridge.TypeCompat.canonical τ) (Bridge.InstrCompat.canonical Φ τ)).mpr
    simpa only [Bridge.Ctx.toThesis, Bridge.BoundCtx.toThesis, Bridge.toThesis_ofThesis] using
      Nonempty.intro (packedTyping (S := modelSig) h)
  exact Quotient.sound (AbortEquiv.symm (AbortEquiv.sequence nativeTyping))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem exists_thesis_reification {n : Nat} {β : BoundCtx τ n} {t : Tm Empty Φ n} {A : τ}
    (d : Derivation Φ (Ctx.nil : Ctx Empty τ) β t A) :
    ∃ h : ThesisTyping Φ .nil (Bridge.BoundCtx.toThesis β) (Bridge.toThesis t) A,
      classOf (packedNative pe d) = classOf (packedArrow (S := modelSig) h) := by
  induction d with
  | @fv _ _ x _ _ => exact x.elim
  | @bv n β i =>
    have ht := (Bridge.hasType_iff (Bridge.TypeCompat.canonical τ) (Bridge.InstrCompat.canonical Φ τ)
      (Γ := (Ctx.nil : Ctx Empty τ)) (β := β) (t := .bv i)).mp
      (Derivation.bv (Φ := Φ) (Γ := (Ctx.nil : Ctx Empty τ)) (β := β) (ι := i)).toHasType
    obtain ⟨h⟩ := ht
    exact ⟨h, congrArg classOf (packedNative_bv_eq_packedArrow pe i h)⟩
  | op d ih =>
    obtain ⟨h, eq⟩ := ih
    refine ⟨.op h, ?_⟩
    rw [packedNative_op, packedArrow_op]
    exact repairedHomClass_comp_congr pe eq rfl
  | let₁ d e ih₁ ih₂ =>
    obtain ⟨ha, ea⟩ := ih₁
    obtain ⟨hb, eb⟩ := ih₂
    refine ⟨.let₁ ha hb, ?_⟩
    rw [packedNative_let1, bind_values, packedArrow_let1]
    exact repairedHomClass_comp_congr pe (repairedHomClass_pairArrows_congr pe rfl ea) eb
  | unit =>
    exact ⟨.unit, congrArg classOf (packedNative_unit_eq_packedArrow pe .unit)⟩
  | pair d e ih₁ ih₂ =>
    obtain ⟨ha, ea⟩ := ih₁
    obtain ⟨hb, eb⟩ := ih₂
    refine ⟨.pair ha hb, ?_⟩
    rw [packedNative_pair, packedArrow_pair]
    exact repairedHomClass_pairArrows_congr pe ea eb
  | let₂ d e ih₁ ih₂ =>
    obtain ⟨ha, ea⟩ := ih₁
    obtain ⟨hb, eb⟩ := ih₂
    refine ⟨.let₂ ha hb, ?_⟩
    rw [packedNative_let2, packedArrow_let2]
    exact repairedHomClass_comp_congr pe (repairedHomClass_pairArrows_congr pe rfl ea)
      (repairedHomClass_comp_congr pe rfl eb)
  | inl d ih =>
    obtain ⟨h, eq⟩ := ih
    refine ⟨.inl h, ?_⟩
    rw [packedNative_inl, packedArrow_inl]
    exact repairedHomClass_comp_congr pe eq rfl
  | inr d ih =>
    obtain ⟨h, eq⟩ := ih
    refine ⟨.inr h, ?_⟩
    rw [packedNative_inr, packedArrow_inr]
    exact repairedHomClass_comp_congr pe eq rfl
  | case d dl dr iht ihl ihr =>
    obtain ⟨ht, et⟩ := iht
    obtain ⟨hl, el⟩ := ihl
    obtain ⟨hr, er⟩ := ihr
    refine ⟨.case ht hl hr, ?_⟩
    rw [packedNative_case, packedArrow_case]
    exact repairedHomClass_comp_congr pe (repairedHomClass_pairArrows_congr pe rfl et)
      (repairedHomClass_comp_congr pe rfl (repairedHomClass_coprodDesc_congr pe el er))
  | @abort _ _ _ A d ih =>
    obtain ⟨h, eq⟩ := ih
    refine ⟨.abort h, ?_⟩
    rw [packedNative_abort]
    exact (repairedHomClass_comp_congr pe eq rfl).trans (packedArrow_abort_repaired pe A h)
  | iter da db iha ihb =>
    obtain ⟨ha, ea⟩ := iha
    obtain ⟨hb, eb⟩ := ihb
    refine ⟨.iter ha hb, ?_⟩
    rw [packedNative_iter, packedArrow_iter_state, ← contextualLoop_carried pe hb]
    exact repairedHomClass_comp_congr pe (repairedHomClass_pairArrows_congr pe rfl ea)
      (repairedHomClass_contextualLoop_congr pe (repairedHomClass_comp_congr pe eb rfl))

theorem packedNative_repaired_reification {n : Nat} {β : BoundCtx τ n} {t : Tm Empty Φ n} {A : τ}
    (d : Derivation Φ (Ctx.nil : Ctx Empty τ) β t A)
    (h : ThesisTyping Φ .nil (Bridge.BoundCtx.toThesis β) (Bridge.toThesis t) A) :
    classOf (packedNative pe d) = classOf (packedArrow (S := modelSig) h) := by
  obtain ⟨witness, eq⟩ := exists_thesis_reification pe d
  have same := (packedArrow_eq_iff (S := modelSig) witness h).mpr (.refl witness)
  exact eq.trans (congrArg classOf same)

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic.ReificationProofs

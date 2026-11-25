module

import Silmaril.SSA.Isotope.LetIter.Categorical.AbortSequence.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.Packing.Thms
import Silmaril.SSA.Isotope.Bridge.Packing.Thms

/-! Checked handoff from the repaired native relation to a packed witness. -/

namespace Silmaril.Isotope.LetIter.AbortSequenceHandoff

open LocallyNameless
open CategoryTheory
open Semantics.Categorical.Syntactic
open Silmaril.Thesis.LambdaIter.Syn.SynCat
open Silmaril.Thesis.LambdaIter.Syn (mk)

universe u v

section Substitution

variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]
  {ν : Type v} [DecidableEq ν] {pe : ε} {Γ : Ctx ν τ}
  {n m : Nat} {β : BoundCtx τ n} {δ : BoundCtx τ m}
  {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)} {A B : τ}

/-- Every native exact equation is admitted by the repaired presentation. -/
theorem exactEquiv_inclusion {l r : Tm ν Φ n}
    (h : Equiv pe Γ β l r A) : AbortEquiv pe Γ β l r A :=
  Refinement.equiv h

/-- The primitive generator implies commuting an arbitrary typed let through abort. -/
theorem commuteAbort (ha : HasType Φ Γ β a A)
    (hb : HasType Φ Γ (.snoc β A) b (empty : τ)) :
    AbortEquiv pe Γ β (.abort (.let₁ a b)) (.let₁ a (.abort b)) B :=
  .trans (AbortEquiv.sequence (.let₁ ha hb))
    (.trans (.equiv (Equiv.bindLet ha hb (.abort (C := B) .bv)))
      (.let₁ (Refinement.refl ha) (AbortEquiv.symm (AbortEquiv.sequence hb))))

/-- Every typed simultaneous bound substitution preserves this commuting instance.
In particular this covers pure packing projections and the unpacking tuple. -/
theorem commuteAbort_bsubst (ha : HasType Φ Γ β a A)
    (hb : HasType Φ Γ (.snoc β A) b (empty : τ))
    {σ : Fin n → Tm ν Φ m} (s : TypedSubst (Γ := Γ) β δ σ) :
    AbortEquiv pe Γ δ (Tm.bsubst σ (.abort (.let₁ a b)))
      (Tm.bsubst σ (.let₁ a (.abort b))) B :=
  commuteAbort (ha.bsubst s) (hb.bsubst (s.up A))

end Substitution

variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]

local instance : Thesis.LambdaIter.TypeFormers τ := Bridge.thesisTypeFormers τ
local instance : Thesis.LambdaIter.HasTy Φ τ := Bridge.thesisHasTy Φ τ
local instance : Thesis.LambdaIter.HasEff Φ ε := Bridge.thesisHasEff Φ ε

theorem thesisEqv_inclusion (pe : ε) {ν : Type v} [DecidableEq ν]
    {Γ : Thesis.LambdaIter.Ctx ν τ} {n : Nat} {β : Thesis.LambdaIter.LocallyNameless.BoundCtx τ n}
    {a b : Thesis.LambdaIter.LocallyNameless.Tm ν Φ n} {A : τ} (h : Thesis.LambdaIter.LocallyNameless.Eqv pe Γ β a b A) :
    AbortEquiv pe (Bridge.Ctx.ofThesis Γ) (Bridge.BoundCtx.ofThesis β)
      (Bridge.ofThesis a) (Bridge.ofThesis b) A :=
  exactEquiv_inclusion ((Bridge.eqv_iff (Bridge.TypeCompat.canonical τ)
    (Bridge.InstrCompat.canonical Φ τ) (Bridge.EffCompat.canonical Φ ε) pe).mp h)

theorem nativeTyping_of_thesis (pe : ε) {n : Nat} {β : BoundCtx τ n}
    {t : Thesis.LambdaIter.LocallyNameless.Tm Empty Φ n} {A : τ}
    (h : Thesis.LambdaIter.LocallyNameless.HasType (signature (τ := τ) (Φ := Φ) pe).Instr .nil
      (Bridge.BoundCtx.toThesis β) t A) :
    HasType Φ (Ctx.nil : Ctx Empty τ) β (Bridge.ofThesis t) A := by
  apply (Bridge.hasType_iff (Bridge.TypeCompat.canonical τ)
    (Bridge.InstrCompat.canonical Φ τ)).mpr
  simpa only [Bridge.Ctx.toThesis, Bridge.toThesis_ofThesis] using Nonempty.intro h

/-- Pull the merged native relation back to the exact syntactic hom representatives.
Here this is a setoid on each hom carrier. -/
def repairedHomSetoid (pe : ε) (P Q : Thesis.LambdaIter.Syn.SynCat (signature (τ := τ) (Φ := Φ) pe)) :
    Setoid (Thesis.LambdaIter.Syn.Carrier (signature (τ := τ) (Φ := Φ) pe) (.snoc .nil P.ty) Q.ty) where
  r a b := AbortEquiv pe (Ctx.nil : Ctx Empty τ) (.snoc .nil P.ty)
    (Bridge.ofThesis a.1) (Bridge.ofThesis b.1) Q.ty
  iseqv := ⟨fun a => a.2.elim fun h => Refinement.refl (nativeTyping_of_thesis pe h),
    AbortEquiv.symm, Refinement.trans⟩

/-- Project an exact syntactic arrow into the hom setoid of the repaired native relation. -/
def repairedHomClass (pe : ε) {P Q : Thesis.LambdaIter.Syn.SynCat (signature (τ := τ) (Φ := Φ) pe)}
    (f : P ⟶ Q) : Quotient (repairedHomSetoid pe P Q) :=
  Quotient.map id (fun _ _ h => thesisEqv_inclusion pe h) f

/-- The repaired hom image of native abort reifies when its scrutinee already reifies
in the exact hom. This checks a single constructor step at a stronger premise. -/
theorem repairedPacked_abort_of_exact (pe : ε) {n : Nat} {β : BoundCtx τ n}
    {t : Tm Empty Φ n} (A : τ)
    (d : Derivation Φ (Ctx.nil : Ctx Empty τ) β t (empty : τ))
    (h : Thesis.LambdaIter.LocallyNameless.HasType (signature (τ := τ) (Φ := Φ) pe).Instr .nil
      (Bridge.BoundCtx.toThesis β) (Bridge.toThesis t) (empty : τ))
    (ih : packedNative pe d = packedArrow h) :
    repairedHomClass pe (packedNative pe (.abort (C := A) d)) =
      repairedHomClass pe (packedArrow (S := signature (τ := τ) (Φ := Φ) pe) (.abort (C := A) h)) := by
  let S := signature (τ := τ) (Φ := Φ) pe
  let J := values S
  let Q := of (S := S) A
  let elim : of (S := S) (empty : τ) ⟶ Q := mk (Thesis.LambdaIter.LocallyNameless.HasType.abort (C := A) Thesis.LambdaIter.LocallyNameless.HasType.newest)
  let e := J.map ((typeModel (Φ := Φ) pe).emptyIsInitial.to (valueObj pe A))
  have he : e = elim := fromEmpty_unique Q e elim
  have packed : packedNative pe (.abort (C := A) d) = packedNative pe d ≫ elim := by
    change J.map (packedEnvIso (Φ := Φ) pe β).inv ≫ denoteInSyntax pe d ≫ e = _
    rw [he]
    exact (Category.assoc _ _ _).symm
  rw [packed, ih]
  apply Quotient.sound
  exact AbortEquiv.symm (AbortEquiv.sequence (nativeTyping_of_thesis pe (packedTyping h)))

section Witness

local instance : HasTy Bool (Ty Empty) where
  src _ := .unit
  trg _ := .empty

local instance : HasEff Bool Bool where
  eff _ := true

private def unitDerivation :
    Derivation Bool (Ctx.nil : Ctx Empty (Ty Empty)) .nil .unit Ty.unit := .unit

private def unitTyping :
    Thesis.LambdaIter.LocallyNameless.HasType Bool (Thesis.LambdaIter.Ctx.nil : Thesis.LambdaIter.Ctx Empty (Ty Empty))
      .nil .unit Ty.unit := .unit

/-- The effectful closed obstruction reifies after projecting to the merged native relation. -/
theorem repairedPacked_effectful_closed_abort :
    repairedHomClass false (packedNative false
      (.abort (C := Ty.unit) (.op (f := true) unitDerivation))) =
    repairedHomClass false (packedArrow (S := signature (τ := Ty Empty) (Φ := Bool) false)
      (.abort (C := Ty.unit) (.op (f := true) unitTyping))) := by
  apply repairedPacked_abort_of_exact
  exact packedNative_op_eq_packedArrow false unitDerivation unitTyping
    (packedNative_unit_eq_packedArrow false unitTyping)

end Witness

#print axioms exactEquiv_inclusion
#print axioms thesisEqv_inclusion
#print axioms commuteAbort
#print axioms commuteAbort_bsubst
#print axioms repairedHomClass
#print axioms repairedPacked_effectful_closed_abort
#print axioms Semantics.Categorical.denote_abortEquiv_of_coherent_shared_tensor

end Silmaril.Isotope.LetIter.AbortSequenceHandoff

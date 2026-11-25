module

public import Silmaril.SSA.Thesis.SyntacticCategory.Packing.Defs
import Silmaril.Proofs.SSA.Thesis.SyntacticCategory.Packing.Reflection

/-! # Context packing and reflection in the one-variable λiter syntactic category -/

public section

universe u

namespace Silmaril.Thesis.LambdaIter.Syn.SynCat

open CategoryTheory
open LocallyNameless

variable {S : Sig.{u}}

/-- Opening a packed term with the tuple of the original context recovers the term
up to exact λiter equality. -/
theorem unpacked_packed {n : Nat} {β : BoundCtx S.Ty n}
    {t : Tm Empty S.Instr n} {A : S.Ty} (h : HasType S.Instr Ctx.nil β t A) :
    Eqv S.pureEff Ctx.nil β (unpackedTerm β (packedTerm β t)) t A :=
  unpacked_packed_proof h

/-- Packing a one-variable term opened with the tuple recovers the one-variable term. -/
theorem packed_unpacked {n : Nat} (β : BoundCtx S.Ty n)
    {t : Tm Empty S.Instr 1} {A : S.Ty}
    (h : HasType S.Instr Ctx.nil (.snoc .nil (packType β)) t A) :
    Eqv S.pureEff Ctx.nil (.snoc .nil (packType β))
      (packedTerm β (unpackedTerm β t)) t A :=
  packed_unpacked_proof β h

/-- The typed quotient in an arbitrary bound context is equivalent to the hom
from its packed product object. The inverse substitutes the tuple. -/
def packedHomEquiv {n : Nat} (β : BoundCtx S.Ty n) (A : S.Ty) :
    El S β A ≃ (of (packType β) ⟶ of A) :=
  packedHomEquiv_proof β A

/-- On representatives the equivalence computes the packed arrow. -/
@[simp] theorem packedHomEquiv_mk {n : Nat} {β : BoundCtx S.Ty n}
    {t : Tm Empty S.Instr n} {A : S.Ty} (h : HasType S.Instr Ctx.nil β t A) :
    packedHomEquiv β A (mk h) = packedArrow h := packedHomEquiv_mk_proof h

/-- With empty free context, equality of the packed syntactic arrows is equivalent to
exact λiter equality in the original bound context. -/
theorem packedArrow_eq_iff {n : Nat} {β : BoundCtx S.Ty n} {A : S.Ty}
    {t v : Tm Empty S.Instr n}
    (h : HasType S.Instr Ctx.nil β t A) (k : HasType S.Instr Ctx.nil β v A) :
    packedArrow h = packedArrow k ↔ Eqv S.pureEff Ctx.nil β t v A := by
  rw [← packedHomEquiv_mk h, ← packedHomEquiv_mk k, (packedHomEquiv β A).injective.eq_iff]
  exact ⟨Syn.eqv_of_mk_eq, Syn.mk_eq_mk h k⟩

/-- Substituting pure terms in a typed term is precomposition by their
packed context arrow. -/
theorem packedSubst_comp {n m : Nat} {β : BoundCtx S.Ty n} {γ : BoundCtx S.Ty m}
    {σ : Fin n → Tm Empty S.Instr m}
    (s : PureTypedSubst (Γ := Ctx.nil) (pureEff := S.pureEff) β γ σ)
    {t : Tm Empty S.Instr n} {A : S.Ty} (h : HasType S.Instr Ctx.nil β t A) :
    packedSubst s ≫ packedArrow h = packedArrow (h.bsubst s.typed) :=
  packedSubst_comp_proof s h

/-- The packed context arrow of a pure substitution is a syntactic value arrow. -/
theorem packedSubst_isPureMor {n m : Nat} {β : BoundCtx S.Ty n} {γ : BoundCtx S.Ty m}
    {σ : Fin n → Tm Empty S.Instr m}
    (s : PureTypedSubst (Γ := Ctx.nil) (pureEff := S.pureEff) β γ σ) :
    IsPureMor (packedSubst s) :=
  packedSubst_isPureMor_proof s

end Silmaril.Thesis.LambdaIter.Syn.SynCat

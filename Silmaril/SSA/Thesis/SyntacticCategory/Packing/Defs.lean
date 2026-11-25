module

public import Silmaril.SSA.Thesis.SyntacticCategory.Values.Thms

/-! # Packing bound contexts in the syntactic λiter category -/

@[expose] public section

universe u

namespace Silmaril.Thesis.LambdaIter.Syn.SynCat

open CategoryTheory
open LocallyNameless

variable {S : Sig.{u}}

/-- The left-associated product of the bound context, starting at unit. -/
def packType : {n : Nat} → BoundCtx S.Ty n → S.Ty
  | _, .nil => unit
  | _, .snoc β A => tensor (packType β) A

/-- The tuple of all bound variables. -/
def packTerm : {n : Nat} → BoundCtx S.Ty n → Tm Empty S.Instr n
  | _, .nil => .unit
  | _, .snoc β _ => .pair (Tm.lift (packTerm β)) (.bv 0)

/-- Read a bound slot from a term of the packed type. -/
def project {m : Nat} : {n : Nat} → (β : BoundCtx S.Ty n) →
    Tm Empty S.Instr m → Fin n → Tm Empty S.Instr m
  | _, .nil, _, i => Fin.elim0 i
  | _, .snoc β _, p, i =>
      Fin.cases (.let₂ p (.bv 0)) (fun j => project β (.let₂ p (.bv 1)) j) i

/-- Construct the typing derivation of the tuple of bound variables. -/
def packTermTyping : {n : Nat} → (β : BoundCtx S.Ty n) →
    HasType S.Instr Ctx.nil β (packTerm β) (packType β)
  | _, .nil => .unit
  | _, .snoc β _ => .pair (packTermTyping β).lift HasType.newest

/-- A projection returns the same type as the original bound slot. -/
def projectTyping {m : Nat} {γ : BoundCtx S.Ty m} :
    {n : Nat} → (β : BoundCtx S.Ty n) → {p : Tm Empty S.Instr m} →
    HasType S.Instr Ctx.nil γ p (packType β) →
    (i : Fin n) → HasType S.Instr Ctx.nil γ (project β p i) (β.get i)
  | _, .nil, _, _, i => Fin.elim0 i
  | _, .snoc β _, _, h, i =>
      Fin.cases
        (HasType.let₂ h HasType.newest)
        (fun j => projectTyping β (HasType.let₂ h (.bv (ι := 1))) j) i

/-- The term in a single bound variable of the packed type. -/
def packedTerm {n : Nat} (β : BoundCtx S.Ty n) (t : Tm Empty S.Instr n) :
    Tm Empty S.Instr 1 :=
  Tm.bsubst (project β (.bv 0)) t

/-- Packing is the pure substitution of the tuple projections for the old variables. -/
def packedTyping {n : Nat} {β : BoundCtx S.Ty n} {t : Tm Empty S.Instr n} {A : S.Ty}
    (h : HasType S.Instr Ctx.nil β t A) :
    HasType S.Instr Ctx.nil (.snoc .nil (packType β)) (packedTerm β t) A :=
  h.bsubst (projectTyping β HasType.newest)

/-- Interpret a multivariable term as a one-variable syntactic arrow. -/
def packedArrow {n : Nat} {β : BoundCtx S.Ty n} {t : Tm Empty S.Instr n} {A : S.Ty}
    (h : HasType S.Instr Ctx.nil β t A) : of (packType β) ⟶ of A :=
  mk (packedTyping h)

/-- A pure typed substitution gives an arrow from the packed target context
to the packed source context by forming the tuple of its images. -/
def packedSubst {n m : Nat} {β : BoundCtx S.Ty n} {γ : BoundCtx S.Ty m}
    {σ : Fin n → Tm Empty S.Instr m}
    (s : PureTypedSubst (Γ := Ctx.nil) (pureEff := S.pureEff) β γ σ) :
    of (packType γ) ⟶ of (packType β) :=
  packedArrow ((packTermTyping β).bsubst s.typed)

/-- Open a one-variable term with the tuple of all bound variables. -/
def unpackedTerm {n : Nat} (β : BoundCtx S.Ty n) (t : Tm Empty S.Instr 1) :
    Tm Empty S.Instr n :=
  Tm.bsubst (fun _ => packTerm β) t

end Silmaril.Thesis.LambdaIter.Syn.SynCat

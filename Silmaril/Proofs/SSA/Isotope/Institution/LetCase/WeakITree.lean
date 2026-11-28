module

public import Silmaril.SSA.Isotope.Institution.LetCase.WeakITree.Defs

public section

namespace Silmaril.Proofs.SSA.Isotope.Institution.LetCase.WeakITree

open CategoryTheory
open Silmaril.Logic.Metatheory.TheoryModel (Algebra)
open Silmaril.Isotope (BoundCtx)
open _root_.Silmaril.Isotope.Institution (castOp)
open _root_.Silmaril.Isotope.Institution.LetCase.WeakITree
open Silmaril.Isotope.Theory (TypingIndex)
open Silmaril.Isotope.LetCase.LocallyNameless
open Silmaril.Isotope.Semantics (BoundEnv)
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed (AtomValues ModelTree)
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed.Ordered

universe u

variable {κ : Type (u + 1)} [AtomValues κ] {Events : Type u → Type u}
  {P Q : FlatInstitution.Signature.{u, u+1} κ}

local notation "D" => Ty.denote (AtomValues.carrier (κ := κ))
local notation "Γ₀" => (emptyContext (κ := κ))

theorem denote_closedOperand (M : Model (κ := κ) Events P.Instr)
    {n : Nat} {β : BoundCtx (Ty κ) n} {t : Tm Empty P.Instr n} {A : Ty κ}
    (d : Derivation P.Instr .nil β t A) :
    Models.denote (algebra (P := P) M) (closedOperand (P := P) d).2 =
      d.denote D ⟨M.instructions.denote⟩ (fun x => x.elim) := by
  induction d with
  | @fv _ _ x _ _ => exact x.elim
  | bv | unit => rfl
  | op _ ih | inl _ ih | inr _ ih | abort _ ih =>
    simp only [closedOperand, Models.denote, Derivation.denote, ← ih]
    rfl
  | let₁ _ _ ih₁ ih₂ | let₂ _ _ ih₁ ih₂ | pair _ _ ih₁ ih₂ =>
    simp only [closedOperand, Models.denote, Derivation.denote, ← ih₁, ← ih₂]
    rfl
  | case _ _ _ ihe ihl ihr =>
    simp only [closedOperand, Models.denote, Derivation.denote, ← ihe, ← ihl, ← ihr]
    funext env
    change (_ >>= _) = (_ >>= _)
    congr 1
    funext reply
    cases reply <;> rfl

private theorem reduct_op (M : Model (κ := κ) Events Q.Instr)
    {n : Nat} {β : BoundCtx (Ty κ) n} {A B : Ty κ} (f : Q.Instr)
    (ht : instrTrg f = A) (hs : instrSrc f = B)
    (a : Arrow Events ⟨n, β, B⟩)
    (args : (j : Fin ((Models.signature Q.Instr Γ₀).arity
      (castOp (Models.signature Q.Instr Γ₀)
        (congrArg (fun A => (⟨n, β, A⟩ : TypingIndex (Ty κ))) ht) (Models.Operation.op f)))) →
      (algebra (P := Q) M).Carrier ((Models.signature Q.Instr Γ₀).argSort
        (castOp (Models.signature Q.Instr Γ₀)
          (congrArg (fun A => (⟨n, β, A⟩ : TypingIndex (Ty κ))) ht) (Models.Operation.op f)) j))
    (hargs : ∀ j, HEq (args j) a) :
    (algebra (P := Q) M).op
      (castOp (Models.signature Q.Instr Γ₀)
        (congrArg (fun A => (⟨n, β, A⟩ : TypingIndex (Ty κ))) ht) (Models.Operation.op f)) args =
      fun env => a env >>= fun x =>
        cast (congrArg (fun T => ModelTree Events (D T)) ht)
          (M.instructions.denote f (cast (congrArg D hs).symm x)) := by
  subst A
  subst B
  change (fun env => args (0 : Fin 1) env >>= M.instructions.denote f) = _
  rw [eq_of_heq (hargs (0 : Fin 1))]
  rfl

theorem algebra_reduct (g : P ⟶ Q) (effects : g.toSignatureMap.eff = id)
    (M : Model (κ := κ) Events Q.Instr) :
    Algebra.reductObj (_root_.Silmaril.Isotope.Institution.LetCase.sigHom Γ₀ (signatureHom g effects)) (algebra (P := Q) M) =
      algebra (P := P) (FlatInstitution.reduct Events g M) := by
  unfold Algebra.reductObj
  congr 1
  funext i o args
  cases o with
  | op f =>
      let hom := signatureHom g effects
      refine reduct_op M (hom.instr f) (hom.target f) (hom.source f) (args 0) _
        (fun j => (eqRec_heq _ _).trans ?_)
      let k : Fin 1 := (_root_.Silmaril.Isotope.Institution.LetCase.sigHom Γ₀ hom).arg (.op f) j
      change HEq (args k) (args (0 : Fin 1))
      rw [Fin.eq_zero k]
  | fv | bv | let₁ | unit | pair | let₂ | inl | inr | case | abort => rfl

end Silmaril.Proofs.SSA.Isotope.Institution.LetCase.WeakITree

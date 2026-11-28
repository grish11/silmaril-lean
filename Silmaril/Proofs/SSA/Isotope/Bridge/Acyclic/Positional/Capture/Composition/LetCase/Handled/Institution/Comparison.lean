module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Renaming.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.Sentence.Defs
import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.TypeChange.LetCase.Thms

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

open CategoryTheory
open Silmaril.Isotope.Institution (InstrSig)
open Silmaril.Isotope.Institution.Acyclic (CaseEquation mapOperand mapCaseSignature typeCaseHom
  typeCaseHom_translate typeCaseHom_primitive)
open LetCase.LocallyNameless (Derivation)
open LetCase.Structural.Finite (Context)
open LetCase.Structural.Reply (Γ₀)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

section Primitive

variable {τ ε : Type} [TypeFormers τ] {P Q : InstrSig τ ε}

/-- The type-changing sentence map at a relabelling is the sentence map of
the existing LetCase institution, with the typing index unchanged. -/
theorem mapCaseSignature_primitive_proof (f : P ⟶ Q) (e : CaseEquation P) :
    mapCaseSignature f.toSignatureMap e = ⟨e.1, mapOperand f e.2.1, mapOperand f e.2.2⟩ := by
  rw [← typeCaseHom_translate, typeCaseHom_primitive]
  rfl

end Primitive

variable {Φ Ψ : Type} [LetCase.Structural.Finite.Signature Ψ] (r : Φ → Ψ)

/-- The existing fold of the LetCase institution is the structural renaming. -/
theorem mapOperand_pulled_proof {n : Nat} {γ : Context n} {t : LetCase.LocallyNameless.Tm Empty (Pulled r) n}
    {A : Ty Empty} (d : Derivation (Pulled r) Γ₀ γ t A) :
    mapOperand (pulledHom r) (⟨t, d⟩ : Operand (Pulled r) γ A) = renameOperand r ⟨t, d⟩ := by
  induction d with
  | fv h => rename_i x _; exact x.elim
  | bv => rfl
  | unit => rfl
  | op ha ih =>
    exact congrArg (fun x : Operand Ψ _ _ => (⟨.op _ x.1, .op x.2⟩ : Operand Ψ _ _)) ih
  | let₁ ha hb iha ihb =>
    exact congrArg₂ (fun (x : Operand Ψ _ _) (y : Operand Ψ _ _) =>
      (⟨.let₁ x.1 y.1, .let₁ x.2 y.2⟩ : Operand Ψ _ _)) iha ihb
  | pair ha hb iha ihb =>
    exact congrArg₂ (fun (x : Operand Ψ _ _) (y : Operand Ψ _ _) =>
      (⟨.pair x.1 y.1, .pair x.2 y.2⟩ : Operand Ψ _ _)) iha ihb
  | let₂ ha hc iha ihc =>
    exact congrArg₂ (fun (x : Operand Ψ _ _) (y : Operand Ψ _ _) =>
      (⟨.let₂ x.1 y.1, .let₂ x.2 y.2⟩ : Operand Ψ _ _)) iha ihc
  | inl ha ih =>
    exact congrArg (fun x : Operand Ψ _ _ => (⟨.inl x.1, .inl x.2⟩ : Operand Ψ _ _)) ih
  | inr ha ih =>
    exact congrArg (fun x : Operand Ψ _ _ => (⟨.inr x.1, .inr x.2⟩ : Operand Ψ _ _)) ih
  | case he hl hr ihe ihl ihr =>
    refine (congrArg₂ (fun (x : Operand Ψ _ _) (y : Operand Ψ _ _) =>
      (⟨.case x.1 y.1 (mapOperand (pulledHom r) ⟨_, hr⟩).1,
        .case x.2 y.2 (mapOperand (pulledHom r) ⟨_, hr⟩).2⟩ : Operand Ψ _ _)) ihe ihl).trans ?_
    exact congrArg (fun z : Operand Ψ _ _ =>
      (⟨.case _ _ z.1, .case (renameDerivation r he) (renameDerivation r hl) z.2⟩ : Operand Ψ _ _)) ihr
  | abort ha ih =>
    exact congrArg (fun x : Operand Ψ _ _ => (⟨.abort x.1, .abort x.2⟩ : Operand Ψ _ _)) ih

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

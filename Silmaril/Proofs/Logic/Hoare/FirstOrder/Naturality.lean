module

public import Silmaril.Logic.Hoare.FirstOrder.Signatures

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Proofs.Logic.Hoare.FirstOrder
open CategoryTheory Silmaril.Logic.Institution.Examples
open Silmaril.Logic
open Silmaril.Logic.Hoare.FirstOrder
variable {S : Type} {A B : FixedSignature S}

/-- Canonical store frames commute exactly with every admitted symbol map. -/
theorem native_reduct (f : A ⟶ B) (M : FOL.Structure B.fol) :
    native ((FOL.Structure.reduct f.fol).obj M) = ModalMu.reduct (languageMap f) (native M) := by
  apply congrArg (fun v : Atom A.fol → Set (Store M) =>
    @ModalMu.Model.mk (language A.fol) (Store M) (havoc M) v (empty M))
  funext a
  apply Set.ext
  intro h
  cases a with
  | eq Γ t u =>
      change (∃ ρ, Encodes _ Γ ρ h ∧ _) ↔ (∃ ρ, Encodes M Γ ρ h ∧ _)
      apply exists_congr
      intro ρ
      exact and_congr Iff.rfl (Iff.of_eq (congrArg₂ Eq
        (EQ.Term.eval_map f.fol.toHom M.toAlgebra ρ t)
        (EQ.Term.eval_map f.fol.toHom M.toAlgebra ρ u)).symm)
  | rel Γ r args =>
      change (∃ ρ, Encodes _ Γ ρ h ∧ _) ↔ (∃ ρ, Encodes M Γ ρ h ∧ _)
      apply exists_congr
      intro ρ
      exact and_congr Iff.rfl (Iff.of_eq (congrArg (M.rel (f.relations r))
        (funext fun j => EQ.Term.eval_map f.fol.toHom M.toAlgebra ρ (args j))).symm)

theorem compile_naturality (f : A ⟶ B) {k} {Γ : Fin k → A.fol.S} (φ : FOL.Formula A.fol Γ) :
    (compile φ).map (languageMap f) = compile (φ.map f.fol) := by
  induction φ with
  | eq => rfl
  | rel => rfl
  | tt => rfl
  | not φ ih => exact congrArg PDL.Formula.neg ih
  | and φ ψ hp hq => exact congrArg₂ PDL.Formula.conj hp hq
  | all hc φ ih => exact congrArg (PDL.Formula.box (.action _)) ih

theorem sentence_naturality (f : A ⟶ B) (φ : FOL.Sentence A.fol) :
    (sentence φ).map (Command S) (nativeSignatureMap f) = sentence (φ.map f.fol) :=
  congrArg (fun p : PDL.Formula (language B.fol) =>
    (⟨none,truth,p⟩ : Hoare.Triple (Command S) (signature B.fol))) (compile_naturality f φ.formula)


end Silmaril.Proofs.Logic.Hoare.FirstOrder

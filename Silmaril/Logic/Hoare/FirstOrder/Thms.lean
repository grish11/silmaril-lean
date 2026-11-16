module

public import Silmaril.Logic.Hoare.FirstOrder.Defs
import Silmaril.Proofs.Logic.Hoare.FirstOrder.Compiler

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Hoare.FirstOrder
open Silmaril.Logic.Institution.Examples
variable {A : FOL.Signature}

/-- Primitive open compilation agrees with actual FOL evaluation on every encoding store. -/
theorem compile_correct (M : FOL.Structure A) {k} {Γ : Fin k → A.S}
    (φ : FOL.Formula A Γ) (ρ : ∀ i, M.carrier (Γ i)) (h : Store M)
    (hh : Encodes M Γ ρ h) :
    (compile φ).Holds (native M) h ↔ φ.Holds M ρ :=
  Silmaril.Proofs.Logic.Hoare.FirstOrder.compile_correct M φ ρ h hh

theorem closed_correct (M : FOL.Structure A) (φ : FOL.Sentence A) (h : Store M) :
    (compile φ.formula).Holds (native M) h ↔ φ.Holds M :=
  Silmaril.Proofs.Logic.Hoare.FirstOrder.closed_correct M φ h

theorem sentence_correct (M : FOL.Structure A) (φ : FOL.Sentence A) :
    (sentence φ).Satisfies (Command A.S) (native M) ↔ φ.Holds M :=
  Silmaril.Proofs.Logic.Hoare.FirstOrder.sentence_correct M φ

end Silmaril.Logic.Hoare.FirstOrder

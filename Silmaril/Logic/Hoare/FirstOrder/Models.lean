module

public import Silmaril.Logic.Hoare.FirstOrder.Signatures
import Silmaril.Proofs.Logic.Hoare.FirstOrder.Naturality

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Hoare.FirstOrder
open CategoryTheory Silmaril.Logic.Institution.Examples
variable {S : Type} {A B : FixedSignature S}

/-- Actual native PDL frames commute with every admitted fixed-sort symbol map. -/
theorem native_reduct (f : A ⟶ B) (M : FOL.Structure B.fol) :
    native ((FOL.Structure.reduct f.fol).obj M) = ModalMu.reduct (languageMap f) (native M) :=
  Silmaril.Proofs.Logic.Hoare.FirstOrder.native_reduct f M

theorem compile_naturality (f : A ⟶ B) {k} {Γ : Fin k → A.fol.S} (φ : FOL.Formula A.fol Γ) :
    (compile φ).map (languageMap f) = compile (φ.map f.fol) :=
  Silmaril.Proofs.Logic.Hoare.FirstOrder.compile_naturality f φ

theorem sentence_naturality (f : A ⟶ B) (φ : FOL.Sentence A.fol) :
    (sentence φ).map (Command S) (nativeSignatureMap f) = sentence (φ.map f.fol) :=
  Silmaril.Proofs.Logic.Hoare.FirstOrder.sentence_naturality f φ

end Silmaril.Logic.Hoare.FirstOrder

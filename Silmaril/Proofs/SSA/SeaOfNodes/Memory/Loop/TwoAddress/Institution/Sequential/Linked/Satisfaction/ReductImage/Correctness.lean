module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImageProofs

open CategoryTheory
open RVSDG (Tuple)
open Memory.Diamond.Institution (reduct reduct_comp reduct_id)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

variable {P Q R : EntrySignature} {cells : Nat}

theorem forall_reduct_image (h : P ⟶ Q) (holds : EntryModel P → Prop) :
    (∀ input : Tuple (Val cells) Q.args, holds (reduct h ⟨cells, input⟩)) ↔
      ∀ input : Tuple (Val cells) P.args, InReductImage h input → holds ⟨cells, input⟩ := by
  constructor
  · rintro all _ ⟨input, equal⟩
    exact equal ▸ all input
  · intro all input
    exact all (reduct h ⟨cells, input⟩).input ⟨input, rfl⟩

theorem in_image_comp (h : P ⟶ Q) (k : Q ⟶ R) (input : Tuple (Val cells) P.args) :
    InReductImage (h ≫ k) input ↔
      ∃ between : Tuple (Val cells) Q.args, InReductImage k between ∧ reduct h ⟨cells, between⟩ = ⟨cells, input⟩ := by
  constructor
  · rintro ⟨last, equal⟩
    exact ⟨(reduct k ⟨cells, last⟩).input, ⟨last, rfl⟩, (reduct_comp h k ⟨cells, last⟩).symm.trans equal⟩
  · rintro ⟨between, ⟨last, lastEq⟩, equal⟩
    exact ⟨last, (reduct_comp h k ⟨cells, last⟩).trans ((congrArg (reduct h) lastEq).trans equal)⟩

theorem in_image_of_retraction (h : P ⟶ Q) (back : Q ⟶ P) (split : h ≫ back = 𝟙 P)
    (input : Tuple (Val cells) P.args) : InReductImage h input := by
  refine ⟨(reduct back ⟨cells, input⟩).input, ?_⟩
  exact (reduct_comp h back ⟨cells, input⟩).symm.trans
    ((congrArg (fun ports => reduct ports (⟨cells, input⟩ : EntryModel P)) split).trans (reduct_id _))

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImageProofs

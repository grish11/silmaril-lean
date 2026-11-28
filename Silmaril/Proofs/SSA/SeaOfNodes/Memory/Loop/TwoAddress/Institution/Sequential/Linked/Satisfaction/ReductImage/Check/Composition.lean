module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.Check.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.Check.Lift
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.Proofs

open CategoryTheory
open CarriedAddress.Institution.RuntimeEntry (Entry)
open Memory.Diamond.Institution (pullInput reduct reduct_comp)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

variable {P Q R : EntrySignature} {cells : Nat}

theorem liftThrough?_sound (h : P ⟶ Q) (k : Q ⟶ R) {entry : Entry P.args cells}
    {between : Entry Q.args cells} {target : Entry R.args cells}
    (lifted : liftThrough? h k entry = some (between, target)) :
    between.reduct h = entry ∧ target.reduct k = between := by
  obtain ⟨input, checked, equal⟩ := Option.map_eq_some_iff.mp lifted
  cases equal
  refine ⟨?_, rfl⟩
  have pulled := (reduct_comp h k ⟨cells, input⟩).symm.trans (liftInput?_sound (h ≫ k) checked)
  have values : pullInput h.port (pullInput k.port input) = entry.input := by
    simpa only [reduct, EntryModel.mk.injEq, heq_eq_eq, true_and] using pulled
  exact congrArg (fun values => Entry.mk values entry.heap) values

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.Proofs

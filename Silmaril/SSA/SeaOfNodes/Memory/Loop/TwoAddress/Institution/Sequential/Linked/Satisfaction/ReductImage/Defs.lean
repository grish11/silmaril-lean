module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.Defs

/-! The typed valuation image at a fixed initialized cell count. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction

open CategoryTheory
open RVSDG (Tuple)
open Memory.Diamond.Institution (reduct)
open Memory.Diamond.Institution renaming Signature → EntrySignature

variable {P Q : EntrySignature} {cells : Nat}

/-- The source input occurs as the reduct of a target input at this cell count. -/
def InReductImage (h : P ⟶ Q) (input : Tuple (Val cells) P.args) : Prop :=
  ∃ targetInput : Tuple (Val cells) Q.args, reduct h ⟨cells, targetInput⟩ = ⟨cells, input⟩

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction

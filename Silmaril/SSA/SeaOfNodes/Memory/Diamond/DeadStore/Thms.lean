module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Defs
import Silmaril.SSA.SeaOfNodes.Diamond.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore

open RVSDG (Tuple)
open SeaOfNodes.Diamond (Projection Slot)

variable {args : List ValueSort} {cells : Nat}
variable {source : Prefixed args} {rewritten : Graph args} {candidate : Candidate args}

theorem PrefixStore.prepend_denote (store : PrefixStore args) (arm : Memory.Graph args)
    (input : Tuple (Val cells) args) (initial : Heap cells) :
    (store.prepend arm).denote input initial = arm.denote input (store.table.denote input initial).2 :=
  Proofs.prepend_denote store arm input initial

theorem Prefixed.returns_iff_denote (source : Prefixed args) (guard : Bool) (input : Tuple (Val cells) args)
    (initial : Heap cells) (word : Word) (final : Heap cells) :
    source.Returns guard input initial word final ↔ source.denote guard input initial = (word, final) :=
  Proofs.returns_iff_denote source guard input initial word final

/-- Each target arm comes from its own checked Region occurrence. -/
theorem rewrite_occurrence (input : Tuple (Val cells) args)
    (success : rewrite source candidate input = some rewritten) (arrival : Slot) :
    rewriteSlot source candidate input arrival = some (rewritten.arm (source.diamond.merge.predecessor arrival)) :=
  Proofs.rewrite_occurrence input success arrival

/-- The all-path cut keeps the Region ordering and the shared suffix. -/
theorem rewrite_shape (input : Tuple (Val cells) args)
    (success : rewrite source candidate input = some rewritten) :
    rewritten.merge = source.diamond.merge ∧ rewritten.suffix = source.diamond.suffix :=
  Proofs.rewrite_shape input success

/-- A checked path exports the same packet and reads the same Loads when
the common entry Store is bypassed. -/
theorem rewriteArm_observations {store : PrefixStore args} {arm edited : Memory.Graph args}
    {witness : ArmOverwrite args} (input : Tuple (Val cells) args)
    (success : rewriteArm store arm witness input = some edited) (initial : Heap cells) :
    let entered := (store.table.denote input initial).2
    edited.denote input initial = arm.denote input entered ∧
      ∀ index, Memory.DeadStore.readAt edited index input PUnit.unit initial =
        Memory.DeadStore.readAt arm index input PUnit.unit entered :=
  Proofs.rewriteArm_observations input success initial

/-- At each checked occurrence the two arm executions agree on all Loads
and on the exact exported word and heap, with the entry Store run only
in the original. -/
theorem rewrite_arm_observations (input : Tuple (Val cells) args)
    (success : rewrite source candidate input = some rewritten) (arrival : Slot) (initial : Heap cells) :
    let edge := source.diamond.merge.predecessor arrival
    let entered := (source.store.table.denote input initial).2
    (rewritten.arm edge).denote input initial = (source.diamond.arm edge).denote input entered ∧
      ∀ index, Memory.DeadStore.readAt (rewritten.arm edge) index input PUnit.unit initial =
        Memory.DeadStore.readAt (source.diamond.arm edge) index input PUnit.unit entered :=
  rewriteArm_observations input (rewrite_occurrence input success arrival) initial

/-- Each Region slot latches the same packet from the arrival, or sees
no publication at that slot in both executions. -/
theorem rewrite_latch (input : Tuple (Val cells) args)
    (success : rewrite source candidate input = some rewritten) (edge : Projection) (slot : Slot)
    (initial : Heap cells) :
    let entered := (source.store.table.denote input initial).2
    latch rewritten.merge slot (publish edge ((rewritten.arm edge).denote input initial)) =
      latch source.diamond.merge slot (publish edge ((source.diamond.arm edge).denote input entered)) := by
  have packet := (rewrite_arm_observations input success (source.diamond.merge.slot edge) initial).1
  simp only [source.diamond.merge.predecessor_slot] at packet
  rw [(rewrite_shape input success).1, packet]

/-- The unchanged suffix observes the same Loads after the selected arm. -/
theorem rewrite_suffix_reads (input : Tuple (Val cells) args)
    (success : rewrite source candidate input = some rewritten) (guard : Bool) (index : Nat)
    (initial : Heap cells) :
    let edge := Projection.ofBool guard
    let before := (source.diamond.arm edge).denote input (source.store.table.denote input initial).2
    let after := (rewritten.arm edge).denote input initial
    Memory.DeadStore.readAt rewritten.suffix index (.cons after.1 input) PUnit.unit after.2 =
      Memory.DeadStore.readAt source.diamond.suffix index (.cons before.1 input) PUnit.unit before.2 := by
  have packet := (rewrite_arm_observations input success (source.diamond.merge.slot (Projection.ofBool guard)) initial).1
  simp only [source.diamond.merge.predecessor_slot] at packet
  simp only [(rewrite_shape input success).2, packet]

theorem rewrite_denote (input : Tuple (Val cells) args)
    (success : rewrite source candidate input = some rewritten) (guard : Bool) (initial : Heap cells) :
    rewritten.denote guard input initial = source.denote guard input initial :=
  Proofs.rewrite_denote input success guard initial

/-- Both guard choices preserve and reflect the returned word and whole heap. -/
theorem rewrite_returns_iff (input : Tuple (Val cells) args)
    (success : rewrite source candidate input = some rewritten) (guard : Bool) (initial : Heap cells)
    (word : Word) (final : Heap cells) :
    rewritten.Returns guard input initial word final ↔ source.Returns guard input initial word final := by
  rw [rewritten.returns_iff_denote, source.returns_iff_denote, rewrite_denote input success]

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore

module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Defs
import Silmaril.SSA.SeaOfNodes.Diamond.Thms
import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Proofs

open RVSDG (Tuple)
open SeaOfNodes.Diamond (Projection Slot)

variable {args : List ValueSort} {cells : Nat}
variable {source : Prefixed args} {rewritten : Graph args} {candidate : Candidate args}

theorem prepend_denote (store : PrefixStore args) (arm : Memory.Graph args)
    (input : Tuple (Val cells) args) (initial : Heap cells) :
    (store.prepend arm).denote input initial = arm.denote input (store.table.denote input initial).2 :=
  Memory.DeadStore.reindexMemory_denote arm 1 input PUnit.unit _

private theorem prepend_readAt (store : PrefixStore args) (arm : Memory.Graph args) (index : Nat)
    (input : Tuple (Val cells) args) (initial : Heap cells) :
    Memory.DeadStore.readAt (store.prepend arm) index input PUnit.unit initial =
      Memory.DeadStore.readAt arm index input PUnit.unit (store.table.denote input initial).2 := by
  exact (Memory.DeadStore.readAt_store (.latest 0) (.arg store.address) (.arg store.value)
    (Memory.DeadStore.reindexMemory arm 1) index input PUnit.unit initial).trans
    (Memory.DeadStore.reindexMemory_readAt arm 1 index input PUnit.unit _)

theorem returns_iff_denote (source : Prefixed args) (guard : Bool) (input : Tuple (Val cells) args)
    (initial : Heap cells) (word : Word) (final : Heap cells) :
    source.Returns guard input initial word final ↔ source.denote guard input initial = (word, final) := by
  simp only [Prefixed.Returns, Memory.Graph.returns_iff_denote, Graph.returns_iff_denote, Prefixed.denote]
  constructor
  · rintro ⟨_, _, entry, taken⟩
    rw [entry]
    exact taken
  · intro observed
    exact ⟨_, _, rfl, observed⟩

private theorem rewrite_result (input : Tuple (Val cells) args)
    (success : rewrite source candidate input = some rewritten) :
    rewritten.merge = source.diamond.merge ∧ rewritten.suffix = source.diamond.suffix ∧
      ∀ arrival, rewriteSlot source candidate input arrival =
        some (rewritten.arm (source.diamond.merge.predecessor arrival)) := by
  obtain ⟨first, firstAccepted, afterFirst⟩ := Option.bind_eq_some_iff.mp success
  obtain ⟨second, secondAccepted, returned⟩ := Option.bind_eq_some_iff.mp afterFirst
  cases Option.some.inj returned
  refine ⟨rfl, rfl, fun arrival => ?_⟩
  change rewriteSlot source candidate input arrival = some (match
      source.diamond.merge.slot (source.diamond.merge.predecessor arrival) with
    | .first => first
    | .second => second)
  rw [source.diamond.merge.slot_predecessor]
  cases arrival
  · exact firstAccepted
  · exact secondAccepted

theorem rewrite_occurrence (input : Tuple (Val cells) args)
    (success : rewrite source candidate input = some rewritten) (arrival : Slot) :
    rewriteSlot source candidate input arrival = some (rewritten.arm (source.diamond.merge.predecessor arrival)) :=
  (rewrite_result input success).2.2 arrival

theorem rewrite_shape (input : Tuple (Val cells) args)
    (success : rewrite source candidate input = some rewritten) :
    rewritten.merge = source.diamond.merge ∧ rewritten.suffix = source.diamond.suffix :=
  let checked := rewrite_result input success
  ⟨checked.1, checked.2.1⟩

theorem rewriteArm_observations {store : PrefixStore args} {arm edited : Memory.Graph args}
    {witness : ArmOverwrite args} (input : Tuple (Val cells) args)
    (success : rewriteArm store arm witness input = some edited) (initial : Heap cells) :
    let entered := (store.table.denote input initial).2
    edited.denote input initial = arm.denote input entered ∧
      ∀ index, Memory.DeadStore.readAt edited index input PUnit.unit initial =
        Memory.DeadStore.readAt arm index input PUnit.unit entered := by
  obtain ⟨checked, valid⟩ := (Memory.DeadStore.rewrite_eq_some_iff input).mp success
  obtain ⟨result, reads⟩ := Memory.DeadStore.rewriteWith_observations checked input valid initial
  exact ⟨result.trans (prepend_denote store arm input initial),
    fun index => (reads index).trans (prepend_readAt store arm index input initial)⟩

theorem rewrite_denote (input : Tuple (Val cells) args)
    (success : rewrite source candidate input = some rewritten) (guard : Bool) (initial : Heap cells) :
    rewritten.denote guard input initial = source.denote guard input initial := by
  have suffix := (rewrite_shape input success).2
  let arrival := source.diamond.merge.slot (Projection.ofBool guard)
  have same := (rewriteArm_observations input (rewrite_occurrence input success arrival) initial).1
  dsimp only [arrival] at same
  rw [source.diamond.merge.predecessor_slot] at same
  simp only [Graph.denote, Prefixed.denote, suffix, same]

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Proofs

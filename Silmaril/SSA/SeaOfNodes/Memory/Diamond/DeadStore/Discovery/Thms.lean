module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery

open RVSDG (Tuple)
open SeaOfNodes.Diamond (Slot)

variable {args : List ValueSort} {cells : Nat}
variable {source : Prefixed args} {result : Result args}

/-- Each witness is inferred from its own occurrence. The existing checker
accepts the pair and produces exactly the returned graph. -/
theorem rewrite_checked (input : Tuple (Val cells) args) (success : rewrite source input = some result) :
    (∀ arrival, discoverSlot source arrival = some (result.candidate arrival)) ∧
      DeadStore.rewrite source result.candidate input = some result.graph :=
  Proofs.rewrite_checked input success

/-- Both checked arm replacements preserve the original Region slot order. -/
theorem rewrite_merge (input : Tuple (Val cells) args) (success : rewrite source input = some result) :
    result.graph.merge = source.diamond.merge :=
  Proofs.rewrite_merge input success

theorem rewrite_occurrence (input : Tuple (Val cells) args)
    (success : rewrite source input = some result) (arrival : Slot) :
    rewriteSlot source result.candidate input arrival =
      some (result.graph.arm (source.diamond.merge.predecessor arrival)) :=
  DeadStore.rewrite_occurrence input (rewrite_checked input success).2 arrival

theorem rewrite_denote (input : Tuple (Val cells) args)
    (success : rewrite source input = some result) (guard : Bool) (initial : Heap cells) :
    result.graph.denote guard input initial = source.denote guard input initial :=
  DeadStore.rewrite_denote input (rewrite_checked input success).2 guard initial

/-- One successful check preserves and reflects the word and whole heap
for either guard at the checked scalar input and any initial heap. -/
theorem rewrite_returns_iff (input : Tuple (Val cells) args)
    (success : rewrite source input = some result) (guard : Bool) (initial : Heap cells)
    (word : Word) (final : Heap cells) :
    result.graph.Returns guard input initial word final ↔ source.Returns guard input initial word final :=
  DeadStore.rewrite_returns_iff input (rewrite_checked input success).2 guard initial word final

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery

module

public import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Defs
import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection

open RVSDG (Tuple)
open Memory.Forwarding.Disjoint (Certificate)

variable {args : List ValueSort} {cells : Nat}
variable {graph : Graph args} {certificates : List (Certificate args)} {result : Result args}

/-- The selected version belongs to the original table. Its overwrite is
the one discovered by the nominated search, and the existing checker
accepts both versions on this input. -/
theorem rewrite_checked (input : Tuple (Val cells) args)
    (success : rewrite graph certificates input = some result) :
    result.candidate.removeVersion ∈ storeVersions graph ∧
      result.facts ∈ certificates ∧
      Search.discover graph result.candidate.removeVersion result.facts = some result.candidate ∧
      Memory.DeadStore.rewrite graph result.candidate result.facts input = some result.graph :=
  Proofs.rewrite_checked input success

theorem rewrite_denote (input : Tuple (Val cells) args)
    (success : rewrite graph certificates input = some result) (initial : Heap cells) :
    result.graph.denote input initial = graph.denote input initial := by
  have accepted := (rewrite_checked input success).2.2.2
  obtain ⟨structural, valid⟩ := (Memory.DeadStore.rewrite_eq_some_iff input).mp accepted
  exact Memory.DeadStore.rewriteWith_denote structural input valid initial

/-- Selection preserves and reflects the returned word and the whole final heap. -/
theorem rewrite_returns_iff (input : Tuple (Val cells) args)
    (success : rewrite graph certificates input = some result)
    (initial : Heap cells) (word : Word) (final : Heap cells) :
    result.graph.Returns input initial word final ↔ graph.Returns input initial word final :=
  Memory.DeadStore.rewrite_returns_iff input (rewrite_checked input success).2.2.2 initial word final

end Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection

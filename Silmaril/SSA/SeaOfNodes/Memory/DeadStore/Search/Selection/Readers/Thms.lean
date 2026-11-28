module

public import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Defs
import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers

open RVSDG (Tuple)

variable {args : List ValueSort} {cells : Nat}
variable {graph : Graph args} {result : Selection.Result args}

/-- Success supplies the inferred certificate and the graph produced by the
existing checked rewrite on the original Store versions. -/
theorem rewrite_checked (input : Tuple (Val cells) args)
    (success : rewrite graph input = some result) :
    result.candidate.removeVersion ∈ Selection.storeVersions graph ∧
      discover graph result.candidate.removeVersion = some result.facts ∧
      Search.discover graph result.candidate.removeVersion result.facts = some result.candidate ∧
      Memory.DeadStore.rewrite graph result.candidate result.facts input = some result.graph :=
  Proofs.rewrite_checked input success

theorem rewrite_denote (input : Tuple (Val cells) args)
    (success : rewrite graph input = some result) (initial : Heap cells) :
    result.graph.denote input initial = graph.denote input initial := by
  have accepted := (rewrite_checked input success).2.2.2
  obtain ⟨structural, valid⟩ := (Memory.DeadStore.rewrite_eq_some_iff input).mp accepted
  exact Memory.DeadStore.rewriteWith_denote structural input valid initial

/-- The inferred rewrite preserves and reflects the returned word and the whole heap. -/
theorem rewrite_returns_iff (input : Tuple (Val cells) args)
    (success : rewrite graph input = some result)
    (initial : Heap cells) (word : Word) (final : Heap cells) :
    result.graph.Returns input initial word final ↔ graph.Returns input initial word final :=
  Memory.DeadStore.rewrite_returns_iff input (rewrite_checked input success).2.2.2 initial word final

end Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers

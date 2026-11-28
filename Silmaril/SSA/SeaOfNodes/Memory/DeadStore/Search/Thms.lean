module

public import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Defs
import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.DeadStore.Search.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search

open RVSDG (Tuple)
open Memory.Forwarding.Disjoint (Certificate)

variable {args : List ValueSort} {cells : Nat}
variable {graph rewritten : Graph args} {removeVersion : Nat} {facts : Certificate args}

/-- Discovery supplies a strictly later overwrite accepted by the
existing structural checker. Concrete cell inequality is checked separately. -/
theorem discover_sound {candidate : Candidate}
    (found : discover graph removeVersion facts = some candidate) :
    candidate.removeVersion = removeVersion ∧ removeVersion < candidate.overwriteVersion ∧
      ∃ rewritten, Memory.DeadStore.rewriteWith graph candidate facts = some rewritten :=
  Proofs.discover_sound found

theorem rewrite_denote (input : Tuple (Val cells) args)
    (success : rewrite graph removeVersion facts input = some rewritten) (heap : Heap cells) :
    rewritten.denote input heap = graph.denote input heap := by
  obtain ⟨_, _, accepted⟩ := Option.bind_eq_some_iff.mp success
  obtain ⟨structural, valid⟩ := (Memory.DeadStore.rewrite_eq_some_iff input).mp accepted
  exact Memory.DeadStore.rewriteWith_denote structural input valid heap

/-- The invocation-checked search preserves and reflects the returned
word and entire final heap. -/
theorem rewrite_returns_iff (input : Tuple (Val cells) args)
    (success : rewrite graph removeVersion facts input = some rewritten)
    (initial : Heap cells) (word : Word) (final : Heap cells) :
    rewritten.Returns input initial word final ↔ graph.Returns input initial word final := by
  obtain ⟨_, _, accepted⟩ := Option.bind_eq_some_iff.mp success
  exact Memory.DeadStore.rewrite_returns_iff input accepted initial word final

end Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search

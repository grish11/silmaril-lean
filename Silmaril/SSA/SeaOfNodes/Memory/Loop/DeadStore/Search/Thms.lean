module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.DeadStore.Search.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Loop.DeadStore.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.DeadStore.Search

open RVSDG (Tuple)
open Memory.DeadStore (Candidate)
open Memory.Forwarding.Disjoint (Certificate)

variable {args : List ValueSort} {cells : Nat}
variable {graph rewritten : Graph args} {removeVersion : Nat} {facts : Certificate args}

private theorem accepted (input : Tuple (Val cells) args)
    (success : rewrite graph removeVersion facts input = some rewritten) :
    ∃ candidate : Candidate, Loop.DeadStore.rewriteWith graph candidate facts = some rewritten ∧
      facts.Valid input := by
  obtain ⟨candidate, _, checked⟩ := Option.bind_eq_some_iff.mp success
  exact ⟨candidate, (Loop.DeadStore.rewrite_eq_some_iff input).mp checked⟩

theorem rewrite_body_denote (input : Tuple (Val cells) args)
    (success : rewrite graph removeVersion facts input = some rewritten) (heap : Heap cells) :
    rewritten.body.denote input heap = graph.body.denote input heap := by
  obtain ⟨_, checked, valid⟩ := accepted input success
  exact Loop.DeadStore.rewriteWith_body_denote checked input valid heap

theorem rewrite_step (input : Tuple (Val cells) args)
    (success : rewrite graph removeVersion facts input = some rewritten) (heap : Heap cells) :
    rewritten.step input heap = graph.step input heap := by
  obtain ⟨_, checked, valid⟩ := accepted input success
  exact Loop.DeadStore.rewriteWith_step checked input valid heap

theorem rewrite_evalAfter (input : Tuple (Val cells) args)
    (success : rewrite graph removeVersion facts input = some rewritten)
    (initial : Heap cells) (count : Nat) :
    rewritten.evalAfter input initial count = graph.evalAfter input initial count := by
  obtain ⟨_, checked, valid⟩ := accepted input success
  exact Loop.DeadStore.rewriteWith_evalAfter checked input valid initial count

theorem rewrite_returnsAfter_iff (input : Tuple (Val cells) args)
    (success : rewrite graph removeVersion facts input = some rewritten)
    (initial : Heap cells) (count : Nat) (word : Word) (final : Heap cells) :
    rewritten.ReturnsAfter input initial count word final ↔ graph.ReturnsAfter input initial count word final := by
  obtain ⟨_, checked, valid⟩ := accepted input success
  exact Loop.DeadStore.rewriteWith_returnsAfter_iff checked input valid initial count word final

theorem rewrite_returns_iff (input : Tuple (Val cells) args)
    (success : rewrite graph removeVersion facts input = some rewritten)
    (initial : Heap cells) (word : Word) (final : Heap cells) :
    rewritten.Returns input initial word final ↔ graph.Returns input initial word final := by
  obtain ⟨_, checked, valid⟩ := accepted input success
  exact Loop.DeadStore.rewriteWith_returns_iff checked input valid initial word final

end Silmaril.SSA.SeaOfNodes.Memory.Loop.DeadStore.Search

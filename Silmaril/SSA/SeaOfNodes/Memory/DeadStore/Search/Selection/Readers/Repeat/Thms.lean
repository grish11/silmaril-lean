module

public import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Repeat.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Repeat.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Repeat

open RVSDG (Tuple)
open Memory.Forwarding.Disjoint (Certificate)

variable {args : List ValueSort} {cells : Nat}

theorem DeletesStores.refl (ops : List (Operation args)) : DeletesStores 0 ops ops :=
  Proofs.keepsAll ops

/-- Compose ordered Store deletions and add their exact counts. -/
theorem DeletesStores.trans {removed more : Nat} {source middle target : List (Operation args)}
    (first : DeletesStores removed source middle) (next : DeletesStores more middle target) :
    DeletesStores (removed + more) source target :=
  Proofs.compose first next

theorem DeletesStores.storeCount_eq {graph rewritten : Graph args} {removed : Nat}
    (deletes : DeletesStores removed (operations graph) (operations rewritten)) :
    storeCount rewritten + removed = storeCount graph :=
  Proofs.deletes_storeCount deletes

/-- Renumbering memory edges preserves the complete ordered operation list. -/
theorem reindex_operations {past : List (List ValueSort)} {version : Nat}
    (body : Body args past version) (live : Nat) :
    operations (reindexMemory body live) = operations body :=
  Proofs.reindex_operations body live

/-- A single checked deletion erases one Store and keeps the order and
operands of every retained operation. -/
theorem checked_operations {graph rewritten : Graph args} {candidate : Candidate} {facts : Certificate args}
    (input : Tuple (Val cells) args) (accepted : Memory.DeadStore.rewrite graph candidate facts input = some rewritten) :
    DeletesStores 1 (operations graph) (operations rewritten) :=
  Proofs.checked_operations input accepted

/-- The pass deletes exactly the reported number of Stores. Every retained
operation keeps its original operands and position relative to the others. -/
theorem rewrite_operations (graph : Graph args) (input : Tuple (Val cells) args) :
    let result := rewrite graph input
    DeletesStores result.deleted (operations graph) (operations result.graph) :=
  (Proofs.run_preserves input (storeCount graph) graph).1

theorem rewrite_storeCount (graph : Graph args) (input : Tuple (Val cells) args) :
    let result := rewrite graph input
    storeCount result.graph + result.deleted = storeCount graph :=
  Proofs.deletes_storeCount (rewrite_operations graph input)

/-- The checked selector refuses another deletion on the final graph at this input. -/
theorem rewrite_exhausted (graph : Graph args) (input : Tuple (Val cells) args) :
    Readers.rewrite (rewrite graph input).graph input = none :=
  Proofs.run_exhausted input (storeCount graph) graph (Nat.le_refl _)

theorem rewrite_denote (graph : Graph args) (input : Tuple (Val cells) args) (initial : Heap cells) :
    (rewrite graph input).graph.denote input initial = graph.denote input initial :=
  (Proofs.run_preserves input (storeCount graph) graph).2 initial

/-- The pass preserves and reflects the returned word and the entire final heap. -/
theorem rewrite_returns_iff (graph : Graph args) (input : Tuple (Val cells) args)
    (initial : Heap cells) (word : Word) (final : Heap cells) :
    (rewrite graph input).graph.Returns input initial word final ↔ graph.Returns input initial word final := by
  rw [Graph.returns_iff_denote, Graph.returns_iff_denote, rewrite_denote]

end Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Repeat

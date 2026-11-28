module

public import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Disjoint.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.DeadStore.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.DeadStore

open RVSDG (Locals Origin Tuple)
open Memory.Forwarding.Disjoint (Certificate)

variable {args : List ValueSort} {cells : Nat}
variable {graph rewritten : Graph args} {candidate : Candidate} {facts : Certificate args}

/-- Renumbering the live chain preserves the returned word and heap. -/
theorem reindexMemory_denote {past : List (List ValueSort)} {version : Nat}
    (body : Body args past version) (live : Nat) (input : Tuple (Val cells) args)
    (locals : Locals (Val cells) past) (heap : Heap cells) :
    (reindexMemory body live).denote input locals heap = body.denote input locals heap :=
  Proofs.reindexMemory_denote body live input locals heap

theorem readAt_store {past : List (List ValueSort)} {version : Nat}
    (memory : MemoryInput version) (address : Origin args past .address)
    (word : Origin args past .word) (rest : Body args past (version + 1)) (index : Nat)
    (input : Tuple (Val cells) args) (locals : Locals (Val cells) past) (heap : Heap cells) :
    readAt (.store memory address word rest) index input locals heap =
      readAt rest index input locals (heap.write (readValue address input locals) (readValue word input locals)) :=
  Proofs.readAt_store memory address word rest index input locals heap

/-- Advance the readback index past a Load and pass its word to the later locals. -/
theorem readAt_load {past : List (List ValueSort)} {version : Nat}
    (memory : MemoryInput version) (address : Origin args past .address)
    (rest : Body args ([.word] :: past) version) (index : Nat)
    (input : Tuple (Val cells) args) (locals : Locals (Val cells) past) (heap : Heap cells) :
    readAt (.load memory address rest) (index + 1) input locals heap =
      readAt rest index input (.cons (heap.read (readValue address input locals)) .nil, locals) heap :=
  Proofs.readAt_load memory address rest index input locals heap

/-- Renumbering the memory edges keeps every Load's observation. -/
theorem reindexMemory_readAt {past : List (List ValueSort)} {version : Nat}
    (body : Body args past version) (live index : Nat) (input : Tuple (Val cells) args)
    (locals : Locals (Val cells) past) (heap : Heap cells) :
    readAt (reindexMemory body live) index input locals heap = readAt body index input locals heap :=
  Proofs.reindexMemory_readAt body live index input locals heap

/-- A checked overwrite makes an arbitrary incoming write to the observed
cell invisible to every Load and to the returned word and complete heap. -/
theorem noReadUntil_write (overwrite : Nat) (graph : Graph args)
    (input : Tuple (Val cells) args) (valid : facts.Valid input) (initial : Heap cells) (word : Word)
    (checked : noReadUntil facts overwrite graph = true) :
    let written := initial.write (Forwarding.Disjoint.cell input facts.observed) word
    graph.denote input initial = graph.denote input written ∧
      ∀ index, readAt graph index input PUnit.unit initial = readAt graph index input PUnit.unit written :=
  Proofs.noReadUntil_write overwrite graph input valid initial word checked

theorem rewrite_eq_some_iff (input : Tuple (Val cells) args) :
    rewrite graph candidate facts input = some rewritten ↔
      rewriteWith graph candidate facts = some rewritten ∧ facts.Valid input := by
  simp only [rewrite, ← facts.check_iff_valid input]
  split <;> simp_all

/-- An accepted elimination preserves the return and every ordered Load
for any heap and input satisfying the reader certificate. -/
theorem rewriteWith_observations (success : rewriteWith graph candidate facts = some rewritten)
    (input : Tuple (Val cells) args) (valid : facts.Valid input) (heap : Heap cells) :
    rewritten.denote input heap = graph.denote input heap ∧
      ∀ index, readAt rewritten index input PUnit.unit heap = readAt graph index input PUnit.unit heap :=
  Proofs.rewriteWith_observations success input valid heap

/-- An accepted elimination preserves both observations for every heap
and input satisfying the reader certificate. -/
theorem rewriteWith_denote (success : rewriteWith graph candidate facts = some rewritten)
    (input : Tuple (Val cells) args) (valid : facts.Valid input) (heap : Heap cells) :
    rewritten.denote input heap = graph.denote input heap :=
  (rewriteWith_observations success input valid heap).1

theorem rewriteWith_returns_iff (success : rewriteWith graph candidate facts = some rewritten)
    (input : Tuple (Val cells) args) (valid : facts.Valid input)
    (initial : Heap cells) (word : Word) (final : Heap cells) :
    rewritten.Returns input initial word final ↔ graph.Returns input initial word final := by
  rw [rewritten.returns_iff_denote, graph.returns_iff_denote, rewriteWith_denote success input valid]

/-- A checked invocation preserves and reflects the explicit memory-edge observation. -/
theorem rewrite_returns_iff (input : Tuple (Val cells) args)
    (success : rewrite graph candidate facts input = some rewritten)
    (initial : Heap cells) (word : Word) (final : Heap cells) :
    rewritten.Returns input initial word final ↔ graph.Returns input initial word final := by
  obtain ⟨accepted, valid⟩ := (rewrite_eq_some_iff input).mp success
  exact rewriteWith_returns_iff accepted input valid initial word final

end Silmaril.SSA.SeaOfNodes.Memory.DeadStore

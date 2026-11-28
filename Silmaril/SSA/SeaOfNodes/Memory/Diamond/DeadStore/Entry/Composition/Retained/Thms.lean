module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained

open RVSDG (Port Tuple)
open Memory.Forwarding.Disjoint (cell)
open SeaOfNodes.Diamond (Projection)
open Silmaril.MLIR.MemRef (Buffer)
open Discovery.MemRef.CF (entryTransition run)

variable {args : List ValueSort} {cells : Nat}

/-- Keep the prefix heap and move the selected write past the disjoint
suffix. The retained writes remain in their original order. -/
theorem erase_heap {entry : Memory.Graph args} {chain : List (PrefixStore args)} {word : Port args .word}
    (recognized : stores entry = some (chain, word)) (index : Nat)
    {selected : PrefixStore args} (found : chain[index]? = some selected)
    (input : Tuple (Val cells) args)
    (distinct : ∀ store ∈ chain.drop (index + 1), cell input selected.address ≠ cell input store.address)
    (initial : Heap cells) :
    (entry.denote input initial).2 =
      (selected.table.denote input (Memory.Graph.denote (storeTable word 0 (chain.eraseIdx index)) input initial).2).2 :=
  Proofs.erase_heap recognized index found input distinct initial

/-- Success retains the exact prefix and suffix in order, checks only the
suffix cells, and obtains the existing two-route rewrite. -/
theorem rewrite_checked {graph : Graph args} {entry : Memory.Graph args} {edit : Edit args}
    (index : Nat) (input : Tuple (Val cells) args)
    (accepted : rewrite graph entry (index + 1) input = some edit) :
    ∃ chain word selected,
      stores entry = some (chain, word) ∧ chain[index]? = some selected ∧
      edit.retained = storeTable word 0 (chain.take index ++ chain.drop (index + 1)) ∧
      (∀ store ∈ chain.drop (index + 1), cell input selected.address ≠ cell input store.address) ∧
      Discovery.rewrite ⟨selected, graph⟩ input = some edit.routes :=
  Proofs.rewrite_checked index input accepted

/-- Successful discovery preserves the word and heap for either guard
when the rewritten routes start from the retained chain's heap. -/
theorem rewrite_denote {graph : Graph args} {entry : Memory.Graph args} {edit : Edit args} {version : Nat}
    (input : Tuple (Val cells) args) (accepted : rewrite graph entry version input = some edit)
    (guard : Bool) (initial : Heap cells) :
    edit.routes.graph.denote guard input (edit.retained.denote input initial).2 =
      graph.denote guard input (entry.denote input initial).2 :=
  Proofs.rewrite_denote input accepted guard initial

theorem lower_refused (graph : Graph args) (entry : Memory.Graph args) (version : Nat)
    (input : Tuple (Val cells) args)
    (refused : rewrite graph (Entry.lowerRepeated graph entry input).entry version input = none) :
    let repeated := Entry.lowerRepeated graph entry input
    lower graph entry version input = ⟨repeated.deleted, false, repeated.programs⟩ := by
  simp only [lower, refused]

/-- The emitted entry forwards the original Region frame and the whole
buffer computed by the retained ordered table. -/
theorem lower_retained_entry (graph : Graph args) (entry : Memory.Graph args) (version : Nat)
    (input : Tuple (Val cells) args) {edit : Edit args}
    (accepted : rewrite graph (Entry.lowerRepeated graph entry input).entry version input = some edit)
    (guard : Bool) (initial : Buffer cells) :
    let programs := (lower graph entry version input).programs
    entryTransition programs.optimized programs.input guard initial =
      (.inl ⟨.arm (graph.merge.slot (Projection.ofBool guard)), .nil⟩,
        Buffer.mk (edit.retained.denote input initial.cell).2) :=
  Proofs.lower_retained_entry graph entry version input accepted guard initial

/-- The actual optimized entry forwards the entire heap of the surviving ordered chain. -/
theorem lower_retained_buffer (graph : Graph args) (entry : Memory.Graph args) (version : Nat)
    (input : Tuple (Val cells) args) {edit : Edit args}
    (accepted : rewrite graph (Entry.lowerRepeated graph entry input).entry version input = some edit)
    (guard : Bool) (initial : Buffer cells) :
    let programs := (lower graph entry version input).programs
    (entryTransition programs.optimized programs.input guard initial).2 =
      Buffer.mk (edit.retained.denote input initial.cell).2 :=
  congrArg Prod.snd (lower_retained_entry graph entry version input accepted guard initial)

/-- Both emitted artifacts return the original word and entire final buffer
in three CF steps for either predicate, with no return at shorter budgets. -/
theorem lower_runs (graph : Graph args) (entry : Memory.Graph args) (version : Nat)
    (input : Tuple (Val cells) args) (guard : Bool) (fuel : Nat) (initial : Buffer cells) :
    let programs := (lower graph entry version input).programs
    let result := graph.denote guard input (entry.denote input initial.cell).2
    let expected := if fuel < 3 then none else some (result.1, Buffer.mk result.2)
    run programs.original programs.input guard fuel initial = expected ∧
      run programs.optimized programs.input guard fuel initial = expected :=
  Proofs.lower_runs graph entry version input guard fuel initial

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained

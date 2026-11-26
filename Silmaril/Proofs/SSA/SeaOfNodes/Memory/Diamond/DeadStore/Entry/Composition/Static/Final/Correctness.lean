module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Final.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery.MemRef.CF.Thms
import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Repeat.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Thms
import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Final.Proofs

open RVSDG (Locals Tuple)
open SeaOfNodes.Diamond (Projection)
open Silmaril.MLIR.MemRef (Buffer)
open Memory.DeadStore.Search.Selection.Readers.Repeat (DeletesStores operations reindex_operations)
open Discovery.MemRef.CF (entryDestination entryTransition lowerDiamond lowerDiamond_entryTransition
  lowerDiamond_run run)

variable {args : List ValueSort} {cells : Nat}

private theorem cutWith_preserves {past : List (List ValueSort)} {live version : Nat}
    {body retainedEntry : Memory.Body args past live} {store : PrefixStore args}
    (input : Tuple (Val cells) args)
    (check : PrefixStore args → {past : List (List ValueSort)} → {live : Nat} → Memory.Body args past live → Bool)
    (transfer : ∀ {past : List (List ValueSort)} {live : Nat} (tail : Memory.Body args past live)
      (store : PrefixStore args), check store tail = true →
      ∀ (locals : Locals (Val cells) past) (initial : Heap cells),
        let retained := tail.denote input locals initial
        tail.denote input locals (store.table.denote input initial).2 =
          (retained.1, (store.table.denote input retained.2).2))
    (accepted : cutWith check version body = some (store, retainedEntry)) :
    DeletesStores 1 (operations body) (operations retainedEntry) ∧
      ∀ (locals : Locals (Val cells) past) (initial : Heap cells),
        let retained := retainedEntry.denote input locals initial
        body.denote input locals initial = (retained.1, (store.table.denote input retained.2).2) := by
  induction body with
  | ret => contradiction
  | load _ address _ ih =>
    obtain ⟨⟨_, _⟩, checked, packed⟩ := Option.map_eq_some_iff.mp accepted
    cases packed
    obtain ⟨order, same⟩ := ih checked
    exact ⟨.keep (.load address) order,
      fun locals initial => same (.cons (initial.read (readValue address input locals)) .nil, locals) initial⟩
  | @store _ live _ address word rest ih =>
    simp only [cutWith] at accepted
    split at accepted
    · split at accepted
      · split at accepted
        next safe =>
          cases Option.some.inj accepted
          constructor
          · simp only [operations, reindex_operations]
            exact .drop _ _ (DeletesStores.refl _)
          · intro locals initial
            rw [Memory.DeadStore.reindexMemory_denote]
            exact transfer rest _ safe locals initial
        next => contradiction
      · contradiction
    · obtain ⟨⟨_, _⟩, checked, packed⟩ := Option.map_eq_some_iff.mp accepted
      cases packed
      obtain ⟨order, same⟩ := ih checked
      exact ⟨.keep (.store address word) order,
        fun locals initial => same locals (initial.write (readValue address input locals) (readValue word input locals))⟩

theorem cutWith_disjoint_preserves {past : List (List ValueSort)} {live version : Nat}
    {body retainedEntry : Memory.Body args past live} {store : PrefixStore args}
    (input : Tuple (Val cells) args)
    (check : PrefixStore args → {past : List (List ValueSort)} → {live : Nat} → Memory.Body args past live → Bool)
    (safe : ∀ {past : List (List ValueSort)} {live : Nat} (tail : Memory.Body args past live)
      (store : PrefixStore args), check store tail = true → Retained.Load.checkTail store input tail = true)
    (accepted : cutWith check version body = some (store, retainedEntry)) :
    DeletesStores 1 (operations body) (operations retainedEntry) ∧
      ∀ (locals : Locals (Val cells) past) (initial : Heap cells),
        let retained := retainedEntry.denote input locals initial
        body.denote input locals initial = (retained.1, (store.table.denote input retained.2).2) :=
  cutWith_preserves input check
    (fun tail store accepted => Retained.Load.tail_transfer tail store input (safe tail store accepted)) accepted

theorem cut_preserves {past : List (List ValueSort)} {live version : Nat}
    {body retainedEntry : Memory.Body args past live} {store : PrefixStore args}
    (input : Tuple (Val cells) args) (accepted : cut version body = some (store, retainedEntry)) :
    DeletesStores 1 (operations body) (operations retainedEntry) ∧
      ∀ (locals : Locals (Val cells) past) (initial : Heap cells),
        let retained := retainedEntry.denote input locals initial
        body.denote input locals initial = (retained.1, (store.table.denote input retained.2).2) := by
  apply cutWith_preserves input _ _ accepted
  intro _ _ tail _ safe _ _
  cases tail <;> first | rfl | contradiction

variable {graph : Graph args} {entry retainedEntry : Memory.Graph args} {version : Nat}
variable {store : PrefixStore args} {artifacts : Artifacts cells args}

theorem lower_replay (emitted : lower cells graph entry version = some artifacts) (input : Tuple (Val cells) args) :
    ∃ store retainedEntry edited, cut version entry = some (store, retainedEntry) ∧
      Discovery.rewrite ⟨store, graph⟩ input = some edited ∧
      artifacts = ⟨lowerDiamond cells graph (some entry), lowerDiamond cells edited.graph (some retainedEntry)⟩ := by
  obtain ⟨⟨store, retainedEntry⟩, checked, next⟩ := Option.bind_eq_some_iff.mp emitted
  obtain ⟨edited, accepted, packed⟩ := Option.bind_eq_some_iff.mp next
  exact ⟨store, retainedEntry, edited, checked, Static.rewrite_replay accepted input, (Option.some.inj packed).symm⟩

theorem lower_retained_entry (emitted : lower cells graph entry version = some artifacts)
    (accepted : cut version entry = some (store, retainedEntry)) (input : Tuple (Val cells) args)
    (guard : Bool) (initial : Buffer cells) :
    entryTransition artifacts.optimized input guard initial =
      (.inl ⟨.arm (graph.merge.slot (Projection.ofBool guard)), .nil⟩, Buffer.mk (retainedEntry.denote input initial.cell).2) := by
  obtain ⟨_, _, edited, checked, replay, rfl⟩ := lower_replay emitted input
  rw [accepted] at checked
  cases Option.some.inj checked
  simpa only [Discovery.rewrite_merge input replay] using
    lowerDiamond_entryTransition edited.graph (some retainedEntry) input guard initial

theorem lower_observations (emitted : lower cells graph entry version = some artifacts)
    (input : Tuple (Val cells) args) (guard : Bool) (fuel : Nat) (initial : Buffer cells) :
    let result := graph.denote guard input (entry.denote input initial.cell).2
    let expected := if fuel < 3 then none else some (result.1, Buffer.mk result.2)
    entryDestination artifacts.optimized input guard initial =
      entryDestination artifacts.original input guard initial ∧
      run artifacts.original input guard fuel initial = expected ∧
      run artifacts.optimized input guard fuel initial = expected := by
  obtain ⟨store, retainedEntry, _, checked, replay, rfl⟩ := lower_replay emitted input
  have transfer := congrArg Prod.snd ((cut_preserves input checked).2 PUnit.unit initial.cell)
  have heap : (entry.denote input initial.cell).2 =
      (store.table.denote input (Memory.Graph.denote retainedEntry input initial.cell).2).2 := transfer
  have same := (Discovery.rewrite_denote input replay guard
    (Memory.Graph.denote retainedEntry input initial.cell).2).trans
    (congrArg (graph.denote guard input) heap.symm)
  constructor
  · simp only [entryDestination, lowerDiamond_entryTransition, Discovery.rewrite_merge input replay]
  · simp only [lowerDiamond_run, same, and_self]

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Final.Proofs

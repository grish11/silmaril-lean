module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Disjoint.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery.MemRef.CF.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Thms
import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Repeat.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Proofs

open RVSDG (Locals Port Tuple)
open Memory.Forwarding.Disjoint (Certificate cell)
open SeaOfNodes.Diamond (Projection)
open Silmaril.MLIR.MemRef (Buffer)
open Discovery.MemRef.CF (entryTransition lowerDiamond lowerDiamond_entryTransition lowerDiamond_run run)
open Memory.DeadStore.Search.Selection.Readers.Repeat renaming rewrite_denote → repeatDenote

variable {args : List ValueSort} {cells : Nat}
variable {entry : Memory.Graph args} {graph : Graph args} {edit : Edit args} {version : Nat}

private def writeStore (input : Tuple (Val cells) args) (heap : Heap cells)
    (store : PrefixStore args) : Heap cells :=
  heap.write (cell input store.address) (input.get store.value)

private theorem stores_heap {past : List (List ValueSort)} {live : Nat}
    (body : Memory.Body args past live) {chain : List (PrefixStore args)} {word : Port args .word}
    (found : stores body = some (chain, word)) (input : Tuple (Val cells) args)
    (locals : Locals (Val cells) past) (initial : Heap cells) :
    (body.denote input locals initial).2 = chain.foldl (writeStore input) initial := by
  induction body generalizing chain word initial with
  | ret _ origin =>
    cases origin with
    | arg port =>
      cases Option.some.inj found
      rfl
    | output _ _ => contradiction
  | load => contradiction
  | store _ address value _ ih =>
    cases address with
    | output _ _ => contradiction
    | arg address =>
      cases value with
      | output _ _ => contradiction
      | arg value =>
        obtain ⟨⟨tail, ret⟩, recognized, packed⟩ := Option.map_eq_some_iff.mp found
        cases packed
        exact ih recognized locals (writeStore input initial ⟨address, value⟩)

private theorem table_heap (chain : List (PrefixStore args)) (word : Port args .word) (live : Nat)
    (input : Tuple (Val cells) args) (initial : Heap cells) :
    ((storeTable word live chain).denote input PUnit.unit initial).2 = chain.foldl (writeStore input) initial := by
  induction chain generalizing live initial with
  | nil => rfl
  | cons store rest ih => exact ih (live + 1) (writeStore input initial store)

private theorem foldl_commute (input : Tuple (Val cells) args) (selected : PrefixStore args)
    (chain : List (PrefixStore args))
    (distinct : ∀ store ∈ chain, cell input selected.address ≠ cell input store.address)
    (initial : Heap cells) :
    chain.foldl (writeStore input) (writeStore input initial selected) =
      writeStore input (chain.foldl (writeStore input) initial) selected := by
  induction chain generalizing initial with
  | nil => rfl
  | cons store rest ih =>
    simp only [List.foldl_cons]
    rw [show writeStore input (writeStore input initial selected) store =
        writeStore input (writeStore input initial store) selected from
      Function.update_comm (β := fun _ : Address cells => Word)
        (distinct store List.mem_cons_self) (input.get selected.value) (input.get store.value) initial]
    exact ih (fun other member => distinct other (List.mem_cons_of_mem _ member)) _

private theorem foldl_erase (input : Tuple (Val cells) args) (chain : List (PrefixStore args))
    (index : Nat) {selected : PrefixStore args} (found : chain[index]? = some selected)
    (distinct : ∀ store ∈ chain.drop (index + 1), cell input selected.address ≠ cell input store.address)
    (initial : Heap cells) :
    chain.foldl (writeStore input) initial =
      writeStore input ((chain.eraseIdx index).foldl (writeStore input) initial) selected := by
  induction chain generalizing index initial with
  | nil => simp at found
  | cons store rest ih =>
    cases index with
    | zero =>
      have same : store = selected := Option.some.inj found
      subst selected
      exact foldl_commute input store rest distinct initial
    | succ index =>
      exact ih index found distinct (writeStore input initial store)

theorem erase_heap {chain : List (PrefixStore args)} {word : Port args .word}
    (recognized : stores entry = some (chain, word)) (index : Nat)
    {selected : PrefixStore args} (found : chain[index]? = some selected)
    (input : Tuple (Val cells) args)
    (distinct : ∀ store ∈ chain.drop (index + 1), cell input selected.address ≠ cell input store.address)
    (initial : Heap cells) :
    (entry.denote input initial).2 =
      (selected.table.denote input (Memory.Graph.denote (storeTable word 0 (chain.eraseIdx index)) input initial).2).2 := by
  change (entry.denote input initial).2 =
    writeStore input (Memory.Graph.denote (storeTable word 0 (chain.eraseIdx index)) input initial).2 selected
  rw [show (entry.denote input initial).2 = _ from stores_heap entry recognized input PUnit.unit initial]
  rw [show (Memory.Graph.denote (storeTable word 0 (chain.eraseIdx index)) input initial).2 = _ from
    table_heap _ word 0 input initial]
  exact foldl_erase input chain index found distinct initial

theorem rewrite_checked (index : Nat) (input : Tuple (Val cells) args)
    (accepted : rewrite graph entry (index + 1) input = some edit) :
    ∃ chain word selected,
      stores entry = some (chain, word) ∧ chain[index]? = some selected ∧
      edit.retained = storeTable word 0 (chain.take index ++ chain.drop (index + 1)) ∧
      (∀ store ∈ chain.drop (index + 1), cell input selected.address ≠ cell input store.address) ∧
      Discovery.rewrite ⟨selected, graph⟩ input = some edit.routes := by
  obtain ⟨⟨chain, word⟩, recognized, rest⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨selected, found, checked⟩ := Option.bind_eq_some_iff.mp rest
  let suffix := chain.drop (index + 1)
  let facts : Certificate args := ⟨selected.address, suffix.map PrefixStore.address⟩
  change (if facts.check input then
    (Discovery.rewrite ⟨selected, graph⟩ input).map (Edit.mk (storeTable word 0 (chain.eraseIdx index)))
    else none) = some edit at checked
  split at checked
  next valid =>
    obtain ⟨result, routes, rfl⟩ := Option.map_eq_some_iff.mp checked
    refine ⟨chain, word, selected, recognized, found, ?_, ?_, routes⟩
    · exact congrArg (storeTable word 0) (List.eraseIdx_eq_take_drop_succ chain index)
    · exact fun store member => (facts.check_iff_valid input).mp valid _ (List.mem_map_of_mem member)
  next => contradiction

theorem rewrite_denote (input : Tuple (Val cells) args) (accepted : rewrite graph entry version input = some edit)
    (guard : Bool) (initial : Heap cells) :
    edit.routes.graph.denote guard input (edit.retained.denote input initial).2 =
      graph.denote guard input (entry.denote input initial).2 := by
  cases version with
  | zero => contradiction
  | succ index =>
    obtain ⟨chain, word, selected, recognized, found, retained, distinct, routes⟩ :=
      rewrite_checked index input accepted
    rw [retained, ← List.eraseIdx_eq_take_drop_succ]
    have heap := erase_heap recognized index found input distinct initial
    exact (Discovery.rewrite_denote input routes guard _).trans (congrArg (graph.denote guard input) heap.symm)

theorem lower_runs (graph : Graph args) (entry : Memory.Graph args) (version : Nat)
    (input : Tuple (Val cells) args) (guard : Bool) (fuel : Nat) (initial : Buffer cells) :
    let programs := (lower graph entry version input).programs
    let result := graph.denote guard input (entry.denote input initial.cell).2
    let expected := if fuel < 3 then none else some (result.1, Buffer.mk result.2)
    run programs.original programs.input guard fuel initial = expected ∧
      run programs.optimized programs.input guard fuel initial = expected := by
  cases checked : rewrite graph (Entry.lowerRepeated graph entry input).entry version input with
  | none => simpa only [lower, checked] using Entry.lowerRepeated_runs graph entry input guard fuel initial
  | some edit =>
    simp only [lower, checked]
    refine ⟨(Entry.lowerRepeated_runs graph entry input guard fuel initial).1, ?_⟩
    have sameHeap := congrArg Prod.snd (repeatDenote entry input initial.cell)
    have same := (rewrite_denote input checked guard initial.cell).trans
      (congrArg (graph.denote guard input) sameHeap)
    exact (lowerDiamond_run edit.routes.graph (some edit.retained) input guard fuel initial).trans
      (congrArg (fun result : Word × Heap cells =>
        if fuel < 3 then none else some (result.1, Buffer.mk result.2)) same)

theorem lower_retained_entry (graph : Graph args) (entry : Memory.Graph args) (version : Nat)
    (input : Tuple (Val cells) args)
    (accepted : rewrite graph (Entry.lowerRepeated graph entry input).entry version input = some edit)
    (guard : Bool) (initial : Buffer cells) :
    let programs := (lower graph entry version input).programs
    entryTransition programs.optimized programs.input guard initial =
      (.inl ⟨.arm (graph.merge.slot (Projection.ofBool guard)), .nil⟩,
        Buffer.mk (edit.retained.denote input initial.cell).2) := by
  cases version with
  | zero => contradiction
  | succ index =>
    obtain ⟨_, _, _, _, _, _, _, routes⟩ := rewrite_checked index input accepted
    have merge := Discovery.rewrite_merge input routes
    simp only [lower, accepted]
    exact (lowerDiamond_entryTransition edit.routes.graph (some edit.retained) input guard initial).trans
      (by rw [merge])

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Proofs

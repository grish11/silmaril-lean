module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Thms
import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery.MemRef.CF.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Thms
import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Repeat.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Proofs

open RVSDG (Locals Tuple)
open Memory.Forwarding.Disjoint (cell)
open Silmaril.MLIR.MemRef (Buffer)
open Discovery.MemRef.CF (lowerDiamond lowerDiamond_entryTransition lowerDiamond_run entryTransition run)
open Memory.DeadStore.Search.Selection.Readers.Repeat (DeletesStores operations reindex_operations)
open Memory.DeadStore.Search.Selection.Readers.Repeat renaming rewrite_denote → repeatDenote

variable {args : List ValueSort} {cells : Nat}

theorem tail_transfer {past : List (List ValueSort)} {live : Nat} (tail : Memory.Body args past live)
    (selected : PrefixStore args) (input : Tuple (Val cells) args) (safe : checkTail selected input tail = true)
    (locals : Locals (Val cells) past) (initial : Heap cells) :
    let retained := tail.denote input locals initial
    tail.denote input locals (selected.table.denote input initial).2 =
      (retained.1, (selected.table.denote input retained.2).2) := by
  induction tail generalizing initial with
  | ret => rfl
  | load _ address rest ih =>
    cases address with
    | output => contradiction
    | arg reader =>
      obtain ⟨distinct, safeRest⟩ := Bool.and_eq_true_iff.mp safe
      have readSafe : cell input selected.address ≠ cell input reader := of_decide_eq_true distinct
      let written := (selected.table.denote input initial).2
      have same : written.read (cell input reader) = initial.read (cell input reader) :=
        initial.read_write_other (cell input selected.address) (cell input reader)
          (input.get selected.value) readSafe.symm
      change rest.denote input (.cons (written.read (cell input reader)) .nil, locals) written = _
      rw [same]
      exact ih safeRest (.cons (initial.read (cell input reader)) .nil, locals) initial
  | store _ address value rest ih =>
    cases address with
    | output => contradiction
    | arg writer =>
      obtain ⟨distinct, safeRest⟩ := Bool.and_eq_true_iff.mp safe
      have writeSafe : cell input selected.address ≠ cell input writer := of_decide_eq_true distinct
      let word := readValue value input locals
      let updated := initial.write (cell input writer) word
      have commute :
          ((selected.table.denote input initial).2).write (cell input writer) word =
            (selected.table.denote input updated).2 :=
        Function.update_comm (β := fun _ : Address cells => Word)
          writeSafe (input.get selected.value) word initial
      change rest.denote input locals (((selected.table.denote input initial).2).write (cell input writer) word) = _
      rw [commute]
      exact ih safeRest locals updated

private theorem cutWith_preserves {past : List (List ValueSort)} {live version : Nat}
    {body retained : Memory.Body args past live} {selected : PrefixStore args}
    (input : Tuple (Val cells) args)
    (check : PrefixStore args → {past : List (List ValueSort)} → {live : Nat} → Memory.Body args past live → Bool)
    (restore : PrefixStore args → Heap cells → Heap cells)
    (transfer : ∀ {past : List (List ValueSort)} {live : Nat} (tail : Memory.Body args past live)
      (store : PrefixStore args), check store tail = true →
      ∀ (locals : Locals (Val cells) past) (initial : Heap cells),
        let result := tail.denote input locals initial
        tail.denote input locals (store.table.denote input initial).2 = (result.1, restore store result.2))
    (accepted : cutWith check version body = some (selected, retained)) :
    DeletesStores 1 (operations body) (operations retained) ∧
      ∀ (locals : Locals (Val cells) past) (initial : Heap cells),
        let result := retained.denote input locals initial
        body.denote input locals initial = (result.1, restore selected result.2) := by
  induction body with
  | ret => contradiction
  | load => contradiction
  | @store _ live _ address value rest ih =>
    cases address with
    | output => contradiction
    | arg address =>
      cases value with
      | output => contradiction
      | arg word =>
        simp only [cutWith] at accepted
        split at accepted
        · split at accepted
          next safe =>
            cases Option.some.inj accepted
            constructor
            · change DeletesStores 1 (.store (.arg address) (.arg word) :: operations rest)
                (operations (Memory.DeadStore.reindexMemory rest live))
              rw [reindex_operations]
              exact .drop (.arg address) (.arg word) (DeletesStores.refl _)
            · intro locals initial
              rw [Memory.DeadStore.reindexMemory_denote]
              exact transfer rest ⟨address, word⟩ safe locals initial
          next => contradiction
        · obtain ⟨⟨candidate, tail⟩, checked, packed⟩ := Option.map_eq_some_iff.mp accepted
          cases packed
          obtain ⟨order, transfer⟩ := ih checked
          exact ⟨.keep (.store (.arg address) (.arg word)) order,
            fun locals initial => transfer locals (initial.write (cell input address) (input.get word))⟩

theorem cutWith_disjoint_preserves {past : List (List ValueSort)} {live version : Nat}
    {body retained : Memory.Body args past live} {selected : PrefixStore args}
    (input : Tuple (Val cells) args)
    (check : PrefixStore args → {past : List (List ValueSort)} → {live : Nat} → Memory.Body args past live → Bool)
    (safe : ∀ {past : List (List ValueSort)} {live : Nat} (tail : Memory.Body args past live)
      (store : PrefixStore args), check store tail = true → checkTail store input tail = true)
    (accepted : cutWith check version body = some (selected, retained)) :
    DeletesStores 1 (operations body) (operations retained) ∧
      ∀ (locals : Locals (Val cells) past) (initial : Heap cells),
        let result := retained.denote input locals initial
        body.denote input locals initial = (result.1, (selected.table.denote input result.2).2) :=
  cutWith_preserves input check (fun store heap => (store.table.denote input heap).2)
    (fun tail store checked => tail_transfer tail store input (safe tail store checked)) accepted

theorem cut_preserves {past : List (List ValueSort)} {live version : Nat}
    {body retained : Memory.Body args past live} {selected : PrefixStore args}
    (input : Tuple (Val cells) args) (accepted : cut version input body = some (selected, retained)) :
    DeletesStores 1 (operations body) (operations retained) ∧
      ∀ (locals : Locals (Val cells) past) (initial : Heap cells),
        let result := retained.denote input locals initial
        body.denote input locals initial = (result.1, (selected.table.denote input result.2).2) :=
  cutWith_disjoint_preserves input (fun store {_ _} tail => checkTail store input tail)
    (fun _ _ safe => safe) accepted

theorem overwrite_tail_denote {past : List (List ValueSort)} {live : Nat}
    (tail : Memory.Body args past live) (selected : PrefixStore args)
    (input : Tuple (Val cells) args) (safe : checkOverwrite selected input tail = true)
    (locals : Locals (Val cells) past) (initial : Heap cells) :
    tail.denote input locals (selected.table.denote input initial).2 = tail.denote input locals initial := by
  induction tail generalizing initial with
  | ret => contradiction
  | load _ address rest ih =>
    cases address with
    | output => contradiction
    | arg reader =>
      obtain ⟨distinct, safeRest⟩ := Bool.and_eq_true_iff.mp safe
      have readSafe : cell input selected.address ≠ cell input reader := of_decide_eq_true distinct
      let written := (selected.table.denote input initial).2
      have same : written.read (cell input reader) = initial.read (cell input reader) :=
        initial.read_write_other (cell input selected.address) (cell input reader)
          (input.get selected.value) readSafe.symm
      change rest.denote input (.cons (written.read (cell input reader)) .nil, locals) written =
        rest.denote input (.cons (initial.read (cell input reader)) .nil, locals) initial
      rw [same]
      exact ih safeRest (.cons (initial.read (cell input reader)) .nil, locals) initial
  | store _ address value rest ih =>
    cases address with
    | output => contradiction
    | arg writer =>
      simp only [checkOverwrite] at safe
      let word := readValue value input locals
      let updated := initial.write (cell input writer) word
      change rest.denote input locals (((selected.table.denote input initial).2).write (cell input writer) word) =
        rest.denote input locals updated
      split at safe
      next sameCell =>
        have killed : ((selected.table.denote input initial).2).write (cell input writer) word = updated := by
          change (initial.write (cell input selected.address) (input.get selected.value)).write
            (cell input writer) word = updated
          rw [sameCell]
          exact Function.update_idem (β := fun _ : Address cells => Word) _ _ _
        rw [killed]
      next distinct =>
        have commute :
            ((selected.table.denote input initial).2).write (cell input writer) word =
              (selected.table.denote input updated).2 :=
          Function.update_comm (β := fun _ : Address cells => Word)
            distinct (input.get selected.value) word initial
        rw [commute]
        exact ih safe locals updated

theorem cutOverwrite_preserves {past : List (List ValueSort)} {live version : Nat}
    {body retained : Memory.Body args past live} {selected : PrefixStore args}
    (input : Tuple (Val cells) args) (accepted : cutOverwrite version input body = some (selected, retained)) :
    DeletesStores 1 (operations body) (operations retained) ∧
      ∀ (locals : Locals (Val cells) past) (initial : Heap cells),
        body.denote input locals initial = retained.denote input locals initial :=
  cutWith_preserves input (fun store {_ _} tail => checkOverwrite store input tail) (fun _ heap => heap)
    (fun tail store safe => overwrite_tail_denote tail store input safe) accepted

variable {graph : Graph args} {entry : Memory.Graph args} {edit : Retained.Edit args} {version : Nat}

theorem rewrite_checked (input : Tuple (Val cells) args) (accepted : rewrite graph entry version input = some edit) :
    ∃ selected, cut version input entry = some (selected, edit.retained) ∧
      Discovery.rewrite ⟨selected, graph⟩ input = some edit.routes := by
  obtain ⟨⟨selected, retained⟩, checked, rest⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨routes, discovered, rfl⟩ := Option.map_eq_some_iff.mp rest
  exact ⟨selected, checked, discovered⟩

theorem rewrite_denote (input : Tuple (Val cells) args) (accepted : rewrite graph entry version input = some edit)
    (guard : Bool) (initial : Heap cells) :
    edit.routes.graph.denote guard input (edit.retained.denote input initial).2 =
      graph.denote guard input (entry.denote input initial).2 := by
  obtain ⟨_, checked, discovered⟩ := rewrite_checked input accepted
  exact (Discovery.rewrite_denote input discovered guard _).trans
    (congrArg (graph.denote guard input) (congrArg Prod.snd ((cut_preserves input checked).2 PUnit.unit initial)).symm)

theorem lower_retained_entry (graph : Graph args) (entry : Memory.Graph args) (version : Nat)
    (input : Tuple (Val cells) args)
    (accepted : rewrite graph (Entry.lowerRepeated graph entry input).entry version input = some edit)
    (guard : Bool) (initial : Buffer cells) :
    let programs := (lower graph entry version input).programs
    entryTransition programs.optimized programs.input guard initial =
      (.inl ⟨.arm (graph.merge.slot (SeaOfNodes.Diamond.Projection.ofBool guard)), .nil⟩,
        Buffer.mk (edit.retained.denote input initial.cell).2) := by
  obtain ⟨_, _, discovered⟩ := rewrite_checked input accepted
  simp only [lower, accepted]
  exact (lowerDiamond_entryTransition edit.routes.graph (some edit.retained) input guard initial).trans
    (by rw [Discovery.rewrite_merge input discovered])

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
    have same := (rewrite_denote input checked guard initial.cell).trans
      (congrArg (fun result : Word × Heap cells => graph.denote guard input result.2)
        (repeatDenote entry input initial.cell))
    exact (lowerDiamond_run edit.routes.graph (some edit.retained) input guard fuel initial).trans
      (congrArg (fun result : Word × Heap cells =>
        if fuel < 3 then none else some (result.1, Buffer.mk result.2)) same)

private theorem residualOverwrite_denote (graph : Graph args) (entry retained : Memory.Graph args)
    (input : Tuple (Val cells) args) {selected : PrefixStore args} {version : Nat}
    (checked : cutOverwrite version input (Entry.lowerRepeated graph entry input).entry = some (selected, retained))
    (initial : Heap cells) : retained.denote input initial = entry.denote input initial :=
  ((cutOverwrite_preserves input checked).2 PUnit.unit initial).symm.trans (repeatDenote entry input initial)

theorem lowerOverwrite_entryTransition_eq (graph : Graph args) (entry : Memory.Graph args) (version : Nat)
    (input : Tuple (Val cells) args) (guard : Bool) (initial : Buffer cells) :
    let programs := (lowerOverwrite graph entry version input).programs
    entryTransition programs.optimized programs.input guard initial =
      entryTransition programs.original programs.input guard initial := by
  cases checked : cutOverwrite version input (Entry.lowerRepeated graph entry input).entry with
  | none =>
    simpa only [lowerOverwrite, checked] using Entry.lowerRepeated_entryTransition_eq graph entry input guard initial
  | some edit =>
    obtain ⟨selected, retained⟩ := edit
    simp only [lowerOverwrite, checked, Entry.lowerPair, lowerDiamond_entryTransition,
      residualOverwrite_denote graph entry retained input checked initial.cell]

theorem lowerOverwrite_runs (graph : Graph args) (entry : Memory.Graph args) (version : Nat)
    (input : Tuple (Val cells) args) (guard : Bool) (fuel : Nat) (initial : Buffer cells) :
    let programs := (lowerOverwrite graph entry version input).programs
    let result := graph.denote guard input (entry.denote input initial.cell).2
    let expected := if fuel < 3 then none else some (result.1, Buffer.mk result.2)
    run programs.original programs.input guard fuel initial = expected ∧
      run programs.optimized programs.input guard fuel initial = expected := by
  cases checked : cutOverwrite version input (Entry.lowerRepeated graph entry input).entry with
  | none => simpa only [lowerOverwrite, checked] using Entry.lowerRepeated_runs graph entry input guard fuel initial
  | some edit =>
    obtain ⟨selected, retained⟩ := edit
    simp only [lowerOverwrite, checked, Entry.lowerPair, lowerDiamond_run,
      residualOverwrite_denote graph entry retained input checked initial.cell, and_self]

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Proofs

module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load

open RVSDG (Locals Tuple)
open SeaOfNodes.Diamond (Projection)
open Silmaril.MLIR.MemRef (Buffer)
open Discovery.MemRef.CF (entryTransition run)
open Memory.DeadStore.Search.Selection.Readers.Repeat (DeletesStores operations)

variable {args : List ValueSort} {cells : Nat}

/-- A checked suffix keeps its scalar result and commutes with the
nominated write on the entire heap, at any typed local environment. -/
theorem tail_transfer {past : List (List ValueSort)} {live : Nat} (tail : Memory.Body args past live)
    (selected : PrefixStore args) (input : Tuple (Val cells) args) (safe : checkTail selected input tail = true)
    (locals : Locals (Val cells) past) (initial : Heap cells) :
    let retained := tail.denote input locals initial
    tail.denote input locals (selected.table.denote input initial).2 =
      (retained.1, (selected.table.denote input retained.2).2) :=
  Proofs.tail_transfer tail selected input safe locals initial

/-- Reuse the cut and replay law with a suffix checker that establishes
the existing disjointness check at this input. -/
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
  Proofs.cutWith_disjoint_preserves input check safe accepted

/-- Exactly the nominated Store is cut. Every retained operation keeps
its typed scalar operands and relative order. -/
theorem cut_operations {past : List (List ValueSort)} {live version : Nat}
    {body retained : Memory.Body args past live} {selected : PrefixStore args}
    (input : Tuple (Val cells) args) (accepted : cut version input body = some (selected, retained)) :
    DeletesStores 1 (operations body) (operations retained) :=
  (Proofs.cut_preserves input accepted).1

/-- The checked cut preserves the suffix's scalar result. Replaying only
the selected Store on the retained heap recovers the complete source heap. -/
theorem cut_denote {past : List (List ValueSort)} {live version : Nat}
    {body retained : Memory.Body args past live} {selected : PrefixStore args}
    (input : Tuple (Val cells) args) (accepted : cut version input body = some (selected, retained))
    (locals : Locals (Val cells) past) (initial : Heap cells) :
    let result := retained.denote input locals initial
    body.denote input locals initial = (result.1, (selected.table.denote input result.2).2) :=
  (Proofs.cut_preserves input accepted).2 locals initial

/-- Success requires both the native entry cut and the existing two-route check. -/
theorem rewrite_checked {graph : Graph args} {entry : Memory.Graph args} {edit : Retained.Edit args} {version : Nat}
    (input : Tuple (Val cells) args) (accepted : rewrite graph entry version input = some edit) :
    ∃ selected, cut version input entry = some (selected, edit.retained) ∧
      Discovery.rewrite ⟨selected, graph⟩ input = some edit.routes :=
  Proofs.rewrite_checked input accepted

theorem lower_refused (graph : Graph args) (entry : Memory.Graph args) (version : Nat)
    (input : Tuple (Val cells) args)
    (refused : rewrite graph (Entry.lowerRepeated graph entry input).entry version input = none) :
    let repeated := Entry.lowerRepeated graph entry input
    lower graph entry version input = ⟨repeated.deleted, false, repeated.programs⟩ := by
  simp only [lower, refused]

/-- The optimized entry emits the original Region frame and the full
buffer of the actual retained table. -/
theorem lower_retained_entry (graph : Graph args) (entry : Memory.Graph args) (version : Nat)
    (input : Tuple (Val cells) args) {edit : Retained.Edit args}
    (accepted : rewrite graph (Entry.lowerRepeated graph entry input).entry version input = some edit)
    (guard : Bool) (initial : Buffer cells) :
    let programs := (lower graph entry version input).programs
    entryTransition programs.optimized programs.input guard initial =
      (.inl ⟨.arm (graph.merge.slot (Projection.ofBool guard)), .nil⟩,
        Buffer.mk (edit.retained.denote input initial.cell).2) :=
  Proofs.lower_retained_entry graph entry version input accepted guard initial

/-- Both emitted CFGs agree on the returned word and entire final buffer
for either guard and any initial buffer. Three CF block steps suffice. -/
theorem lower_runs (graph : Graph args) (entry : Memory.Graph args) (version : Nat)
    (input : Tuple (Val cells) args) (guard : Bool) (fuel : Nat) (initial : Buffer cells) :
    let programs := (lower graph entry version input).programs
    let result := graph.denote guard input (entry.denote input initial.cell).2
    let expected := if fuel < 3 then none else some (result.1, Buffer.mk result.2)
    run programs.original programs.input guard fuel initial = expected ∧
      run programs.optimized programs.input guard fuel initial = expected :=
  Proofs.lower_runs graph entry version input guard fuel initial

/-- Up to the first overwrite the two runs bind identical words and
differ only by the nominated write. The first overwrite uses the same
operand in both runs and establishes equality of the entire heap. -/
theorem overwrite_tail_denote {past : List (List ValueSort)} {live : Nat}
    (tail : Memory.Body args past live) (selected : PrefixStore args)
    (input : Tuple (Val cells) args) (safe : checkOverwrite selected input tail = true)
    (locals : Locals (Val cells) past) (initial : Heap cells) :
    tail.denote input locals (selected.table.denote input initial).2 = tail.denote input locals initial :=
  Proofs.overwrite_tail_denote tail selected input safe locals initial

/-- The edit removes exactly the nominated Store, retaining operation
order and original scalar operands, with identical returned word and
entire heap at the checked valuation. -/
theorem cutOverwrite_preserves {past : List (List ValueSort)} {live version : Nat}
    {body retained : Memory.Body args past live} {selected : PrefixStore args}
    (input : Tuple (Val cells) args) (accepted : cutOverwrite version input body = some (selected, retained)) :
    DeletesStores 1 (operations body) (operations retained) ∧
      ∀ (locals : Locals (Val cells) past) (initial : Heap cells),
        body.denote input locals initial = retained.denote input locals initial :=
  Proofs.cutOverwrite_preserves input accepted

theorem lowerOverwrite_refused (graph : Graph args) (entry : Memory.Graph args) (version : Nat)
    (input : Tuple (Val cells) args)
    (refused : cutOverwrite version input (Entry.lowerRepeated graph entry input).entry = none) :
    let repeated := Entry.lowerRepeated graph entry input
    lowerOverwrite graph entry version input = ⟨repeated.deleted, false, repeated.programs⟩ := by
  simp only [lowerOverwrite, refused]

/-- The actual emitted entries agree on the successor frame and every cell. -/
theorem lowerOverwrite_entryTransition_eq (graph : Graph args) (entry : Memory.Graph args) (version : Nat)
    (input : Tuple (Val cells) args) (guard : Bool) (initial : Buffer cells) :
    let programs := (lowerOverwrite graph entry version input).programs
    entryTransition programs.optimized programs.input guard initial =
      entryTransition programs.original programs.input guard initial :=
  Proofs.lowerOverwrite_entryTransition_eq graph entry version input guard initial

/-- At the checked input, both CFGs agree for any initial buffer, either
predicate, and every CF budget. Each still executes three blocks. -/
theorem lowerOverwrite_runs (graph : Graph args) (entry : Memory.Graph args) (version : Nat)
    (input : Tuple (Val cells) args) (guard : Bool) (fuel : Nat) (initial : Buffer cells) :
    let programs := (lowerOverwrite graph entry version input).programs
    let result := graph.denote guard input (entry.denote input initial.cell).2
    let expected := if fuel < 3 then none else some (result.1, Buffer.mk result.2)
    run programs.original programs.input guard fuel initial = expected ∧
      run programs.optimized programs.input guard fuel initial = expected :=
  Proofs.lowerOverwrite_runs graph entry version input guard fuel initial

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load

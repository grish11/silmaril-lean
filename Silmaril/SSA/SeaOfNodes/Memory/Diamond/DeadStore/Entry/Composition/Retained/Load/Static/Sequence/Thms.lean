module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Sequence.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Sequence.Correctness
import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Repeat.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Sequence

open RVSDG (Tuple)
open Diamond.Institution (PortMap mapBody pullInput)
open Memory.DeadStore.Search.Selection.Readers.Repeat (DeletesStores operations)
open Silmaril.MLIR.MemRef (Buffer)
open Discovery.MemRef.CF renaming Programs → EmittedPrograms
open Discovery.MemRef.CF (entryTransition run)

variable {args target : List ValueSort} {cells : Nat}

theorem Plan.check_iff_valid (plan : Plan args) (input : Tuple (Val cells) args) :
    plan.check input = true ↔ plan.Valid input :=
  Proofs.check_iff_valid plan input

/-- A completed plan deletes exactly one Store per step, retains operation
order and operands, and preserves the word and all heap cells. -/
theorem Plan.rewrite_preserves {plan : Plan args} {entry final : Memory.Graph args}
    (accepted : plan.rewrite entry = some final) {input : Tuple (Val cells) args}
    (valid : plan.Valid input) (initial : Heap cells) :
    DeletesStores plan.length (operations entry) (operations final) ∧
      entry.denote input initial = final.denote input initial :=
  Proofs.rewrite_preserves accepted valid initial

/-- Emission requires a fully checked plan and every contract at this input. -/
theorem lower_eq_some_iff (graph : Graph args) (entry : Memory.Graph args) (plan : Plan args)
    (input : Tuple (Val cells) args) (programs : EmittedPrograms cells args) :
    lower graph entry plan input = some programs ↔
      plan.Valid input ∧ ∃ final, plan.rewrite entry = some final ∧ Entry.lowerPair graph entry final input = programs :=
  Proofs.lower_eq_some_iff graph entry plan input programs

/-- The original and final emitted entries forward the same successor
packet and full buffer for either predicate and any initial buffer. -/
theorem lower_entryTransition_eq {graph : Graph args} {entry : Memory.Graph args} {plan : Plan args}
    {input : Tuple (Val cells) args} {programs : EmittedPrograms cells args}
    (emitted : lower graph entry plan input = some programs) (guard : Bool) (initial : Buffer cells) :
    entryTransition programs.optimized programs.input guard initial =
      entryTransition programs.original programs.input guard initial :=
  Proofs.lower_entryTransition_eq emitted guard initial

/-- Both actual CFGs have the same finite-budget observation. Three CF
block steps suffice, including the selected arm and join. -/
theorem lower_runs {graph : Graph args} {entry : Memory.Graph args} {plan : Plan args}
    {input : Tuple (Val cells) args} {programs : EmittedPrograms cells args}
    (emitted : lower graph entry plan input = some programs) (guard : Bool) (fuel : Nat) (initial : Buffer cells) :
    let result := graph.denote guard input (entry.denote input initial.cell).2
    let expected := if fuel < 3 then none else some (result.1, Buffer.mk result.2)
    run programs.original programs.input guard fuel initial = expected ∧
      run programs.optimized programs.input guard fuel initial = expected :=
  Proofs.lower_runs emitted guard fuel initial

theorem Plan.valid_transport (rename : PortMap args target) {plan : Plan args} {mapped : Plan target}
    (transported : plan.transport rename = some mapped) (input : Tuple (Val cells) target) :
    mapped.Valid input ↔ plan.Valid (pullInput rename input) :=
  Proofs.valid_transport rename transported input

/-- Transport replays the successful steps against the same succession of
mapped entry tables, producing the mapped final table. -/
theorem Plan.rewrite_transport (rename : PortMap args target) {plan : Plan args} {mapped : Plan target}
    (transported : plan.transport rename = some mapped)
    {entry final : Memory.Graph args} (accepted : plan.rewrite entry = some final) :
    mapped.rewrite (mapBody rename entry) = some (mapBody rename final) :=
  Proofs.rewrite_transport rename transported accepted

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Sequence

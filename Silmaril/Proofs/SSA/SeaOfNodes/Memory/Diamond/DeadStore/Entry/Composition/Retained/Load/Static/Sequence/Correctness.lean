module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Sequence.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Reindex.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery.MemRef.CF.Thms
import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Repeat.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Sequence.Proofs

open RVSDG (Tuple)
open Diamond.Institution (PortMap mapBody pullInput)
open Memory.DeadStore.Search.Selection.Readers.Repeat (DeletesStores operations)
open Silmaril.MLIR.MemRef (Buffer)
open Discovery.MemRef.CF renaming Programs → EmittedPrograms
open Discovery.MemRef.CF (entryTransition run lowerDiamond_entryTransition lowerDiamond_run)

variable {args target : List ValueSort} {cells : Nat}

theorem check_iff_valid (plan : Plan args) (input : Tuple (Val cells) args) :
    plan.check input = true ↔ plan.Valid input := by
  simp [Plan.check, Plan.Valid, AddressContract.check_iff_valid]

private theorem rewrite_cons (step : Step args) (rest : Plan args) (entry : Memory.Graph args) :
    Plan.rewrite (step :: rest) entry =
      ((cut step.facts step.version entry).map Prod.snd).bind rest.rewrite := by
  simp only [Plan.rewrite, List.foldlM_cons]
  rfl

private theorem split_rewrite {step : Step args} {rest : Plan args} {entry final : Memory.Graph args}
    (accepted : Plan.rewrite (step :: rest) entry = some final) :
    ∃ selected current, cut step.facts step.version entry = some (selected, current) ∧
      rest.rewrite current = some final := by
  rw [rewrite_cons] at accepted
  obtain ⟨current, stepAccepted, next⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨⟨selected, retained⟩, first, same⟩ := Option.map_eq_some_iff.mp stepAccepted
  cases same
  exact ⟨selected, retained, first, next⟩

theorem rewrite_preserves {plan : Plan args} {entry final : Memory.Graph args}
    (accepted : plan.rewrite entry = some final) {input : Tuple (Val cells) args}
    (valid : plan.Valid input) (initial : Heap cells) :
    DeletesStores plan.length (operations entry) (operations final) ∧
      entry.denote input initial = final.denote input initial := by
  induction plan generalizing entry with
  | nil =>
    cases Option.some.inj accepted
    exact ⟨DeletesStores.refl _, rfl⟩
  | cons step rest ih =>
    obtain ⟨_, current, cutAccepted, next⟩ := split_rewrite accepted
    obtain ⟨first, entryEq⟩ := Static.cut_preserves cutAccepted (valid step (List.mem_cons_self ..)) initial
    obtain ⟨remaining, finalEq⟩ := ih next (fun s member => valid s (List.mem_cons_of_mem _ member))
    refine ⟨?_, entryEq.trans finalEq⟩
    simpa only [List.length_cons, Nat.add_comm 1 rest.length] using first.trans remaining

theorem lower_eq_some_iff (graph : Graph args) (entry : Memory.Graph args) (plan : Plan args)
    (input : Tuple (Val cells) args) (programs : EmittedPrograms cells args) :
    lower graph entry plan input = some programs ↔
      plan.Valid input ∧ ∃ final, plan.rewrite entry = some final ∧ Entry.lowerPair graph entry final input = programs := by
  rw [← check_iff_valid]
  cases checked : plan.check input <;> simp [lower, checked, Option.map_eq_some_iff]

theorem lower_entryTransition_eq {graph : Graph args} {entry : Memory.Graph args} {plan : Plan args}
    {input : Tuple (Val cells) args} {programs : EmittedPrograms cells args}
    (emitted : lower graph entry plan input = some programs) (guard : Bool) (initial : Buffer cells) :
    entryTransition programs.optimized programs.input guard initial =
      entryTransition programs.original programs.input guard initial := by
  obtain ⟨valid, final, rewritten, rfl⟩ := (lower_eq_some_iff graph entry plan input programs).mp emitted
  have same := (rewrite_preserves rewritten valid initial.cell).2
  simp only [Entry.lowerPair, lowerDiamond_entryTransition]
  rw [← same]

theorem lower_runs {graph : Graph args} {entry : Memory.Graph args} {plan : Plan args}
    {input : Tuple (Val cells) args} {programs : EmittedPrograms cells args}
    (emitted : lower graph entry plan input = some programs) (guard : Bool) (fuel : Nat) (initial : Buffer cells) :
    let result := graph.denote guard input (entry.denote input initial.cell).2
    let expected := if fuel < 3 then none else some (result.1, Buffer.mk result.2)
    run programs.original programs.input guard fuel initial = expected ∧
      run programs.optimized programs.input guard fuel initial = expected := by
  obtain ⟨valid, final, rewritten, rfl⟩ := (lower_eq_some_iff graph entry plan input programs).mp emitted
  have same := (rewrite_preserves rewritten valid initial.cell).2
  simp only [Entry.lowerPair, lowerDiamond_run, ← same, and_self]

private theorem split_transport (rename : PortMap args target)
    {step : Step args} {rest : Plan args} {mapped : Plan target}
    (transported : Plan.transport (step :: rest) rename = some mapped) :
    ∃ facts next, step.facts.transport rename = some facts ∧ rest.transport rename = some next ∧
      mapped = ⟨step.version, facts⟩ :: next := by
  simp only [Plan.transport, List.mapM_cons] at transported
  obtain ⟨first, firstAccepted, remaining⟩ := Option.bind_eq_some_iff.mp transported
  obtain ⟨next, restAccepted, same⟩ := Option.bind_eq_some_iff.mp remaining
  obtain ⟨facts, accepted, rfl⟩ := Option.map_eq_some_iff.mp firstAccepted
  exact ⟨facts, next, accepted, restAccepted, (Option.some.inj same).symm⟩

theorem valid_transport (rename : PortMap args target) {plan : Plan args} {mapped : Plan target}
    (transported : plan.transport rename = some mapped) (input : Tuple (Val cells) target) :
    mapped.Valid input ↔ plan.Valid (pullInput rename input) := by
  induction plan generalizing mapped with
  | nil =>
    cases Option.some.inj transported
    simp [Plan.Valid]
  | cons step rest ih =>
    obtain ⟨facts, next, first, remaining, rfl⟩ := split_transport rename transported
    simp only [Plan.Valid, List.forall_mem_cons]
    exact and_congr (Reindex.valid_transport rename first input) (ih remaining)

theorem rewrite_transport (rename : PortMap args target) {plan : Plan args} {mapped : Plan target}
    (transported : plan.transport rename = some mapped)
    {entry final : Memory.Graph args} (accepted : plan.rewrite entry = some final) :
    mapped.rewrite (mapBody rename entry) = some (mapBody rename final) := by
  induction plan generalizing mapped entry with
  | nil =>
    cases Option.some.inj transported
    cases Option.some.inj accepted
    rfl
  | cons step rest ih =>
    obtain ⟨facts, next, first, remaining, rfl⟩ := split_transport rename transported
    obtain ⟨_, current, cutAccepted, cutNext⟩ := split_rewrite accepted
    rw [rewrite_cons]
    exact Option.bind_eq_some_iff.mpr
      ⟨mapBody rename current, Option.map_eq_some_iff.mpr ⟨_, Reindex.cut_transport rename first cutAccepted, rfl⟩,
        ih remaining cutNext⟩

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Sequence.Proofs

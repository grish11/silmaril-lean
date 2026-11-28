module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery.MemRef.CF.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Proofs

open RVSDG (Tuple)
open SeaOfNodes.Diamond (Slot)
open Silmaril.MLIR.MemRef (Buffer)
open Memory.Forwarding.Disjoint (Certificate)
open Discovery.MemRef.CF (entryDestination entryTransition lowerDiamond lowerDiamond_entryTransition
  lowerDiamond_run run)

variable {args : List ValueSort} {cells : Nat}
variable {source : Prefixed args} {candidate : Candidate args} {rewritten : Graph args}
variable {result : Discovery.Result args}

theorem rewriteWith_readers_empty (accepted : rewriteWith source candidate = some rewritten) (arrival : Slot) :
    (candidate arrival).readers = [] := by
  unfold rewriteWith at accepted
  split at accepted
  next checked =>
    obtain ⟨first, second⟩ := Bool.and_eq_true_iff.mp checked
    cases arrival
    · exact List.isEmpty_iff.mp first
    · exact List.isEmpty_iff.mp second
  next => contradiction

theorem rewriteWith_replay (accepted : rewriteWith source candidate = some rewritten)
    (input : Tuple (Val cells) args) :
    DeadStore.rewrite source candidate input = some rewritten := by
  have empty := rewriteWith_readers_empty accepted
  have checked : ((candidate .first).readers.isEmpty && (candidate .second).readers.isEmpty) = true := by
    simp [empty]
  have slots : DeadStore.rewriteSlot source candidate input = rewriteSlot source candidate := by
    funext arrival
    simp [DeadStore.rewriteSlot, DeadStore.rewriteArm, rewriteSlot, Memory.DeadStore.rewrite, Certificate.check,
      empty arrival]
  simpa only [rewriteWith, ite_eq_left checked, DeadStore.rewrite, slots] using accepted

theorem rewrite_replay (accepted : rewrite source = some result) (input : Tuple (Val cells) args) :
    Discovery.rewrite source input = some result := by
  obtain ⟨candidate, found, cut⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨edited, editedEq, rfl⟩ := Option.map_eq_some_iff.mp cut
  exact Option.bind_eq_some_iff.mpr ⟨candidate, found,
    Option.bind_eq_some_iff.mpr ⟨edited, rewriteWith_replay editedEq input, rfl⟩⟩

theorem rewrite_readers_empty (accepted : rewrite source = some result) (arrival : Slot) :
    (result.candidate arrival).readers = [] := by
  obtain ⟨_, _, cut⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨_, edited, rfl⟩ := Option.map_eq_some_iff.mp cut
  exact rewriteWith_readers_empty edited arrival

variable {graph : Graph args} {entry : Memory.Graph args} {artifacts : Artifacts cells args}

theorem lower_replay (emitted : lower cells graph entry = some artifacts) (input : Tuple (Val cells) args) :
    ∃ store result, Composition.asPrefixStore entry = some store ∧
      Discovery.rewrite ⟨store, graph⟩ input = some result ∧
      artifacts = ⟨lowerDiamond cells graph (some entry), lowerDiamond cells result.graph none⟩ := by
  obtain ⟨store, recognized, remaining⟩ := Option.bind_eq_some_iff.mp emitted
  obtain ⟨edited, accepted, packed⟩ := Option.bind_eq_some_iff.mp remaining
  exact ⟨store, edited, recognized, rewrite_replay accepted input, (Option.some.inj packed).symm⟩

theorem lower_observations (emitted : lower cells graph entry = some artifacts)
    (input : Tuple (Val cells) args) (guard : Bool) (fuel : Nat) (initial : Buffer cells) :
    let result := graph.denote guard input (entry.denote input initial.cell).2
    let expected := if fuel < 3 then none else some (result.1, Buffer.mk result.2)
    entryDestination artifacts.optimized input guard initial =
      entryDestination artifacts.original input guard initial ∧
      run artifacts.original input guard fuel initial = expected ∧
      run artifacts.optimized input guard fuel initial = expected := by
  obtain ⟨store, edited, recognized, replay, rfl⟩ := lower_replay emitted input
  have same := (Discovery.rewrite_denote input replay guard initial.cell).trans
    (congrArg (graph.denote guard input) (Composition.asPrefixStore_heap recognized input initial.cell))
  constructor
  · simp only [entryDestination, lowerDiamond_entryTransition, Discovery.rewrite_merge input replay]
  · simp only [lowerDiamond_run, same, and_self]

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Proofs

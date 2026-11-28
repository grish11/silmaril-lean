module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.StoreTail.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Final.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Final.LoadTail.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Sequence.Search.Inference.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery.MemRef.CF.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Disjoint.Thms
import Silmaril.SSA.SeaOfNodes.Memory.MLIR.MemRef.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.StoreTail.Proofs

open RVSDG (Origin Tuple)
open Retained.Load.Static.Sequence.Search
open Discovery.MemRef.CF (entryDestination entryTransition lowerDiamond lowerDiamond_entryTransition lowerDiamond_run run)
open Memory.Forwarding.Disjoint (Certificate cell)
open Memory.DeadStore.Search.Selection.Readers.Repeat (DeletesStores operations)
open Silmaril.MLIR.MemRef (Buffer)
open SeaOfNodes.Memory.MLIR.MemRef (observe lower_run)
open Final.LoadTail (entryWord)

variable {args : List ValueSort} {cells : Nat}
variable {facts : Certificate args} {input : Tuple (Val cells) args}

private theorem checkTail_safe {past : List (List ValueSort)} {live : Nat}
    (tail : Memory.Body args past live) (store : PrefixStore args)
    (accepted : checkTail facts store tail = true) (valid : facts.Valid input) :
    Retained.Load.checkTail store input tail = true := by
  cases tail with
  | ret => contradiction
  | load => contradiction
  | store _ address _ rest =>
    cases address with
    | output => contradiction
    | arg writer =>
      simp only [checkTail, Bool.and_eq_true_iff] at accepted
      obtain ⟨anchor, ⟨_, covered⟩, tailSafe⟩ := accepted
      have matched : cell input store.address = cell input facts.observed :=
        facts.matches_read (.arg store.address : Origin args [] .address) anchor input PUnit.unit
      have distinct : cell input store.address ≠ cell input writer := by
        rw [matched]
        exact facts.covers_read (.arg writer : Origin args [] .address) covered input PUnit.unit valid
      have restSafe : Retained.Load.checkTail store input rest = true := by
        cases rest with
        | ret => rfl
        | load => exact Final.LoadTail.checkTail_disjoint _ store tailSafe valid
        | store => exact Final.LoadTail.checkTail_disjoint _ store tailSafe valid
      simp [Retained.Load.checkTail, distinct, restSafe]

theorem cut_preserves {entry retained : Memory.Graph args} {version : Nat} {store : PrefixStore args}
    (accepted : cut facts version entry = some (store, retained)) (valid : facts.Valid input) (initial : Heap cells) :
    DeletesStores 1 (operations entry) (operations retained) ∧
      entry.denote input initial =
        ((retained.denote input initial).1, (store.table.denote input (retained.denote input initial).2).2) := by
  obtain ⟨order, same⟩ := Final.cutWith_disjoint_preserves input (checkTail facts)
    (fun tail selected safe => checkTail_safe tail selected safe valid) accepted
  exact ⟨order, same PUnit.unit initial⟩

variable {graph : Graph args} {entry : Memory.Graph args} {version : Nat} {artifacts : Artifacts cells args}

theorem emit_replay (emitted : emit cells graph entry version facts = some artifacts) (input : Tuple (Val cells) args) :
    ∃ store retained edited, cut facts version entry = some (store, retained) ∧
      Discovery.rewrite ⟨store, graph⟩ input = some edited ∧
      artifacts = ⟨lowerDiamond cells graph (some entry), lowerDiamond cells edited.graph (some retained)⟩ := by
  obtain ⟨⟨store, retained⟩, checked, next⟩ := Option.bind_eq_some_iff.mp emitted
  obtain ⟨edited, accepted, packed⟩ := Option.bind_eq_some_iff.mp next
  exact ⟨store, retained, edited, checked, Static.rewrite_replay accepted input, (Option.some.inj packed).symm⟩

theorem emit_entry (emitted : emit cells graph entry version facts = some artifacts)
    (valid : facts.Valid input) (guard : Bool) (initial : Buffer cells) :
    ∃ store retained, cut facts version entry = some (store, retained) ∧
      entryWord artifacts.optimized input initial = entryWord artifacts.original input initial ∧
      let entered := entryTransition artifacts.optimized input guard initial
      entryTransition artifacts.original input guard initial =
        (entered.1, ⟨(store.table.denote input entered.2.cell).2⟩) := by
  obtain ⟨store, retained, edited, checked, replay, rfl⟩ := emit_replay emitted input
  have transfer := (cut_preserves checked valid initial.cell).2
  refine ⟨store, retained, checked, ?_, ?_⟩
  · change some (observe retained input initial).1 = some (observe entry input initial).1
    rw [lower_run, lower_run]
    exact congrArg some (congrArg Prod.fst transfer).symm
  · simp only [lowerDiamond_entryTransition, Discovery.rewrite_merge input replay]
    rw [congrArg Prod.snd transfer]

theorem emit_observations (emitted : emit cells graph entry version facts = some artifacts)
    (valid : facts.Valid input) (guard : Bool) (fuel : Nat) (initial : Buffer cells) :
    let result := graph.denote guard input (entry.denote input initial.cell).2
    let expected := if fuel < 3 then none else some (result.1, Buffer.mk result.2)
    entryDestination artifacts.optimized input guard initial = entryDestination artifacts.original input guard initial ∧
      run artifacts.original input guard fuel initial = expected ∧
      run artifacts.optimized input guard fuel initial = expected := by
  obtain ⟨store, retained, edited, checked, replay, rfl⟩ := emit_replay emitted input
  have transfer := (cut_preserves checked valid initial.cell).2
  have heap := congrArg Prod.snd transfer
  have same := (Discovery.rewrite_denote input replay guard (Memory.Graph.denote retained input initial.cell).2).trans
    (congrArg (graph.denote guard input) heap.symm)
  constructor
  · simp only [entryDestination, lowerDiamond_entryTransition, Discovery.rewrite_merge input replay]
  · simp only [lowerDiamond_run, same, and_self]

variable {result : Final.LoadTail.Result cells args}

theorem lower_checked (emitted : lower graph entry version input facts = .ok result) :
    Inference.lower graph entry input = .ok result.entryOnly ∧
      Retained.Load.Static.Sequence.lower graph entry result.entryOnly.plan input = some result.entryOnly.programs ∧
      match result.routes with
      | none => result.programs = result.entryOnly.programs
      | some artifacts =>
        facts.Valid input ∧ emit cells graph result.entryOnly.entry version facts = some artifacts ∧
          artifacts.original = result.entryOnly.programs.optimized := by
  have stage := Inference.lower_eq_ok graph entry input
  simp only [lower, Inference.lower_eq_ok] at emitted
  cases Except.ok.inj emitted
  refine ⟨stage, (Inference.lower_checked stage).1, ?_⟩
  by_cases valid : facts.check input = true
  · cases routed : emit cells graph (discover entry (Inference.inferContracts entry)).entry version facts with
    | none => simp [valid, Final.LoadTail.Result.programs]
    | some artifacts =>
      obtain ⟨_, _, _, _, _, packed⟩ := emit_replay routed input
      simp only [ite_eq_left valid, true_and]
      exact ⟨(facts.check_iff_valid input).mp valid, congrArg Artifacts.original packed⟩
  · simp [valid, Final.LoadTail.Result.programs]

theorem lower_observations (emitted : lower graph entry version input facts = .ok result)
    (guard : Bool) (fuel : Nat) (initial : Buffer cells) :
    let programs := result.programs
    let observed := graph.denote guard input (entry.denote input initial.cell).2
    let expected := if fuel < 3 then none else some (observed.1, Buffer.mk observed.2)
    entryDestination programs.optimized programs.input guard initial =
      entryDestination programs.original programs.input guard initial ∧
      run programs.original programs.input guard fuel initial = expected ∧
      run programs.optimized programs.input guard fuel initial = expected := by
  obtain ⟨entryReplay, _, routeReplay⟩ := lower_checked emitted
  have first := Inference.lower_observations entryReplay guard fuel initial
  let stage := result.entryOnly.programs
  have sameDestination : entryDestination stage.optimized stage.input guard initial =
      entryDestination stage.original stage.input guard initial :=
    congrArg Prod.fst first.1
  cases outcome : result.routes with
  | none => simpa only [Final.LoadTail.Result.programs, outcome] using And.intro sameDestination first.2
  | some artifacts =>
    rw [outcome] at routeReplay
    obtain ⟨valid, routed, linked⟩ := routeReplay
    have second := emit_observations routed valid guard fuel initial
    rw [linked] at second
    have sameInput : stage.input = input := by
      rw [Inference.lower_eq_ok] at entryReplay
      exact congrArg (fun emission : Emission cells args => emission.programs.input) (Except.ok.inj entryReplay).symm
    rw [← sameInput] at second
    simp only [Final.LoadTail.Result.programs, outcome]
    exact ⟨second.1.trans sameDestination, first.2.1, (second.2.2.trans second.2.1.symm).trans first.2.2⟩

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.StoreTail.Proofs

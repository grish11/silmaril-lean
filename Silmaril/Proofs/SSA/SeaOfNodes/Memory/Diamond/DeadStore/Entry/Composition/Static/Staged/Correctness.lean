module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Staged.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Sequence.Search.Inference.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Staged.Proofs

open RVSDG (Tuple)
open Silmaril.MLIR.MemRef (Buffer)
open Discovery.MemRef.CF (entryDestination run)
open Retained.Load.Static
open Retained.Load.Static.Sequence.Search

variable {args : List ValueSort} {cells : Nat}
variable {graph : Graph args} {entry : Memory.Graph args} {input : Tuple (Val cells) args}
variable {result : Staged.Result cells args}

theorem lower_eq_ok (graph : Graph args) (entry : Memory.Graph args) (input : Tuple (Val cells) args) :
    let found := discover entry (Inference.inferContracts entry)
    let stage : Emission cells args := ⟨found, Entry.lowerPair graph entry found.entry input⟩
    lower graph entry input = .ok ⟨stage, checkRoutes cells graph stage.entry⟩ := by
  simp only [lower, Inference.lower_eq_ok]
  rfl

theorem lower_checked (emitted : lower graph entry input = .ok result) :
    Inference.lower graph entry input = .ok result.entryOnly ∧
      Sequence.lower graph entry result.entryOnly.plan input = some result.entryOnly.programs ∧
      match result.route with
      | .entryNotSingleton => Composition.asPrefixStore result.entryOnly.entry = none
      | .routesRefused =>
        (Composition.asPrefixStore result.entryOnly.entry).isSome = true ∧
          Static.lower cells graph result.entryOnly.entry = none
      | .applied artifacts =>
        Static.lower cells graph result.entryOnly.entry = some artifacts ∧
          artifacts.original = result.entryOnly.programs.optimized := by
  rw [lower_eq_ok] at emitted
  cases Except.ok.inj emitted
  have stage := Inference.lower_eq_ok graph entry input
  refine ⟨stage, (Inference.lower_checked stage).1, ?_⟩
  cases routed : Static.lower cells graph (discover entry (Inference.inferContracts entry)).entry with
  | none =>
    cases shape : Composition.asPrefixStore (discover entry (Inference.inferContracts entry)).entry <;>
      simp [checkRoutes, routed, shape]
  | some artifacts =>
    obtain ⟨_, _, _, _, packed⟩ := Static.lower_replay routed input
    simp only [checkRoutes, routed]
    exact ⟨True.intro, congrArg Artifacts.original packed⟩

theorem lower_observations (emitted : lower graph entry input = .ok result)
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
  cases outcome : result.route with
  | entryNotSingleton | routesRefused =>
    simpa only [Result.programs, outcome] using And.intro sameDestination first.2
  | applied artifacts =>
    rw [outcome] at routeReplay
    obtain ⟨routed, linked⟩ := routeReplay
    have second := Static.lower_observations routed stage.input guard fuel initial
    rw [linked] at second
    simp only [Result.programs, outcome]
    refine ⟨second.1.trans sameDestination, first.2.1, ?_⟩
    exact (second.2.2.trans second.2.1.symm).trans first.2.2

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Staged.Proofs

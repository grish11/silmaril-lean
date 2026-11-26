module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Final.Staged.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Final.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Sequence.Search.Inference.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Final.Staged.Proofs

open RVSDG (Tuple)
open Silmaril.MLIR.MemRef (Buffer)
open Discovery.MemRef.CF (entryDestination run)
open Memory.DeadStore.Search.Selection (storeVersions)
open Memory.DeadStore.Search.Selection.Readers.Repeat (storeCount)
open Retained.Load.Static
open Retained.Load.Static.Sequence.Search

variable {args : List ValueSort} {cells : Nat}
variable {graph : Graph args} {entry : Memory.Graph args} {input : Tuple (Val cells) args}
variable {result : Staged.Result cells args}

private theorem cut_version {past : List (List ValueSort)} {live version : Nat}
    {body retained : Memory.Body args past live} {store : PrefixStore args}
    (accepted : Final.cut version body = some (store, retained)) : live + storeCount body = version := by
  induction body with
  | ret => contradiction
  | load _ _ _ ih =>
    obtain ⟨⟨_, _⟩, checked, packed⟩ := Option.map_eq_some_iff.mp accepted
    cases packed
    exact ih checked
  | store _ _ _ _ ih =>
    simp only [Final.cut, Final.cutWith] at accepted
    split at accepted
    next chosen =>
      split at accepted
      · split at accepted
        · simpa [storeCount, storeVersions] using chosen
        · contradiction
      · contradiction
    next =>
      obtain ⟨⟨_, _⟩, checked, packed⟩ := Option.map_eq_some_iff.mp accepted
      cases packed
      have count := ih checked
      simp only [storeCount, storeVersions, List.length_cons] at count ⊢
      omega

theorem find_eq_some_iff (entry : Memory.Graph args) (version : Nat) :
    find entry = some version ↔ ∃ store retained, Final.cut version entry = some (store, retained) := by
  constructor
  · intro found
    obtain ⟨⟨store, retained⟩, checked, equal⟩ := Option.map_eq_some_iff.mp found
    cases equal
    exact ⟨store, retained, checked⟩
  · rintro ⟨_, _, checked⟩
    have finalVersion : storeCount entry = version := by simpa only [Nat.zero_add] using cut_version checked
    subst version
    simp [find, checked]

theorem find_none_iff (entry : Memory.Graph args) :
    find entry = none ↔ ∀ version, Final.cut version entry = none := by
  constructor
  · intro absent version
    cases checked : Final.cut version entry with
    | none => rfl
    | some edit =>
      have found := (find_eq_some_iff entry version).mpr ⟨edit.1, edit.2, checked⟩
      simp [absent] at found
  · intro refused
    simp [find, refused]

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
      | .noFinalCandidate => find result.entryOnly.entry = none
      | .routesRefused version =>
        find result.entryOnly.entry = some version ∧ Final.lower cells graph result.entryOnly.entry version = none
      | .applied version artifacts =>
        find result.entryOnly.entry = some version ∧ Final.lower cells graph result.entryOnly.entry version = some artifacts ∧
          artifacts.original = result.entryOnly.programs.optimized := by
  rw [lower_eq_ok] at emitted
  cases Except.ok.inj emitted
  have stage := Inference.lower_eq_ok graph entry input
  refine ⟨stage, (Inference.lower_checked stage).1, ?_⟩
  cases found : find (discover entry (Inference.inferContracts entry)).entry with
  | none => simp [checkRoutes, found]
  | some version =>
    cases routed : Final.lower cells graph (discover entry (Inference.inferContracts entry)).entry version with
    | none => simp [checkRoutes, found, routed]
    | some artifacts =>
      obtain ⟨_, _, _, _, _, packed⟩ := Final.lower_replay routed input
      simp only [checkRoutes, found, routed, true_and]
      exact congrArg Artifacts.original packed

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
  | noFinalCandidate | routesRefused _ =>
    simpa only [Result.programs, outcome] using And.intro sameDestination first.2
  | applied version artifacts =>
    rw [outcome] at routeReplay
    obtain ⟨_, routed, linked⟩ := routeReplay
    have second := Final.lower_observations routed stage.input guard fuel initial
    rw [linked] at second
    simp only [Result.programs, outcome]
    exact ⟨second.1.trans sameDestination, first.2.1, (second.2.2.trans second.2.1.symm).trans first.2.2⟩

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Final.Staged.Proofs

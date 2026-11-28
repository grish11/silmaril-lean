module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence.Discovery.Defs
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence.Discovery

open Silmaril.MLIR.Arith (Width)
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence.Discovery

variable {Input : List Width} {saved carried result : Width} {origin : Nat}
variable {source : Layout.Output Input saved carried result} {plan : Plan source}

theorem hoist?_none_iff :
    hoist? source origin = none ↔
    ∀ ranked, Layout.PreheaderSearch.rank? source.2 origin 0 = some ranked →
      ranked.crossBlock.selectedMove? = none := by
  unfold hoist?
  split
  · rename_i refused
    simp [refused]
  · rename_i ranked checked
    split
    · rename_i retained
      simp [checked, retained]
    · rename_i moved selected
      simp [checked, selected]

theorem choose?_some {chosen : Hoist source origin} (found : choose? source = some ⟨origin, chosen⟩) :
    origin ∈ source.2.reference.origins ∧ hoist? source origin = some chosen := by
  obtain ⟨index, member, candidate⟩ := List.exists_of_findSome?_eq_some found
  obtain ⟨hoist, checked, same⟩ := Option.map_eq_some_iff.mp candidate
  cases same
  exact ⟨member, checked⟩

theorem choose?_none_iff :
    choose? source = none ↔ ∀ origin ∈ source.2.reference.origins, hoist? source origin = none := by
  simp only [choose?, List.findSome?_eq_none_iff, Option.map_eq_none_iff]

theorem hoist_moves (hoist : Hoist source origin) :
    ∃ cut, Layout.emit? source.2 ⟨origin, cut⟩ = some hoist.move ∧
      hoist.choice.ranked.selection.1 = ⟨none, cut⟩ ∧
      hoist.choice.ranked.selection.2 = ⟨_, hoist.move.next⟩ ∧
      source.2.reference.origins[hoist.move.append.index]? = some origin ∧
      hoist.choice.ranked.selection.2.2.reference.origins =
        source.2.reference.origins.eraseIdx hoist.move.append.index := by
  obtain ⟨cut, latest, point, out⟩ := Layout.PreheaderSearch.rank?_hoist hoist.choice.checked hoist.selected
  have emitted := (Layout.PreheaderSearch.latest?_some latest).2
  have append := Step.emit_spec (Layout.emit?_spec emitted).1
  refine ⟨cut, emitted, point, out, (Layout.emit?_placement emitted).1, ?_⟩
  rw [out]
  exact append.2.2.2.2.2.1

theorem hoist_decreases (hoist : Hoist source origin) :
    hoist.choice.ranked.selection.2.2.reference.origins.length + 1 = source.2.reference.origins.length := by
  obtain ⟨_, _, _, _, present, erased⟩ := hoist_moves hoist
  rw [erased, List.length_eraseIdx_of_lt (List.getElem?_eq_some_iff.mp present).1]
  have bound := (List.getElem?_eq_some_iff.mp present).1
  omega

theorem collect_replay (source : Layout.Output Input saved carried result) (budget position : Nat) :
    let plan := collect source budget
    Layout.PreheaderSearch.Sequence.run source position plan.requests = .ok plan.trace := by
  induction budget generalizing source position with
  | zero => rfl
  | succ budget ih =>
    cases picked : choose? source with
    | none =>
      rw [collect, picked]
      rfl
    | some candidate =>
      rcases candidate with ⟨_, hoist⟩
      rw [collect, picked]
      exact (Layout.PreheaderSearch.Sequence.run_continue hoist.choice position).trans (by rw [ih]; rfl)

theorem collect_count (source : Layout.Output Input saved carried result) (budget : Nat) :
    let plan := collect source budget
    plan.output.2.reference.origins.length + plan.requests.length = source.2.reference.origins.length := by
  induction budget generalizing source with
  | zero => simp [collect, Plan.output, Layout.PreheaderSearch.Sequence.Trace.output]
  | succ budget ih =>
    cases picked : choose? source with
    | none =>
      rw [collect, picked]
      rfl
    | some candidate =>
      rcases candidate with ⟨_, hoist⟩
      rw [collect, picked]
      simp only [Plan.output, Layout.PreheaderSearch.Sequence.Trace.output, List.length_cons]
      have rest := ih hoist.choice.ranked.selection.2
      change (collect hoist.choice.ranked.selection.2 budget).trace.output.2.reference.origins.length +
        (collect hoist.choice.ranked.selection.2 budget).requests.length =
        hoist.choice.ranked.selection.2.2.reference.origins.length at rest
      have decrease := hoist_decreases hoist
      omega

theorem collect_terminal {budget : Nat} (enough : source.2.reference.origins.length ≤ budget) :
    choose? (collect source budget).output = none := by
  induction budget generalizing source with
  | zero =>
    have empty : source.2.reference.origins = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero enough)
    simp [collect, Plan.output, Layout.PreheaderSearch.Sequence.Trace.output, choose?, empty]
  | succ budget ih =>
    cases picked : choose? source with
    | none =>
      rw [collect, picked]
      exact picked
    | some candidate =>
      rcases candidate with ⟨_, hoist⟩
      have decrease := hoist_decreases hoist
      have remaining : hoist.choice.ranked.selection.2.2.reference.origins.length ≤ budget := by omega
      rw [collect, picked]
      exact ih remaining

theorem schedule?_spec (accepted : schedule? source = some plan) (position : Nat) :
    Layout.Discovery.supported? source.2 = true ∧
    Layout.PreheaderSearch.Sequence.run source position plan.requests = .ok plan.trace ∧
    plan.output.2.reference.origins.length + plan.requests.length = source.2.reference.origins.length ∧
    ∀ origin ∈ plan.output.2.reference.origins, ∀ ranked,
      Layout.PreheaderSearch.rank? plan.output.2 origin 0 = some ranked →
        ranked.crossBlock.selectedMove? = none := by
  unfold schedule? at accepted
  split at accepted
  · rename_i supported
    cases accepted
    exact ⟨supported, collect_replay _ _ position, collect_count _ _,
      fun origin present ranked checked =>
        hoist?_none_iff.mp (choose?_none_iff.mp (collect_terminal (Nat.le_refl _)) origin present) ranked checked⟩
  · cases accepted

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence.Discovery

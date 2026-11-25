module

public import Silmaril.Languages.Python.Core.Closure.Finite.Defs
import Silmaril.Semantics.Operational.Environment.Finite.Thms
import Silmaril.Semantics.Operational.Projection.Thms

public section

namespace Silmaril.Proofs.Languages.Python.Core.Closure.Finite

open Silmaril.Languages.Python.Core.Closure
open Silmaril.Languages.Python.Core.Closure.Finite
open Silmaril.Semantics.Operational

theorem contents_outside (table : HeapTable) {address : Nat} (outside : table.next ≤ address) :
    table.project.contents address = none := by
  change Environment.Finite.view table.rows address = none
  cases present : Environment.Finite.view table.rows address with
  | none => rfl
  | some value => exact False.elim (Nat.not_lt_of_ge outside (table.bounded address value present))

theorem exists_project_iff (heap : Heap) :
    (∃ table : HeapTable, table.project = heap) ↔
      ∀ address, heap.next ≤ address → heap.contents address = none := by
  constructor
  · rintro ⟨table, rfl⟩ address outside
    exact contents_outside table outside
  · intro normalized
    have bounded (address : Nat) (value : Value) (found : heap.contents address = some value) :
        address < heap.next := by
      apply Nat.lt_of_not_ge
      intro outside
      rw [normalized address outside] at found
      cases found
    let rows := Environment.Finite.encode heap.contents (List.range heap.next)
    have projects : Environment.Finite.view rows = heap.contents :=
      Environment.Finite.view_encode (fun address value found => List.mem_range.mpr (bounded address value found))
    refine ⟨⟨heap.next, rows, ?_⟩, congrArg (Heap.mk heap.next) projects⟩
    rw [projects]
    exact bounded

theorem reserve_project (table : HeapTable) (count : Nat) :
    (table.reserve count).project = table.project.reserve count := by
  apply congrArg (Heap.mk (table.next + count))
  funext address
  change table.project.contents address = if address < table.next then table.project.contents address else none
  by_cases allocated : address < table.next
  · simp [allocated]
  · simpa [allocated] using contents_outside table (Nat.le_of_not_gt allocated)

theorem write_project (table : HeapTable) (identity : CellId) (value : Value) :
    (table.write identity value).map HeapTable.project = table.project.write identity value := by
  by_cases allocated : identity.address < table.next
  · simp [HeapTable.write, Heap.write, HeapTable.project, allocated, HeapTable.bind,
      Environment.Finite.view_insert]
    rfl
  · simp [HeapTable.write, Heap.write, HeapTable.project, allocated]

variable {layout : Layout}

private theorem writeCell_project (source : Snapshot layout) (identity : CellId) (value : Value) :
    let next := source.writeCell identity value
    (next.1, next.2.project) =
      match source.frame.writeCell source.heap.project identity value with
      | .ok next => (.write (.ok ()), next)
      | .error failure => (.write (.error failure), source.project) := by
  have agrees := write_project source.heap identity value
  cases written : source.heap.write identity value with
  | none => simp [written] at agrees
            simp [Snapshot.writeCell, Frame.writeCell, written, ← agrees]
  | some heap => simp [written] at agrees
                 simp [Snapshot.writeCell, Frame.writeCell, written, ← agrees, Snapshot.project]

theorem execute_project (source : Snapshot layout) (request : Request layout) :
    let next := source.execute request
    (next.1, next.2.project) = execute source.project request := by
  cases request with
  | read slot => rfl
  | write slot value =>
    cases slot with
    | «local» index => rfl
    | owned index => exact writeCell_project source (source.frame.owned index) value
    | capture index => exact writeCell_project source (source.frame.captures index) value
  | fresh captures =>
    change (Response.fresh, ((source.heap.reserve layout.owned).project,
        (Frame.fresh source.heap.project captures).2)) = (Response.fresh, Frame.fresh source.heap.project captures)
    rw [reserve_project]
    rfl

theorem projection (layout : Layout) :
    Projection (presented layout) (semantic layout) Snapshot.project id where
  sound {source action target} moved := by
    change source.execute action.1 = (action.2, target) at moved
    change execute source.project action.1 = (action.2, target.project)
    rw [← execute_project source action.1, moved]
  readback {source action target} moved := by
    change execute source.project action.1 = (action.2, target) at moved
    rw [← execute_project source action.1] at moved
    refine ⟨action, (source.execute action.1).2, ?_, rfl, congrArg Prod.snd moved⟩
    change source.execute action.1 = (action.2, (source.execute action.1).2)
    have response : (source.execute action.1).1 = action.2 := congrArg Prod.fst moved
    exact Prod.ext response rfl

theorem step_iff {source : Snapshot layout} {action : Action layout} {target : Heap × Frame layout} :
    (semantic layout).Tr source.project action target ↔
      ∃ next, (presented layout).Tr source action next ∧ next.project = target := by
  rw [(projection layout).step_iff]
  constructor
  · rintro ⟨label, next, moved, rfl, projected⟩
    exact ⟨next, moved, projected⟩
  · rintro ⟨next, moved, projected⟩
    exact ⟨action, next, moved, rfl, projected⟩

theorem execution_readback {source : Snapshot layout} {actions : List (Action layout)}
    {target : Heap × Frame layout} {states : List (Heap × Frame layout)}
    (run : (semantic layout).Execution source.project actions target states) :
    ∃ final witnesses, (presented layout).Execution source actions final witnesses ∧
      witnesses.map Snapshot.project = states ∧ final.project = target := by
  obtain ⟨final, labels, witnesses, lifted, actionsEq, statesEq, targetEq⟩ :=
    (projection layout).execution_readback run rfl
  simp only [List.map_id] at actionsEq
  subst labels
  exact ⟨final, witnesses, lifted, statesEq, targetEq⟩

end Silmaril.Proofs.Languages.Python.Core.Closure.Finite

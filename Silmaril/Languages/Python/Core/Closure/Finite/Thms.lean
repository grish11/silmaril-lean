module

public import Silmaril.Languages.Python.Core.Closure.Finite.Defs
import Silmaril.Proofs.Languages.Python.Core.Closure.Finite.Projection

public section

namespace Silmaril.Languages.Python.Core.Closure.Finite

open Semantics.Operational

variable {layout : Layout}

theorem HeapTable.contents_outside (table : HeapTable) {address : Nat} (outside : table.next ≤ address) :
    table.project.contents address = none :=
  Proofs.Languages.Python.Core.Closure.Finite.contents_outside table outside

/-- Raw heap equality requires that the backing map has no binding
at or beyond the allocation frontier. -/
theorem HeapTable.exists_project_iff (heap : Heap) :
    (∃ table : HeapTable, table.project = heap) ↔
      ∀ address, heap.next ≤ address → heap.contents address = none :=
  Proofs.Languages.Python.Core.Closure.Finite.exists_project_iff heap

theorem HeapTable.reserve_project (table : HeapTable) (count : Nat) :
    (table.reserve count).project = table.project.reserve count :=
  Proofs.Languages.Python.Core.Closure.Finite.reserve_project table count

theorem HeapTable.write_project (table : HeapTable) (identity : CellId) (value : Value) :
    (table.write identity value).map HeapTable.project = table.project.write identity value :=
  Proofs.Languages.Python.Core.Closure.Finite.write_project table identity value

theorem Snapshot.write_project (source : Snapshot layout) (slot : Slot layout) (value : Value) :
    (source.write slot value).map Snapshot.project =
      source.frame.write source.heap.project slot value :=
  Proofs.Languages.Python.Core.Closure.Finite.snapshot_write_project source slot value

theorem Snapshot.execute_project (source : Snapshot layout) (request : Request layout) :
    let next := source.execute request
    (next.1, next.2.project) = Finite.execute source.project request :=
  Proofs.Languages.Python.Core.Closure.Finite.execute_project source request

theorem projection (layout : Layout) :
    Projection (presented layout) (semantic layout) Snapshot.project id :=
  Proofs.Languages.Python.Core.Closure.Finite.projection layout

/-- Keep the complete request and response and recover the full successor
from the given finite source. -/
theorem step_iff {source : Snapshot layout} {action : Action layout} {target : Heap × Frame layout} :
    (semantic layout).Tr source.project action target ↔
      ∃ next, (presented layout).Tr source action next ∧ next.project = target :=
  Proofs.Languages.Python.Core.Closure.Finite.step_iff

/-- Thread the finite witness through every operation, preserving the
ordered actions and the projections of all visited states. -/
theorem execution_readback {source : Snapshot layout} {actions : List (Action layout)}
    {target : Heap × Frame layout} {states : List (Heap × Frame layout)}
    (run : (semantic layout).Execution source.project actions target states) :
    ∃ final witnesses, (presented layout).Execution source actions final witnesses ∧
      witnesses.map Snapshot.project = states ∧ final.project = target :=
  Proofs.Languages.Python.Core.Closure.Finite.execution_readback run

end Silmaril.Languages.Python.Core.Closure.Finite

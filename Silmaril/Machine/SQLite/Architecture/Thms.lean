module

public import Silmaril.Machine.SQLite.Architecture.Defs

public section

namespace Silmaril.Machine.SQLite.Architecture

theorem nodes_complete (node : Node) : node ∈ nodes := by
  cases node <;> decide

theorem labels_unique : nodes.Nodup ∧ (nodes.map label).Nodup := by decide

theorem groups_exact :
    nodes.filter (fun node => (parent node).isNone) =
      [.core, .backend, .compiler, .accessories] := by decide

theorem mem_containment (group child : Node) :
    (group, child) ∈ containment ↔ parent child = some group := by
  simp [containment, Option.map_eq_some_iff, nodes_complete, and_assoc, and_comm]

theorem containment_wellFormed :
    containment.length = 11 ∧ (containment.map Prod.snd).Nodup ∧
    containment.all (fun (group, child) =>
      (parent group).isNone && parent child == some group) = true := by decide

theorem edges_wellFormed :
    diagramArrows.length = 9 ∧ ∀ edges ∈ [diagramArrows, calls, dependencies],
      edges.Nodup ∧ edges.all (fun (source, target) =>
        (parent source).isSome && (parent target).isSome && source != target) = true := by
  decide

theorem calls_diagram_delta :
    diagramArrows.filter (fun edge => !calls.contains edge) =
      [(.codeGenerator, .commandProcessor)] ∧
    calls.filter (fun edge => !diagramArrows.contains edge) =
      [(.interface, .virtualMachine)] := by decide

end Silmaril.Machine.SQLite.Architecture

module

public import Silmaril.Logic.Graph.Examples.Defs
import Silmaril.Proofs.Logic.Graph.Examples

@[expose] public section
namespace Silmaril.Logic.Graph.Examples
open Silmaril.Semantics.Graph

theorem marker_loses_loop : markPresence withoutLoop = markPresence withLoop ∧ withoutLoop ≠ withLoop :=
  Proofs.marker_loses_loop

/-- Identifying vertices turns a genuine off-diagonal pair into a presence
marker. This is why marker naturality requires injectivity. -/
theorem marker_not_natural :
    ¬ (markPresence (presentReduct collapse withoutLoop)).edge false true ∧
      (reduct collapse (markPresence withoutLoop)).edge false true := by
  simp [markPresence, presentReduct, reduct, collapse, withoutLoop]
  rfl

theorem parallel_loss : oneEdge.relation = twoEdges.relation ∧ oneEdge ≠ twoEdges := Proofs.parallel_loss

theorem incomplete_loss : unknownEdge.relation = noEdge.relation ∧
    ¬ unknownEdge.Complete ∧ ¬ Incidence.Sat unknownEdge (.sourceKnown ()) := Proofs.incomplete_loss

theorem cross_base_isomorphic : Nonempty (Iso namedGraph indexedGraph) := ⟨Proofs.cross_base_iso⟩

noncomputable def crossBaseIso : Iso namedGraph indexedGraph := Classical.choice cross_base_isomorphic

theorem cross_base_minor : Nonempty (Minor namedGraph indexedGraph) := Minor.exists_of_iso crossBaseIso

theorem iteration_backedge : iteration.graph.edge 2 0 := by simp [iteration, Structured.graph, Structured.exit]

theorem iteration_wellformed : iteration.WellFormed := by
  simp [iteration, Structured.WellFormed, Structured.nodes]

end Silmaril.Logic.Graph.Examples

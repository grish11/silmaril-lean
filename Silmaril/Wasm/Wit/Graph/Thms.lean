module

public import Silmaril.Wasm.Wit.Graph.Defs
public import Silmaril.Prelude.FiniteGraph.Thms

/-! # Finite dependency graph laws used by WIT -/

public section

namespace Silmaril.Wasm.Wit.Graph

export Silmaril.FiniteGraph (kahn_of_any kahn_of_not_any krank_of_any not_mem_of_ready
  mem_nextRound nextRound_subset ranked_step bound_step kahn_sound exists_min ranked_mono
  ready_of_min kahn_complete kahn_iff acyclic_iff_edges kahn_bounded_edges)

end Silmaril.Wasm.Wit.Graph

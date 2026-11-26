module

public import Silmaril.Prelude.FiniteGraph.Defs

/-! # Finite dependency graph definitions used by WIT -/

public section

namespace Silmaril.Wasm.Wit.Graph

export Silmaril.FiniteGraph (Ranked Acyclic ready nextRound nextRound_lt kahn krank)

end Silmaril.Wasm.Wit.Graph

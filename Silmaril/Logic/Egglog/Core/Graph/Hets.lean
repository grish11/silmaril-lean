module

public import Silmaril.Logic.Egglog.Core.Graph.Thms
public import Silmaril.Logic.Institution.Hets.LogicGraph

@[expose] public section

namespace Silmaril.Logic.Egglog.Core.Graph.Hets

open CategoryTheory Silmaril.Logic.Institution

inductive Node where
  | normalizedCore
  | functionalFirstOrder

inductive Edge : Node → Node → Type where
  | graph : Edge .normalizedCore .functionalFirstOrder

/-- An actual institution edge; the target keeps partial-table functionality. -/
def logicGraph : LogicGraph where
  Logics := Node
  inst
    | .normalizedCore => Core.inst
    | .functionalFirstOrder => Graph.inst
  Comor := Edge
  comor e := match e with | .graph => fromCore
  Mor _ _ := PEmpty
  mor e := e.elim

theorem edge_path :
    IndexedCoInst.coHom logicGraph.indexed ((Paths.of logicGraph.Idx).map Edge.graph) = fromCore :=
  logicGraph.coHom_toPath Edge.graph

end Silmaril.Logic.Egglog.Core.Graph.Hets

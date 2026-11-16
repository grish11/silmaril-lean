module

public import Silmaril.Logic.Egglog.Core.Graph.Functional.Thms
public import Silmaril.Logic.Egglog.Core.Graph.Hets

@[expose] public section
namespace Silmaril.Logic.Egglog.Core.Graph.Functional.Hets
open CategoryTheory Silmaril.Logic.Institution

inductive Node where
  | normalizedCore
  | sameModelGraph
  | independentFunctional
  | unrestrictedPublic

inductive Edge : Node → Node → Type where
  | sameModel : Edge .normalizedCore .sameModelGraph
  | reconstruct : Edge .normalizedCore .independentFunctional
  | restrict : Edge .unrestrictedPublic .independentFunctional

/-- Distinct old and independent model layers, with the unrestricted restriction
in its actual comorphism direction. -/
def logicGraph : LogicGraph where
  Logics := Node
  inst
    | .normalizedCore => Core.inst
    | .sameModelGraph => Graph.inst
    | .independentFunctional => Functional.inst
    | .unrestrictedPublic => publicInst
  Comor := Edge
  comor e := match e with
    | .sameModel => Graph.fromCore
    | .reconstruct => Functional.fromCore
    | .restrict => restriction
  Mor _ _ := PEmpty
  mor e := e.elim

theorem reconstruct_path :
    IndexedCoInst.coHom logicGraph.indexed
      ((Paths.of logicGraph.Idx).map Edge.reconstruct) = Functional.fromCore :=
  logicGraph.coHom_toPath Edge.reconstruct

theorem restriction_path :
    IndexedCoInst.coHom logicGraph.indexed
      ((Paths.of logicGraph.Idx).map Edge.restrict) = restriction :=
  logicGraph.coHom_toPath Edge.restrict

end Silmaril.Logic.Egglog.Core.Graph.Functional.Hets

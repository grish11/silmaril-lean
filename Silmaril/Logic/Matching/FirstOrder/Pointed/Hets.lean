module

public import Silmaril.Logic.Matching.FirstOrder.Pointed.Propositional
public import Silmaril.Logic.Institution.Hets.LogicGraph

@[expose] public section
namespace Silmaril.Logic.Matching.FirstOrder.Pointed.Hets
open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Examples

inductive Node where
  | propositional
  | pointedMatching

inductive Edge : Node → Node → Type where
  | propositional : Edge .propositional .pointedMatching

/-- The proved incoming edge registered in the shared Hets logic graph API. -/
def logicGraph : LogicGraph where
  Logics := Node
  inst
    | .propositional => PL.inst
    | .pointedMatching => ⟨Algebraic.ManySorted.Signature Unit, institution ()⟩
  Comor := Edge
  comor e := match e with | .propositional => propositionalToPointedMatching
  Mor _ _ := PEmpty
  mor e := e.elim

/-- Hets path composition uses the actual proved translation. -/
theorem edge_path :
    IndexedCoInst.coHom logicGraph.indexed
      ((Paths.of logicGraph.Idx).map Edge.propositional) = propositionalToPointedMatching :=
  logicGraph.coHom_toPath Edge.propositional
end Silmaril.Logic.Matching.FirstOrder.Pointed.Hets

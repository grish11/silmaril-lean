module

public import Silmaril.Logic.Temporal.CTLStar.Thms
public import Silmaril.Logic.Institution.Hets.LogicGraph

@[expose] public section
namespace Silmaril.Logic.Temporal.CTLStar.Hets
open CategoryTheory Silmaril.Logic.Institution

inductive Node
  | ctl | discrete | rich

inductive Translation : Node → Node → Type
  | includeCTL : Translation .ctl .discrete
  | discretePresentation : Translation .rich .discrete

/-- An honest span: no rich-to-discrete model functor is asserted. -/
def graph : LogicGraph where
  Logics := Node
  inst
    | .ctl => ⟨Signature, CTL.institution⟩
    | .discrete => ⟨Signature, institution⟩
    | .rich => ⟨Signature, richInstitution⟩
  Comor := Translation
  comor
    | .includeCTL => ctlToCTLStar
    | .discretePresentation => richToDiscrete
  Mor _ _ := PEmpty
  mor edge := edge.elim

theorem edge_modelExpansive {a b : Node} (edge : Translation a b) :
    (graph.comor edge).ModelExpansive := by
  cases edge with
  | includeCTL => exact ctlToCTLStar_modelExpansive
  | discretePresentation => exact richToDiscrete_modelExpansive

/-- The CTL inclusion is an actual edge in the free Hets path category. -/
def inclusionPath : Quiver.Path (show graph.Idx from Node.ctl)
    (show graph.Idx from Node.discrete) := .cons .nil .includeCTL

end Silmaril.Logic.Temporal.CTLStar.Hets

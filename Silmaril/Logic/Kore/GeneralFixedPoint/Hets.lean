module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Institution.Defs
public import Silmaril.Logic.Institution.Hets.LogicGraph

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Hets
open CategoryTheory Silmaril.Logic.Institution

inductive Node where
  | positiveMatching
  | generalMatching
  | namedKore

inductive Translation : Node → Node → Type where
  | positive : Translation .positiveMatching .generalMatching
  | lower : Translation .namedKore .generalMatching

/-- Actual semantic graph edges with unchanged relational model categories.
The named endpoint checks local binder positivity, including mixed free polarity. -/
def graph : LogicGraph where
  Logics := Node
  inst
    | .positiveMatching => ⟨Algebraic.ManySorted.Signature String, Matching.FixedPoint.institution String⟩
    | .generalMatching => ⟨Algebraic.ManySorted.Signature String, Matching.GeneralFixedPoint.institution String⟩
    | .namedKore => ⟨Algebraic.ManySorted.Signature String, institution⟩
  Comor := Translation
  comor
    | .positive => Matching.GeneralFixedPoint.positiveComorphism
    | .lower => loweringComorphism
  Mor _ _ := PEmpty
  mor e := e.elim

theorem positive_modelExpansive :
    (graph.comor Translation.positive).ModelExpansive :=
  Matching.GeneralFixedPoint.positive_modelExpansive

theorem lower_modelExpansive : (graph.comor Translation.lower).ModelExpansive :=
  lowering_modelExpansive

theorem lower_path :
    IndexedCoInst.coHom graph.indexed
      ((Paths.of graph.Idx).map Translation.lower) = loweringComorphism :=
  graph.coHom_toPath Translation.lower
end Silmaril.Logic.Kore.GeneralFixedPoint.Hets

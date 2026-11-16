module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Institution.Defs
public import Silmaril.Logic.Institution.Hets.LogicGraph

@[expose] public section

/-! # A Hets logic graph for MLTT and semantic set constraints -/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Hets

open CategoryTheory Silmaril.Logic.Institution

universe u

noncomputable section

inductive Node : Type
  | mltt
  | setConstraints

inductive Translation : Node → Node → Type
  | realize : Translation .mltt .setConstraints

/-- Hets registers the proved semantic realization as a logic-translation edge. -/
noncomputable def graph : LogicGraph.{0, 0, 0, 0, u + 1, u + 1, u + 1} where
  Logics := Node
  inst
    | .mltt => Institution.bundled.{u}
    | .setConstraints => SetTheoryInterpretation.bundled.{u}
  Comor := Translation
  comor
    | .realize => SetTheoryInterpretation.toSetTheory.{u}
  Mor _ _ := PEmpty
  mor e := e.elim

/-- The one-edge path gives the same route as later composed Hets translations. -/
def realizationPath :
    Quiver.Path (show graph.{u}.Idx from Node.mltt)
      (show graph.{u}.Idx from Node.setConstraints) :=
  .cons .nil .realize

/-- The flattened source signature in the Grothendieck institution. -/
abbrev sourceSig : graph.{u}.Sig :=
  graph.sigOf .mltt (Discrete.mk ())

/-- The flattened signature reached by the realization path. -/
abbrev targetSig : graph.{u}.Sig :=
  IndexedCoInst.mkSig graph.indexed (graph.pt .setConstraints)
    ((IndexedCoInst.coHom graph.indexed (graph.pathHom realizationPath)).Φ.obj (Discrete.mk ()))

/-- Heterogeneous translation along the path in the flattened institution. -/
abbrev realizationLift : sourceSig.{u} ⟶ targetSig.{u} :=
  IndexedCoInst.lift graph.indexed (graph.pathHom realizationPath) (Discrete.mk ())

/-- A concrete closed judgment used to exercise the logic translation. -/
def unitJudgment : EJdg := ⟨.nil, .unit, .star, .star⟩

end

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Hets

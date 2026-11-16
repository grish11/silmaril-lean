module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Mutual.Apex.Thms
public import Silmaril.Logic.Institution.Hets.LogicGraph

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Mutual.Apex.Hets

open CategoryTheory Silmaril.Logic.Institution

universe u

noncomputable section

inductive Node where
  | stage (levels : ℕ)
  | indexedStage (levels : ℕ)
  | mutualApex
  | indexedApex
  | ordinaryWApex
  | setConstraints

inductive Translation : Node → Node → Type
  | apex (levels : ℕ) : Translation (.stage levels) .mutualApex
  | stageFlatten (levels : ℕ) : Translation (.stage levels) (.indexedStage levels)
  | indexedApex (levels : ℕ) : Translation (.indexedStage levels) .indexedApex
  | stageLevels {n m : ℕ} (h : n ≤ m) : Translation (.stage n) (.stage m)
  | indexedStageLevels {n m : ℕ} (h : n ≤ m) : Translation (.indexedStage n) (.indexedStage m)
  | flatten : Translation .mutualApex .indexedApex
  | compile : Translation .indexedApex .ordinaryWApex
  | directCompile : Translation .mutualApex .ordinaryWApex
  | ordinary : Translation .ordinaryWApex .mutualApex
  | realize : Translation .ordinaryWApex .setConstraints

/-- Genuine mutual and indexed finite stages, hierarchy apices and set realization. -/
def graph : LogicGraph.{0, 0, 0, 0, u + 1, u + 1, u + 1} where
  Logics := Node
  inst
    | .stage n => Stage.bundled.{u} n
    | .indexedStage n => Indexed.Apex.Stage.bundled.{u} n
    | .mutualApex => Apex.bundled.{u}
    | .indexedApex => Indexed.Apex.bundled.{u}
    | .ordinaryWApex => W.Institution.bundled.{u}
    | .setConstraints => ExtensionalMLTT.SetTheoryInterpretation.bundled.{u}
  Comor := Translation
  comor
    | .apex n => Stage.toApex n
    | .stageFlatten n => Stage.toIndexed n
    | .indexedApex n => Indexed.Apex.Stage.toApex n
    | .stageLevels h => Stage.inclusion h
    | .indexedStageLevels h => Indexed.Apex.Stage.inclusion h
    | .flatten => Apex.toIndexed
    | .compile => Indexed.Apex.toW
    | .directCompile => Apex.toW
    | .ordinary => Apex.fromW
    | .realize => W.SetTheoryInterpretation.toSetTheory
  Mor _ _ := PEmpty
  mor e := e.elim

/-- Simultaneous hierarchy flattening, indexed compilation and actual W set realization. -/
def realizationPath : Quiver.Path (show graph.{u}.Idx from Node.mutualApex)
    (show graph.{u}.Idx from Node.setConstraints) :=
  .cons (.cons (.cons .nil .flatten) .compile) .realize

/-- Reduce a supplied hierarchy to the finite tower used by a mutual source proof. -/
def stagePath (levels : ℕ) : Quiver.Path (show graph.{u}.Idx from Node.stage levels)
    (show graph.{u}.Idx from Node.setConstraints) :=
  .cons (.cons (.cons (.cons .nil (.apex levels)) .flatten) .compile) .realize

/-- The alternative route flattens at the finite stage before entering the indexed apex. -/
def indexedStagePath (levels : ℕ) : Quiver.Path (show graph.{u}.Idx from Node.stage levels)
    (show graph.{u}.Idx from Node.setConstraints) :=
  .cons (.cons (.cons (.cons .nil (.stageFlatten levels)) (.indexedApex levels)) .compile) .realize

abbrev sourceSig : graph.{u}.Sig := graph.sigOf .mutualApex (Discrete.mk ())

abbrev targetSig : graph.{u}.Sig :=
  IndexedCoInst.mkSig graph.indexed (graph.pt .setConstraints)
    ((IndexedCoInst.coHom graph.indexed (graph.pathHom realizationPath)).Φ.obj (Discrete.mk ()))

abbrev realizationLift : sourceSig.{u} ⟶ targetSig.{u} :=
  IndexedCoInst.lift graph.indexed (graph.pathHom realizationPath) (Discrete.mk ())

end

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Mutual.Apex.Hets

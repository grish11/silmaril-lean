module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Systems.Thms
public import Silmaril.Logic.Institution.Hets.LogicGraph

@[expose] public section

/-! # Hets graphs for the base calculus and its ordinary W extension

The finite graph has both languages at every universe count. Its edges add
available universes or add W at the same count. The hierarchy graph also
registers realization into the existing independent set-constraint language.
-/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Hets

open CategoryTheory Silmaril.Logic.Institution

universe u

namespace Finite

inductive Node : Type
  | base (levels : ℕ)
  | withW (levels : ℕ)

inductive Translation : Node → Node → Type
  | baseLevels {n m : ℕ} (h : n ≤ m) : Translation (.base n) (.base m)
  | wLevels {n m : ℕ} (h : n ≤ m) : Translation (.withW n) (.withW m)
  | addW (levels : ℕ) : Translation (.base levels) (.withW levels)

/-- Both finite institution towers and the checked base-to-W maps. -/
def graph : LogicGraph.{0, 0, 0, 0, 0, u + 1, u + 1} where
  Logics := Node
  inst
    | .base n => ExtensionalMLTT.Finite.bundled.{u} n
    | .withW n => W.Finite.bundled.{u} n
  Comor := Translation
  comor
    | .baseLevels h => ExtensionalMLTT.Finite.inclusion h
    | .wLevels h => W.Finite.inclusion h
    | .addW n => Embedding.finiteInclusion n
  Mor _ _ := PEmpty
  mor e := e.elim

/-- A concrete heterogeneous route that adds W at a fixed universe count. -/
def extensionPath (levels : ℕ) :
    Quiver.Path (show graph.{u}.Idx from Node.base levels)
      (show graph.{u}.Idx from Node.withW levels) :=
  .cons .nil (.addW levels)

abbrev sourceSig (levels : ℕ) : graph.{u}.Sig :=
  graph.sigOf (.base levels) (Discrete.mk ())

abbrev targetSig (levels : ℕ) : graph.{u}.Sig :=
  IndexedCoInst.mkSig graph.indexed (graph.pt (.withW levels))
    ((IndexedCoInst.coHom graph.indexed (graph.pathHom (extensionPath levels))).Φ.obj (Discrete.mk ()))

abbrev extensionLift (levels : ℕ) : sourceSig.{u} levels ⟶ targetSig.{u} levels :=
  IndexedCoInst.lift graph.indexed (graph.pathHom (extensionPath levels)) (Discrete.mk ())

end Finite

namespace Hierarchy

noncomputable section

inductive Node : Type
  | base
  | withW
  | setConstraints

inductive Translation : Node → Node → Type
  | addW : Translation .base .withW
  | realizeW : Translation .withW .setConstraints
  | realizeBase : Translation .base .setConstraints

/-- The hierarchy-level realization triangle in the Hets logic graph. -/
noncomputable def graph : LogicGraph.{0, 0, 0, 0, u + 1, u + 1, u + 1} where
  Logics := Node
  inst
    | .base => ExtensionalMLTT.Institution.bundled.{u}
    | .withW => Institution.bundled.{u}
    | .setConstraints => ExtensionalMLTT.SetTheoryInterpretation.bundled.{u}
  Comor := Translation
  comor
    | .addW => Embedding.hierarchyInclusion
    | .realizeW => SetTheoryInterpretation.toSetTheory
    | .realizeBase => ExtensionalMLTT.SetTheoryInterpretation.toSetTheory
  Mor _ _ := PEmpty
  mor e := e.elim

/-- Add W, then realize the extended judgment as an actual set constraint. -/
def realizationPath :
    Quiver.Path (show graph.{u}.Idx from Node.base)
      (show graph.{u}.Idx from Node.setConstraints) :=
  .cons (.cons .nil .addW) .realizeW

abbrev sourceSig : graph.{u}.Sig := graph.sigOf .base (Discrete.mk ())

abbrev targetSig : graph.{u}.Sig :=
  IndexedCoInst.mkSig graph.indexed (graph.pt .setConstraints)
    ((IndexedCoInst.coHom graph.indexed (graph.pathHom realizationPath)).Φ.obj (Discrete.mk ()))

abbrev realizationLift : sourceSig.{u} ⟶ targetSig.{u} :=
  IndexedCoInst.lift graph.indexed (graph.pathHom realizationPath) (Discrete.mk ())

end

end Hierarchy

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Hets

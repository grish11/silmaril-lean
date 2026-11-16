module

public import Silmaril.Logic.Egglog.Source.Named.Hets.Defs

@[expose] public section
namespace Silmaril.Logic.Egglog.Source.Named.Hets
open CategoryTheory Silmaril.Logic.Institution

/-- Every displayed source edge is its actual comparison along the indexed path. -/
theorem edge_path {source target : Node} (edge : Edge source target) :
    IndexedCoInst.coHom logicGraph.indexed ((Paths.of logicGraph.Idx).map edge) =
      logicGraph.comor edge :=
  logicGraph.coHom_toPath edge
end Silmaril.Logic.Egglog.Source.Named.Hets

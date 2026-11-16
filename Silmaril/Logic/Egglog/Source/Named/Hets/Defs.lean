module

public import Silmaril.Logic.Egglog.Source.Named.Supplied.Institution.Thms
public import Silmaril.Logic.Egglog.Source.Named.Supplied.Direct.Thms
public import Silmaril.Logic.Institution.Hets.LogicGraph

@[expose] public section
namespace Silmaril.Logic.Egglog.Source.Named.Hets
open Silmaril.Logic.Institution

inductive Node where
  | families
  | suppliedSupport
  | suppliedDirect
  | core
  | graph

inductive Edge : Node → Node → Type where
  | familiesCore : Edge .families .core
  | familiesGraph : Edge .families .graph
  | supportFamilies : Edge .suppliedSupport .families
  | supportDirect : Edge .suppliedSupport .suppliedDirect
  | supportCore : Edge .suppliedSupport .core
  | supportGraph : Edge .suppliedSupport .graph
  | directCore : Edge .suppliedDirect .core
  | directGraph : Edge .suppliedDirect .graph
  | coreGraph : Edge .core .graph

/-- Only actual natural institution comparisons are registered. The direct
supplied-to-family per-room embedding is deliberately a separate API. -/
def logicGraph : LogicGraph where
  Logics := Node
  inst
    | .families => Families.inst
    | .suppliedSupport => Supplied.inst
    | .suppliedDirect => Supplied.Direct.inst
    | .core => Core.inst
    | .graph => Core.Graph.inst
  Comor := Edge
  comor edge := match edge with
    | .familiesCore => Families.toCore
    | .familiesGraph => Families.toGraph
    | .supportFamilies => Supplied.toFamilies
    | .supportDirect => Supplied.toDirect
    | .supportCore => Supplied.toCore
    | .supportGraph => Supplied.toGraph
    | .directCore => Supplied.Direct.toCore
    | .directGraph => Supplied.Direct.toGraph
    | .coreGraph => Core.Graph.fromCore
  Mor _ _ := PEmpty
  mor edge := edge.elim
end Silmaril.Logic.Egglog.Source.Named.Hets

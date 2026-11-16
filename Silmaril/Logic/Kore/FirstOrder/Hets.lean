module

public import Silmaril.Logic.Kore.FirstOrder.Institution
public import Silmaril.Logic.Institution.Hets.LogicGraph

@[expose] public section
namespace Silmaril.Logic.Kore.FirstOrder.Hets
open Silmaril.Logic.Institution

inductive Node where
  | koreFragment
  | matchingFirstOrder

inductive Translation : Node → Node → Type where
  | lower : Translation .koreFragment .matchingFirstOrder

/-- A two-node Hets logic graph containing the checked lowering edge.
It registers no full K language, rewrite rule, or reachability logic. -/
def graph (S : Type) : LogicGraph where
  Logics := Node
  inst
    | .koreFragment => FirstOrder.inst S
    | .matchingFirstOrder => matchingInst S
  Comor := Translation
  comor
    | .lower => loweringComorphism S
  Mor _ _ := PEmpty
  mor e := e.elim

theorem lower_modelExpansive (S : Type) :
    ((graph S).comor Translation.lower).ModelExpansive := lowering_modelExpansive S
end Silmaril.Logic.Kore.FirstOrder.Hets

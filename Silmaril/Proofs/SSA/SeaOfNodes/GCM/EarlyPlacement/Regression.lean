module

import Silmaril.SSA.SeaOfNodes.GCM.EarlyPlacement.Thms
import Silmaril.SSA.SeaOfNodes.GCM.EarlyPlacement.Example.Defs

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.EarlyPlacement.Regression

open Silmaril.SSA.SeaOfNodes.GCM
open Silmaril.SSA.SeaOfNodes.GCM.EarlyPlacement
open Silmaril.SSA.SeaOfNodes.GCM.EarlyPlacement.Example
open Silmaril.SSA.SeaOfNodes.GCM.LatePlacement (lateBound?)
open Silmaril.SSA.SeaOfNodes.GCM.LatePlacement.Example

attribute [local cbv_eval] List.maxOn?_nil List.maxOn?_cons maxOn_eq_ite

-- Both parallel Phi occurrences read after the local binding in left.
example : observe = some (2, 2, false, true, false) := by cbv

-- A reachable right-arm Phi read moves the late bound above the left definition.
example : (tree?.map fun tree =>
    (earlyBound? tree.1 nestedDefs, lateBound? tree.1 blocks bothArms,
      discoverPlacement tree.1 blocks nestedDefs bothArms)) =
    some (some (block .left), some (block .fork), none) := by cbv

private def earlyRead : List (Use Label) := .ordinary ⟨block .left, 0⟩ :: parallelUses

-- Equal block bounds can still leave no cut between a definition and a read.
example : (tree?.map fun tree =>
    (earlyBound? tree.1 nestedDefs, lateBound? tree.1 blocks earlyRead,
      discoverPlacement tree.1 blocks nestedDefs earlyRead)) =
    some (some (block .left), some (block .left), none) := by cbv

private def definitionLists : List (List (Point Label)) :=
  [[], [⟨block .left, 1⟩, ⟨block .right, 0⟩], [⟨block .left, 2⟩], [⟨block .dead, 0⟩]]

-- Entry is the bound for an empty definition list. Incomparability and
-- invalid definition cuts are rejected.
example : (tree?.map fun tree => definitionLists.map (earlyBound? tree.1)) =
    some [some none, none, none, none] := by cbv

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.EarlyPlacement.Regression

module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Example.Defs

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute

open DeleteRoute.Example (layout compactReturn compactLoop)
open SCCP.Example (model program facts concrete nativeReturn)
open Dispatch.Example (looping)
open Diamond.SCCP (TupleCovers)

#guard layout (.constant ⟨false⟩) = some ([0, 1, 2, 4], some 3)
#guard layout (.constant ⟨true⟩) = some ([0, 1, 2, 3], some 3)
#guard layout .overdefined = none
#guard (rewrite model program (facts .overdefined)).isNone
#guard compactReturn false 4 = some none
#guard compactReturn false 5 = some (nativeReturn false 5)
#guard compactReturn true 5 = some (nativeReturn true 5)
#guard compactLoop 12 = some none

example (checked : Checked model looping (facts (.constant ⟨false⟩))) (fuel : Nat)
    (covered : TupleCovers (facts (.constant ⟨false⟩)) (concrete false)) :
    (compact checked).runFrom model fuel 0 (concrete false) =
      looping.source.runFrom model fuel 0 (concrete false) :=
  runFrom_eq checked covered fuel

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute

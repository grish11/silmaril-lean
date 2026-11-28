module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Example.Defs

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass

open SCCP.Example (Byte model program facts)
open Bypass.Example (originalBlocks returnPair immediateExit repeatPair loopPair repeatModel repeatProgram
  repeatEntry)

#guard originalBlocks (.constant ⟨false⟩) = some [0, 1, 4]
#guard originalBlocks (.constant ⟨true⟩) = some [0, 1, 3]
#guard (rewrite model program (facts .overdefined)).isNone
#guard returnPair false 4 = some (none, some 7)
#guard returnPair true 5 = some (some 99, some 99)
#guard immediateExit 1 = some (none, none)
#guard immediateExit 2 = some (some 7, some 7)
#guard repeatPair 5 = some (none, none)
#guard repeatPair 6 = some (none, some 3)
#guard repeatPair 7 = some (none, some 3)
#guard repeatPair 8 = some (some 3, some 3)
#guard loopPair 18 = some (none, none)

example : ReturnsAfter repeatProgram repeatModel 2 repeatEntry (3 : Byte) :=
  .feedback rfl (.feedback rfl (.exit rfl))

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass

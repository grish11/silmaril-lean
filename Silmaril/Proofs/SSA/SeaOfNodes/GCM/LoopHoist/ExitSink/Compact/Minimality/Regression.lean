module

import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Minimality.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Minimality.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Minimality.Example.Defs

open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Minimality.Example

#guard observe == some ([([4, 6, 8], true), ([0, 4, 6, 8], true), ([6, 8], false)], [6, 4])
#guard ambientOnly

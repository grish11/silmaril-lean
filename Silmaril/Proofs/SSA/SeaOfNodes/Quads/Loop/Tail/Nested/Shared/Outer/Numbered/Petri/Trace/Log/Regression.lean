module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Log.Thms
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Log.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Log.Example

/-- info: (some ([((6, 0), 15, true, 17), ((6, 0), 73, true, 75), ((7, 0), 150, false, 152)], 152), true, true, true, true) -/
#guard_msgs in
#eval (summary (flat false), summary (flat true) == summary (flat false), schedulesDiffer, truncated, malformed)

module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Log.Normalize.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Log.Normalize.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Log.Normalize.Example.Defs

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Log.Normalize.Example

open Diamond.MLIR.CF.Example (input)
open RVSDG.NestedTheta.Petri (pending)

example : List.IsChain (RootFire plan input) (pending semantics (emitted plan) :: flat) :=
  (schedule plan input 200 (pending semantics (emitted plan))).property

/--
info: (some false, some 152, false, some ([((6, 0), 15, true, 17), ((6, 0), 73, true, 75), ((7, 0), 150, false, 152)], 152),
  true, true, true)
-/
#guard_msgs in
#eval report

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Log.Normalize.Example

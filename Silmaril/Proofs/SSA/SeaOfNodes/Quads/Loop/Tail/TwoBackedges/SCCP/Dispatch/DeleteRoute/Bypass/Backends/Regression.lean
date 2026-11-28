module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Example.Defs

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends

open Bypass.MLIR.CF.Example (entry facts program looping)
open Example (computesSelector observations stoppingFacts)
open SeaOfNodes.Diamond.SCCP (TupleCovers)
open SeaOfNodes.Loop.MLIR.CF (model)

#guard observations program true false 1 = .ok (false, some 7, some 7, some 7)
#guard observations program true true 1 = .ok (true, some 99, some 99, some 99)
#guard observations program true true 0 = .ok (true, none, none, none)
#guard observations program false true 0 = .ok (true, some 7, some 7, some 7)
#guard observations looping true true 9 = .ok (true, none, none, none)
#guard (compile program (facts .overdefined)).map Targets.retained = .error .bothMarked
#guard (compile program stoppingFacts).map Targets.retained = .error .neitherMarked
#guard (compile computesSelector (facts .overdefined)).map Targets.retained = .ok false
#guard observations computesSelector true true 1 = .ok (false, some 7, some 7, some 7)

-- Both concrete route choices satisfy the contract that triggers the refusal.
example (side : Bool) : TupleCovers (facts .overdefined) (entry true side) := by
  intro s port
  cases port with
  | head => trivial
  | tail port =>
    cases port with
    | head => trivial
    | tail port =>
      cases port with
      | head => rfl
      | tail port => nomatch port

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends

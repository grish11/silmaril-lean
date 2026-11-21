module

public import Silmaril.Wasm.Game.Intrinsic.Requests.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.Intrinsic.Requests

open Silmaril.Games Execution.Core Numerics SingleThreaded

variable {source : Module} {instance_ : ScalarInstance}

/-- One guarded back-edge for a recursive request: after the selected successful
reply, a host-free run returns to exactly the same store and pending thread.
This models a single recurring request, not arbitrary recursive effect trees. -/
structure Repeat (profile_ : Profile) (request : NamedImport source instance_)
    (args : Typed request.signature.params) (reply : Typed request.signature.results)
    (store : Store Nat) (waiting : Thread) : Prop where
  callout : CalloutAt store waiting request.slot.val args.val
  decode : instance_.importOp? request.slot.val args.val = some (request.question args)
  restart : Reach profile_ (store, resumeResult store waiting (.values reply.val)) (store, waiting)

/-- A natural-number stream of answered requests, as finite stock game prefixes.
The first ask is supplied by the entry; each repetition answers and asks again. -/
def Repeat.moves (request : NamedImport source instance_) (args : Typed request.signature.params)
    (reply : Typed request.signature.results) (count : Nat) : List (Move instance_.E instance_.F) :=
  (List.replicate count [.inl (.ans (request.question args) (.values reply)),
    .inl (.ask (request.question args))]).flatten

end Silmaril.Wasm.Game.Intrinsic.Requests

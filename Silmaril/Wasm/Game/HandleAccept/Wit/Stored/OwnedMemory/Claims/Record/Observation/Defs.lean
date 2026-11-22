module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Record.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Record

open Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower (Object)

/-- The first unequal nominal observation along two dry runs. A tail demand
requires a successful head on both sides, with its disposable update. Shared
contexts contribute no spend and must be present before visiting the tail. -/
inductive ReachedPrepareConflict {E : CoreEngine} {sig : Signature} (store : CStore E) :
    State sig → State sig → List Object → Spend → Prop where
  | owner {left right receipt rest}
      (different : ¬ (Spend.owner (receiptId receipt)).ObservationAgrees left right) :
      ReachedPrepareConflict store left right (.owner receipt :: rest) (.owner (receiptId receipt))
  | endpoint {left right channel element id rest}
      (different : ¬ (Spend.endpoint id).ObservationAgrees left right) :
      ReachedPrepareConflict store left right (.shared (.endpoint channel element id) :: rest) (.endpoint id)
  | afterOwner {left right lhs rhs receipt rep rest probe}
      (agrees : (Spend.owner (receiptId receipt)).ObservationAgrees left right)
      (checked : prepareOwner left receipt = .ok (rep, lhs))
      (raw : prepareOwner right receipt = .ok (rep, rhs))
      (tail : ReachedPrepareConflict store lhs rhs rest probe) :
      ReachedPrepareConflict store left right (.owner receipt :: rest) probe
  | afterEndpoint {left right lhs rhs channel element id rest probe}
      (agrees : (Spend.endpoint id).ObservationAgrees left right)
      (checked : prepareEndpoint store left channel element id = .ok lhs)
      (raw : prepareEndpoint store right channel element id = .ok rhs)
      (tail : ReachedPrepareConflict store lhs rhs rest probe) :
      ReachedPrepareConflict store left right (.shared (.endpoint channel element id) :: rest) probe
  | afterContext {left right id rest probe} (found : (store.errCtx? id).isSome)
      (tail : ReachedPrepareConflict store left right rest probe) :
      ReachedPrepareConflict store left right (.shared (.errorContext id) :: rest) probe

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Record

module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Record.Observation.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.RecordPrepare

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Record

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints

/-- The public payload preparation neither reorders nor substitutes observed
owners, even when several of them have the same resource type and representation. -/
theorem preflightValue_receipts {E : CoreEngine} (cx : LiftLowerContext E) (type : TypeOf)
    (payload : Payload type) (output : Stored.Lower.Output) (field : RecordLower.Field)
    (objects : List RecordLower.Object) (compiled : preflightValue cx type payload output = .ok (field, objects)) :
    payload.val.owners = objects.filterMap RecordLower.Object.ownerReceipt := by
  simp only [preflightValue, bind, Except.bind, Except.mapError] at compiled
  split at compiled <;> try contradiction
  exact RecordLower.compileValue_receipts _ _ _ _ _ _ _ compiled

/-- The same preflight used by `givePayload` and `giveFlat` preserves the
canonical value; it does not turn that observation into transfer permission. -/
theorem preflightValue_value {E : CoreEngine} (cx : LiftLowerContext E) (type : TypeOf)
    (payload : Payload type) (output : Stored.Lower.Output) (field : RecordLower.Field)
    (objects : List RecordLower.Object) (compiled : preflightValue cx type payload output = .ok (field, objects)) :
    field.value = payload.val.value := by
  simp only [preflightValue, bind, Except.bind, Except.mapError] at compiled
  split at compiled <;> first | contradiction | exact RecordLower.compileValue_value _ _ _ _ _ _ _ compiled

/-- Both public payload routes obtain the recursive node shape from their
actual preflight, independently of the authority available at a later visit. -/
theorem preflightValue_emitted {E : CoreEngine} (cx : LiftLowerContext E) (type : TypeOf)
    (payload : Payload type) (output : Stored.Lower.Output) (field : RecordLower.Field)
    (objects : List RecordLower.Object) (compiled : preflightValue cx type payload output = .ok (field, objects)) :
    field.Emitted := by
  simp only [preflightValue, bind, Except.bind, Except.mapError] at compiled
  split at compiled <;> first | contradiction | exact RecordLower.compileValue_emitted _ _ _ _ _ _ _ compiled

/-- The recursive layout certificate for either public payload output. -/
theorem preflightValue_layout {E : CoreEngine} (cx : LiftLowerContext E) (type : TypeOf)
    (payload : Payload type) (output : Stored.Lower.Output) (field : RecordLower.Field)
    (objects : List RecordLower.Object) (compiled : preflightValue cx type payload output = .ok (field, objects)) :
    field.LayoutMatches type := by
  simp only [preflightValue, bind, Except.bind, Except.mapError] at compiled
  split at compiled <;> first | contradiction | exact RecordLower.compileValue_layout _ _ _ _ _ _ _ compiled

/-- Compare the reached dry run on the common live store. The prospective
spends are threaded in list order, so repeated claims still fail on both sides. -/
theorem prepare_live {E : CoreEngine} {sig : Signature} (store : CStore E)
    (plan : List RecordLower.Object) {left right : State sig} (agrees : left.LiveClaimsAgree right) :
    prepare store left plan = prepare store right plan :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.RecordPrepare.prepare_live store plan agrees

/-- A compiled plan reads only its own nominal claims. Prospective spends on
both sides preserve agreement for the remaining demands, including duplicates. -/
theorem prepare_observations {E : CoreEngine} {sig : Signature} (store : CStore E)
    (plan : List RecordLower.Object) {left right : State sig}
    (agrees : ∀ probe ∈ exclusiveSpends plan, probe.ObservationAgrees left right) :
    prepare store left plan = prepare store right plan :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.RecordPrepare.prepare_observations store plan agrees

/-- An unequal dry-run result witnesses an actually reached pending claim,
not merely a claim mentioned in an unvisited suffix of the compiled plan. -/
theorem prepare_conflict {E : CoreEngine} {sig : Signature} (store : CStore E)
    (plan : List RecordLower.Object) {left right : State sig} {pending : Spend → Prop}
    (related : left.ClaimDiscrepancies right pending)
    (unequal : prepare store left plan ≠ prepare store right plan) :
    ∃ probe, pending probe ∧ ReachedPrepareConflict store left right plan probe :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.RecordPrepare.prepare_conflict store plan related unequal

theorem owner_prepared {sig : Signature} {state next : State sig} {receipt : Receipt} {rep : Nat}
    (checked : prepareOwner state receipt = .ok (rep, next)) :
    next = (Spend.owner (receiptId receipt)).apply state ∧ (Spend.owner (receiptId receipt)).Live state :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.RecordPrepare.owner_prepared checked

theorem endpoint_prepared {E : CoreEngine} {sig : Signature} {store : CStore E}
    {state next : State sig} {channel element id} (checked : prepareEndpoint store state channel element id = .ok next) :
    next = (Spend.endpoint id).apply state ∧ (Spend.endpoint id).Live state :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.RecordPrepare.endpoint_prepared checked

/-- A successful whole-plan dry run authorizes each nominal owner or readable
endpoint at most once. Error contexts are shared and do not enter the claim list. -/
theorem prepare_distinct {E : CoreEngine} {sig : Signature} (store : CStore E)
    (state : State sig) (plan : List RecordLower.Object) (checked : prepare store state plan = .ok ()) :
    (exclusiveSpends plan).Nodup :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.RecordPrepare.prepare_distinct
    store state plan checked

theorem lower_preflight_error {E : CoreEngine} {World : Type} {sig : Signature} (access : Access E World sig)
    (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E) (type : TypeOf)
    (payload : Payload type) (output : Stored.Lower.Output) {issue : RecordLower.Issue}
    (reject : preflight cx type payload output = .error issue) :
    lower access limits quirks cx type payload output = pure (.error issue) := by
  simp only [lower, RecordLower.Internal.lowerCompiled, RecordLower.Internal.lowerWithPlan, reject]

theorem lowerValue_preflight_error {E : CoreEngine} {World : Type} {sig : Signature}
    (access : Access E World sig) (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E)
    (type : TypeOf) (payload : Payload type) (output : Stored.Lower.Output) {issue : RecordLower.Issue}
    (reject : preflightValue cx type payload output = .error issue) :
    lowerValue access limits quirks cx type payload output = pure (.error issue) := by
  simp only [lowerValue, RecordLower.Internal.lowerWithPlan, reject]

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Record

module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims

open Silmaril.Wasm.Component.Runtime

/-- Nominal identities introduced by published roots, newest first. Existing child trees are
references to earlier observations, so their receipts are not introduced again by the parent.
Representations, Core handles, and canonical guest table slots are not identities. -/
def State.publishedOwners {sig : Signature} (state : State sig) : List HandleObjId :=
  (state.accepted.flatMap rootReceipts).map receiptId

/-- Live owner claims are an ordered selection of the exact published receipts. Spending
removes receipts without rewriting the nominal type, identity, or representation. -/
def State.ClaimsBacked {sig : Signature} (state : State sig) : Prop :=
  state.held.Sublist (state.accepted.flatMap rootReceipts)

/-- Resolve the journal suffix by its recorded Core handles, in publication order.
An unchecked state can contain an entry with no corresponding root. -/
def Core.Scheduled.HostState.publicationRootsFrom {sig : Signature}
    (state : Core.Scheduled.HostState sig) (position : Nat) : List (Option (OwnedMemory.Tree sig)) :=
  (state.publications.drop position).map fun (_, handle) =>
    if handle < 2 ^ 32 then Endpoints.Core.childFromHistory state.writer.accepted (BitVec.ofNat 32 handle)
    else none

/-- The journal entry at `position`, in publication order, names the accepted root
that contains this exact receipt. Child observations do not introduce new receipts. -/
def Core.Scheduled.HostState.RecordsOwner {sig : Signature} (state : Core.Scheduled.HostState sig)
    (position ticket handle : Nat) (receipt : Receipt) : Prop :=
  state.publications[position]? = some (ticket, handle) ∧ handle < 2 ^ 32 ∧
    ∃ root, Endpoints.Core.childFromHistory state.writer.accepted (BitVec.ofNat 32 handle) = some root ∧
      receipt ∈ rootReceipts root

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims

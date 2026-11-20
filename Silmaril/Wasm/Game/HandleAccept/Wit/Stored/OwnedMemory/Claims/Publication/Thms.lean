module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Publication.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Deferred.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Publication

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Machine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Execution.Core

variable {sig : Signature} {grow : SingleThreaded.GrowOracle}

/-- Successive writer actions never publish a nominal owner twice. Spending an owner or reusing
an endpoint does not change this history. -/
theorem WriterRun.published_owners_unique {before after : State sig} (run : WriterRun before after)
    (unique : before.publishedOwners.Nodup) : after.publishedOwners.Nodup :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Publication.run_preserves run unique

/-- Every held receipt continues to come from the publication history. -/
theorem WriterRun.claims_backed {before after : State sig} (run : WriterRun before after)
    (backed : before.ClaimsBacked) : after.ClaimsBacked :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Publication.run_backed run backed

/-- A checked give or drop reads the nominal type and representation of the exact
published receipt it will spend; a matching representation alone is not evidence. -/
theorem prepare_from_published_root {state spent : State sig} {resource : RtId}
    {id : HandleObjId} {representation : Nat} (backed : state.ClaimsBacked)
    (success : state.prepare resource id = .ok (representation, spent)) :
    ∃ tree ∈ state.accepted, ∃ receipt ∈ rootReceipts tree,
      receiptId receipt = id ∧ receipt.1 = resource ∧ receipt.2.representation = representation :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Publication.prepared_from_history backed success

/-- Committing the prepared writer state retires the published identity, even though
the accepted tree and all of its observations remain available. -/
theorem prepare_retires {state spent : State sig} {resource : RtId} {id : HandleObjId} {representation : Nat}
    (backed : state.ClaimsBacked) (success : state.prepare resource id = .ok (representation, spent)) :
    spent.retiredOwner id :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Publication.prepared_retires backed success

/-- Retrying a retired owner after arbitrary checked writer actions is still a typed
refusal, even if the requested nominal type is different. -/
theorem WriterRun.retired_owner_refuses {before after : State sig} {id : HandleObjId}
    (run : WriterRun before after) (retired : before.retiredOwner id) (resource : RtId) :
    after.prepare resource id = .error .unclaimed :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Publication.retired_refuses
    (run.owner_retired retired) resource

/-- A successful preparation of a newly introduced owner identifies the journal entry and
the Core handle of its publishing root, even before the original import returns to Core. -/
theorem PublicationDelta.prepared_owner {before after : HostState sig} {spent : State sig}
    {resource : RtId} {id : HandleObjId} {representation : Nat}
    (journal : PublicationDelta before after) (run : WriterRun before.writer after.writer)
    (backed : before.writer.ClaimsBacked) (fresh : id ∉ before.writer.publishedOwners)
    (success : after.writer.prepare resource id = .ok (representation, spent)) :
    ∃ position ticket handle receipt, before.publications.length ≤ position ∧
      after.RecordsOwner position ticket handle receipt ∧
      receiptId receipt = id ∧ receipt.1 = resource ∧ receipt.2.representation = representation :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Publication.prepared_publication
    journal run backed fresh success

/-- Spending authority or publishing another root leaves the original audit entry and
its exact receipt available. Looking up the receipt does not restore the claim. -/
theorem PublicationDelta.retains_owner_record {before after : HostState sig} {position ticket handle : Nat}
    {receipt : OwnedMemory.Receipt} (journal : PublicationDelta before after)
    (run : WriterRun before.writer after.writer) (recorded : before.RecordsOwner position ticket handle receipt) :
    after.RecordsOwner position ticket handle receipt :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Publication.retained_owner_record
    journal run recorded

/-- Reading the new journal entries by their Core handles recovers every new accepted
root in order, including duplicate tree values, with no missing handle or extra root. -/
theorem PublicationDelta.publication_roots {before after : HostState sig}
    (journal : PublicationDelta before after) (run : WriterRun before.writer after.writer) :
    after.publicationRootsFrom before.publications.length =
      (after.writer.accepted.reverse.drop before.writer.accepted.length).map some :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Publication.publication_roots journal run

/-- The chronological acceptance history of every ordinary checked export prefix is
exactly its newly journaled roots. A journal entry denotes commitment, not necessarily
delivery of a result to the original Core caller. -/
theorem ComponentCall.Deferred.publication_roots (bindings : List (Binding sig))
    (callees : List (ComponentCall.Callee sig)) (deferred : List HostFuncId) (control : String)
    {prof : ProfileKind} {ready : HostReady (HostState sig)}
    (store : CStore (core3 grow)) (state : HostState sig)
    {final : Config (core3 grow) (HostState sig)} {labels : List (Label (core3 grow) (HostState sig))}
    (steps : Steps prof ready (specDispatch ready (ComponentCall.Deferred.hostWithDeferred bindings callees deferred control))
      (Config.init store state) labels final)
    (ordinary : ∀ program, Label.host (.run program) ∉ labels) :
    final.host.publicationRootsFrom state.publications.length =
      (final.host.writer.accepted.reverse.drop state.writer.accepted.length).map some := by
  obtain ⟨_, run, journal⟩ := checked_of_session bindings callees deferred control store state steps ordinary
  exact journal.publication_roots run

/-- The checked component scheduler preserves root-publication uniqueness across arbitrary
export prefixes, including rejected calls, canonical traps and deferred cancellation. -/
theorem ComponentCall.Deferred.published_owners_unique (bindings : List (Binding sig))
    (callees : List (ComponentCall.Callee sig)) (deferred : List HostFuncId) (control : String)
    {prof : ProfileKind} {ready : HostReady (HostState sig)}
    (store : CStore (core3 grow)) (state : HostState sig)
    {final : Config (core3 grow) (HostState sig)} {labels : List (Label (core3 grow) (HostState sig))}
    (steps : Steps prof ready (specDispatch ready (ComponentCall.Deferred.hostWithDeferred bindings callees deferred control))
      (Config.init store state) labels final)
    (ordinary : ∀ program, Label.host (.run program) ∉ labels)
    (unique : state.writer.publishedOwners.Nodup) : final.host.writer.publishedOwners.Nodup :=
  (ComponentCall.Deferred.checked_of_session bindings callees deferred control store state steps ordinary).2.1
    |>.published_owners_unique unique

/-- Across arbitrary checked export prefixes, every held owner is backed by a published
receipt. This includes prefixes ending at a refusal, canonical trap, or cancellation. -/
theorem ComponentCall.Deferred.claims_backed (bindings : List (Binding sig))
    (callees : List (ComponentCall.Callee sig)) (deferred : List HostFuncId) (control : String)
    {prof : ProfileKind} {ready : HostReady (HostState sig)}
    (store : CStore (core3 grow)) (state : HostState sig)
    {final : Config (core3 grow) (HostState sig)} {labels : List (Label (core3 grow) (HostState sig))}
    (steps : Steps prof ready (specDispatch ready (ComponentCall.Deferred.hostWithDeferred bindings callees deferred control))
      (Config.init store state) labels final)
    (ordinary : ∀ program, Label.host (.run program) ∉ labels)
    (backed : state.writer.ClaimsBacked) : final.host.writer.ClaimsBacked :=
  (ComponentCall.Deferred.checked_of_session bindings callees deferred control store state steps ordinary).2.1
    |>.claims_backed backed

/-- Owner preparation after any ordinary checked export prefix traces a new owner to the
specific committed publication, not to a reused canonical slot or equal representation. -/
theorem ComponentCall.Deferred.prepared_owner_publication (bindings : List (Binding sig))
    (callees : List (ComponentCall.Callee sig)) (deferred : List HostFuncId) (control : String)
    {prof : ProfileKind} {ready : HostReady (HostState sig)}
    (store : CStore (core3 grow)) (state : HostState sig)
    {final : Config (core3 grow) (HostState sig)} {labels : List (Label (core3 grow) (HostState sig))}
    (steps : Steps prof ready (specDispatch ready (ComponentCall.Deferred.hostWithDeferred bindings callees deferred control))
      (Config.init store state) labels final)
    (ordinary : ∀ program, Label.host (.run program) ∉ labels)
    {spent : State sig} {resource : RtId} {id : HandleObjId} {representation : Nat}
    (backed : state.writer.ClaimsBacked) (fresh : id ∉ state.writer.publishedOwners)
    (success : final.host.writer.prepare resource id = .ok (representation, spent)) :
    ∃ position ticket handle receipt, state.publications.length ≤ position ∧
      final.host.RecordsOwner position ticket handle receipt ∧
      receiptId receipt = id ∧ receipt.1 = resource ∧ receipt.2.representation = representation := by
  obtain ⟨_, run, journal⟩ := checked_of_session bindings callees deferred control store state steps ordinary
  exact journal.prepared_owner run backed fresh success

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled

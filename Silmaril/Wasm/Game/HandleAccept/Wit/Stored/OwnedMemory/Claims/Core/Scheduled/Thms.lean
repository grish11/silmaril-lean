module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Defs
public import Silmaril.Wasm.Component.Reference.Machine.Step.Defs
public import Silmaril.Wasm.Component.Reference.HostWrite.Defs
import Silmaril.Wasm.Component.Reference.HostWrite.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Machine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored (Signature)

variable {sig : Signature} {grow : SingleThreaded.GrowOracle}
  {prof : ProfileKind} {ready : HostReady (HostState sig)}
  {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}

/-- Record the import's typed arguments and reserve a fresh ticket before routing it. The
same ticket stays in the continuation even if a destructor later reenters this dispatcher. -/
theorem enter_steps (config : Config (core3 grow) (HostState sig))
    (thread : Option Runtime.ThreadId) (segments : List (Seg (core3 grow) (HostState sig)))
    (rest : List (Activation (core3 grow) (HostState sig))) (bindings : List (Binding sig))
    (name : String) (type : V1.FuncType) (args : List FlatValue)
    (pending : config.ctl = ⟨thread, .prog (.flat <$> dispatchImport bindings name type args), segments⟩ :: rest) :
    Steps prof ready dispatch config [.tau, .tau]
      { config with
        host := config.host.enter name type args
        ctl := ⟨thread, .prog (.flat <$> route config.host.nextTicket bindings name type args), segments⟩ :: rest } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript.enter_steps
    config thread segments rest bindings name type args pending

/-- In any activation, recording a completion returns exactly the corresponding Core status
pair without changing the writer, component store or suspended work. -/
theorem finish_steps (config : Config (core3 grow) (HostState sig))
    (thread : Option Runtime.ThreadId) (segments : List (Seg (core3 grow) (HostState sig)))
    (rest : List (Activation (core3 grow) (HostState sig)))
    (ticket : Nat) (result : Except Issue Nat)
    (pending : config.ctl = ⟨thread, .prog (.flat <$> finish ticket result), segments⟩ :: rest) :
    Steps prof ready dispatch config [.tau, .tau]
      { config with
        host := config.host.record (completion ticket result).1
        ctl := ⟨thread, .prog (.pure (.flat (completion ticket result).2)), segments⟩ :: rest } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript.finish_steps
    config thread segments rest ticket result pending

/-- A failed checked load records its diagnostic and returns the refusal status without
publishing a tree. The loader's reached store distinguishes effect-free preflight from a
later canonical failure after table effects. The suspended work is not discarded. -/
theorem accept_refusal_steps (config : Config (core3 grow) (HostState sig))
    (thread : Option Runtime.ThreadId) (segments : List (Seg (core3 grow) (HostState sig)))
    (rest : List (Activation (core3 grow) (HostState sig))) (ticket : Nat)
    (loadNode : World grow sig → CStore (core3 grow) × Except Core.Issue (OwnedMemory.Tree sig))
    (updated : CStore (core3 grow)) (issue : Core.Issue)
    (refused : loadNode ⟨config.store, config.host.writer⟩ = (updated, .error issue))
    (pending : config.ctl = ⟨thread,
      .prog (.flat <$> (do finish ticket (← acceptWith ticket loadNode))), segments⟩ :: rest) :
    Steps prof ready dispatch config [.tau, .tau, .tau, .tau, .tau]
      { config with
        store := updated
        host := config.host.record (.refused ticket (.accept issue))
        ctl := ⟨thread, .prog (.pure (.flat [i32Flat 1, i32Flat 0])), segments⟩ :: rest } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript.accept_refusal_steps
    config thread segments rest ticket loadNode updated issue refused pending

/-- The loaded tree and its registered claims become visible before the successful
Core reply. The publication and the journal use the same committed writer state. -/
theorem accept_success_steps (config : Config (core3 grow) (HostState sig))
    (thread : Option Runtime.ThreadId) (segments : List (Seg (core3 grow) (HostState sig)))
    (rest : List (Activation (core3 grow) (HostState sig))) (ticket : Nat)
    (loadNode : World grow sig → CStore (core3 grow) × Except Core.Issue (OwnedMemory.Tree sig))
    (updated : CStore (core3 grow)) (tree : OwnedMemory.Tree sig) (writer : State sig)
    (loaded : loadNode ⟨config.store, config.host.writer⟩ = (updated, .ok tree))
    (registered : config.host.writer.register tree = .ok writer)
    (fits : writer.accepted.length < 2 ^ 32)
    (pending : config.ctl = ⟨thread,
      .prog (.flat <$> (do finish ticket (← acceptWith ticket loadNode))), segments⟩ :: rest) :
    let handle := writer.accepted.length
    Steps prof ready dispatch config [.tau, .tau, .tau, .tau, .tau, .tau, .tau]
      { config with
        store := updated
        host := (({ config.host with writer } : HostState sig).record (.published ticket handle)).record
          (.returned ticket handle)
        ctl := ⟨thread, .prog (.pure (.flat [i32Flat 0, i32Flat handle])), segments⟩ :: rest } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript.accept_success_steps
    config thread segments rest ticket loadNode updated tree writer loaded registered fits pending

/-- Registration can refuse after lifting. It must not publish the root, spend another
claim, or roll back canonical effects already performed by the loader. -/
theorem accept_registration_refusal_steps (config : Config (core3 grow) (HostState sig))
    (thread : Option Runtime.ThreadId) (segments : List (Seg (core3 grow) (HostState sig)))
    (rest : List (Activation (core3 grow) (HostState sig))) (ticket : Nat)
    (loadNode : World grow sig → CStore (core3 grow) × Except Core.Issue (OwnedMemory.Tree sig))
    (updated : CStore (core3 grow)) (tree : OwnedMemory.Tree sig) (issue : Claims.Issue)
    (loaded : loadNode ⟨config.store, config.host.writer⟩ = (updated, .ok tree))
    (rejected : config.host.writer.register tree = .error issue)
    (pending : config.ctl = ⟨thread,
      .prog (.flat <$> (do finish ticket (← acceptWith ticket loadNode))), segments⟩ :: rest) :
    Steps prof ready dispatch config [.tau, .tau, .tau, .tau, .tau, .tau]
      { config with
        store := updated
        host := config.host.record (.refused ticket (.accept (.claims issue)))
        ctl := ⟨thread, .prog (.pure (.flat [i32Flat 1, i32Flat 0])), segments⟩ :: rest } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript.accept_registration_refusal_steps
    config thread segments rest ticket loadNode updated tree issue loaded rejected pending

/-- The commit guard also refuses exhaustion in a direct use of the continuation, leaving
the reached store and writer unchanged. The Core loaders check capacity before lifting. -/
theorem publish_exhausted_steps (config : Config (core3 grow) (HostState sig))
    (thread : Option Runtime.ThreadId) (segments : List (Seg (core3 grow) (HostState sig)))
    (rest : List (Activation (core3 grow) (HostState sig))) (ticket : Nat)
    (tree : OwnedMemory.Tree sig) (writer : State sig)
    (registered : config.host.writer.register tree = .ok writer) (exhausted : 2 ^ 32 ≤ writer.accepted.length)
    (pending : config.ctl = ⟨thread,
      .prog (.flat <$> (do finish ticket (← publishRoot ticket tree))), segments⟩ :: rest) :
    Steps prof ready dispatch config [.tau, .tau, .tau]
      { config with
        host := config.host.record (.refused ticket (.accept (.boundary .exhaustedHandles)))
        ctl := ⟨thread, .prog (.pure (.flat [i32Flat 1, i32Flat 0])), segments⟩ :: rest } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript.publish_exhausted_steps
    config thread segments rest ticket tree writer registered exhausted pending

/-- Journal a complete flat payload and its status, including shape-correct padding on refusal. -/
theorem finish_flat_steps (config : Config (core3 grow) (HostState sig))
    (thread : Option Runtime.ThreadId) (segments : List (Seg (core3 grow) (HostState sig)))
    (rest : List (Activation (core3 grow) (HostState sig))) (ticket : Nat) (shape : List NumType)
    (result : Except Issue (List FlatValue))
    (pending : config.ctl = ⟨thread, .prog (.flat <$> writeCompletion (flatCompletion ticket shape result)),
      segments⟩ :: rest) :
    Steps prof ready dispatch config [.tau, .tau]
      { config with
        host := config.host.record (flatCompletion ticket shape result).1
        ctl := ⟨thread, .prog (.pure (.flat (flatCompletion ticket shape result).2)), segments⟩ :: rest } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript.write_completion_steps
    config thread segments rest _ pending

theorem flatCompletion_type (ticket : Nat) (shape : List NumType) (result : Except Issue (List FlatValue)) :
    (flatCompletion ticket shape result).2.map Stored.flatType = .int .i32 :: shape :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript.flatCompletion_type
    ticket shape result

/-- A linking error records the typed diagnostic before the real reference trap, not a
status return. A destructor trap follows its own path and never calls this handler. -/
theorem binding_trap_steps (config : Config (core3 grow) (HostState sig))
    (thread : Option Runtime.ThreadId) (segments : List (Seg (core3 grow) (HostState sig)))
    (rest : List (Activation (core3 grow) (HostState sig))) (ticket : Nat) (issue : Issue)
    (pending : config.ctl = ⟨thread, .prog (.flat <$> rejectBinding ticket issue), segments⟩ :: rest) :
    Steps prof ready dispatch config [.tau, .tau, .trap (.hostTrap "invalid mixed acceptor import binding")]
      (StepDefs.trapCfg { config with host := config.host.record (.bindingTrap ticket issue) }) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript.binding_trap_steps
    config thread segments rest ticket issue pending

/-- Failure to resolve the public import binding logs the typed diagnostic and takes the
reference trap transition before any loader, writer mutation, or claim transfer. -/
theorem import_binding_trap_steps (config : Config (core3 grow) (HostState sig))
    (thread : Option Runtime.ThreadId) (segments : List (Seg (core3 grow) (HostState sig)))
    (rest : List (Activation (core3 grow) (HostState sig))) (bindings : List (Binding sig))
    (name : String) (type : V1.FuncType) (args : List FlatValue) (issue : Issue)
    (unresolved : resolveBinding bindings name type = .error issue)
    (pending : config.ctl = ⟨thread, .prog (.flat <$> dispatchImport bindings name type args), segments⟩ :: rest) :
    Steps prof ready dispatch config [.tau, .tau, .tau, .tau, .trap (.hostTrap "invalid mixed acceptor import binding")]
      (StepDefs.trapCfg { config with
        host := (config.host.enter name type args).record (.bindingTrap config.host.nextTicket issue) }) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript.import_binding_trap_steps
    config thread segments rest bindings name type args issue unresolved pending

/-- The diagnostic history is append-only even for host-injected programs whose writes
need not follow the stronger writer policy. -/
theorem extends_of_steps (bindings : List (Binding sig))
    {initial final : Config (core3 grow) (HostState sig)}
    {labels : List (Label (core3 grow) (HostState sig))}
    (steps : Steps prof ready (specDispatch ready (host bindings)) initial labels final)
    (safe : CfgSafe Extends initial) (runSafe : RunSafe Extends labels) : Extends initial.host final.host :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript.extends_of_steps
    bindings steps safe runSafe

/-- For arbitrary machine prefixes, including trapping or suspended calls, diagnostic history
only grows, every writer change follows the publication and spend policy, and each newly
accepted root contributes one publication entry. Host-supplied raw programs must respect
the same write policy. -/
theorem checked_of_steps (bindings : List (Binding sig))
    {initial final : Config (core3 grow) (HostState sig)}
    {labels : List (Label (core3 grow) (HostState sig))}
    (steps : Steps prof ready (specDispatch ready (host bindings)) initial labels final)
    (safe : CfgSafe CheckedWrite initial) (runSafe : RunSafe CheckedWrite labels) :
    Extends initial.host final.host ∧ WriterRun initial.host.writer final.host.writer ∧
      PublicationDelta initial.host final.host :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript.checked_of_steps
    bindings steps safe runSafe

/-- The reached configuration also obeys the checked writer policy, so the
same invariant can be used on a later suffix without reinitializing the machine. -/
theorem checked_cfgSafe_of_steps (bindings : List (Binding sig))
    {initial final : Config (core3 grow) (HostState sig)}
    {labels : List (Label (core3 grow) (HostState sig))}
    (steps : Steps prof ready (specDispatch ready (host bindings)) initial labels final)
    (safe : CfgSafe CheckedWrite initial) (runSafe : RunSafe CheckedWrite labels) :
    CfgSafe CheckedWrite final :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript.checked_cfgSafe_of_steps
    bindings steps safe runSafe

/-- An initialized session admits arbitrary ordinary host events and internal scheduling
without any hypothesis about the component or its export sequence. -/
theorem checked_of_session (bindings : List (Binding sig)) (store : CStore (core3 grow)) (state : HostState sig)
    {final : Config (core3 grow) (HostState sig)} {labels : List (Label (core3 grow) (HostState sig))}
    (steps : Steps prof ready (specDispatch ready (host bindings)) (Config.init store state) labels final)
    (ordinary : ∀ program, Label.host (.run program) ∉ labels) :
    Extends state final.host ∧ WriterRun state.writer final.host.writer ∧ PublicationDelta state final.host :=
  checked_of_steps bindings steps (Component.Reference.HostWrite.cfgSafe_init _ _)
    (fun program member => (ordinary program member).elim)

theorem extends_of_session (bindings : List (Binding sig)) (store : CStore (core3 grow)) (state : HostState sig)
    {final : Config (core3 grow) (HostState sig)} {labels : List (Label (core3 grow) (HostState sig))}
    (steps : Steps prof ready (specDispatch ready (host bindings)) (Config.init store state) labels final)
    (ordinary : ∀ program, Label.host (.run program) ∉ labels) : Extends state final.host :=
  (checked_of_session bindings store state steps ordinary).1

/-- Once spent, an owner that was observed in an accepted root cannot be reacquired as the
same arena identity, even if a later Core call reuses the guest slot or representation. -/
theorem WriterRun.owner_retired {before after : State sig} {id : HandleObjId}
    (run : WriterRun before after) (retired : before.retiredOwner id) : after.retiredOwner id :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript.owner_retired run retired

/-- Readable endpoint identity can be acquired again, but only through a new root
publication. Spending or a rejected call cannot restore an earlier claim. -/
theorem WriterRun.endpoint_publications {before after : State sig} (run : WriterRun before after) :
    ∃ roots, after.accepted = roots ++ before.accepted ∧
      ∀ id ∈ after.endpoints, id ∈ before.endpoints ∨ id ∈ roots.flatMap rootEndpoints :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript.endpoint_publications run

/-- Each ticket's publication handle selects its root in the final writer, even when the
session stops mid-call. The history of new roots is in reverse publication order. -/
theorem PublicationDelta.targets {before after : HostState sig}
    (journal : PublicationDelta before after) (run : WriterRun before.writer after.writer) :
    ∃ entries roots, after.publications = before.publications ++ entries ∧
      after.writer.accepted = roots ++ before.writer.accepted ∧ entries.length = roots.length ∧
      ∀ index ticket handle, entries[index]? = some (ticket, handle) →
        ∃ tree, roots[roots.length - (index + 1)]? = some tree ∧
          Endpoints.Core.childFromHistory after.writer.accepted (BitVec.ofNat 32 handle) = some tree :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript.publication_targets run journal

/-- Later publication, spending, and refusal never change an existing tree lookup.
Selecting a historical tree does not restore its spent authority. -/
theorem WriterRun.retains_target {before after : State sig} (run : WriterRun before after)
    {handle : BitVec 32} {tree : OwnedMemory.Tree sig}
    (selected : Endpoints.Core.childFromHistory before.accepted handle = some tree) :
    Endpoints.Core.childFromHistory after.accepted handle = some tree :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript.retained_target run selected

/-- A completed callout with a single publication delta identifies the newly
accepted root. An arbitrary checked suffix, including refusal, suspension or
trap, keeps the same journal index and tree lookup. Lookup does not revive a
spent resource or endpoint claim. -/
theorem single_publication_survives (bindings : List (Binding sig))
    {before published final : Config (core3 grow) (HostState sig)}
    {publishing suffix : List (Label (core3 grow) (HostState sig))}
    (first : Steps prof ready (specDispatch ready (host bindings)) before publishing published)
    (later : Steps prof ready (specDispatch ready (host bindings)) published suffix final)
    (safe : CfgSafe CheckedWrite before)
    (firstSafe : RunSafe CheckedWrite publishing) (laterSafe : RunSafe CheckedWrite suffix)
    {ticket handle : Nat}
    (recorded : published.host.publications = before.host.publications ++ [(ticket, handle)]) :
    ∃ tree, published.host.writer.accepted = tree :: before.host.writer.accepted ∧
      final.host.publications[before.host.publications.length]? = some (ticket, handle) ∧
      Endpoints.Core.childFromHistory published.host.writer.accepted (BitVec.ofNat 32 handle) = some tree ∧
      Endpoints.Core.childFromHistory final.host.writer.accepted (BitVec.ofNat 32 handle) = some tree :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript.single_publication_survives
    bindings first later safe firstSafe laterSafe recorded

/-- A fresh Core handle resolves exactly when its journal position records a
publication. This is a statement about tree lookup, not live transfer authority. -/
theorem PublicationDelta.fresh_lookup_iff {before after : HostState sig}
    (journal : PublicationDelta before after) {handle : BitVec 32}
    (fresh : before.writer.accepted.length < handle.toNat) :
    (Endpoints.Core.childFromHistory after.writer.accepted handle).isSome = true ↔
      ∃ ticket, after.publications[before.publications.length +
        (handle.toNat - (before.writer.accepted.length + 1))]? = some (ticket, handle.toNat) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript.publication_lookup_iff
    journal fresh

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled

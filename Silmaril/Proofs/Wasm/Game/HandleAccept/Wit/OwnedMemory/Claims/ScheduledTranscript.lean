module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Defs
public import Silmaril.Wasm.Component.Reference.Machine.Step.Defs
public import Silmaril.Wasm.Component.Reference.HostWrite.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Deferred.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Publication.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Thms
import Silmaril.Wasm.Component.Reference.HostWrite.Thms
import Silmaril.Wasm.Component.Reference.Canon.Builtins.Resource.Thms
import Silmaril.Wasm.Component.Reference.Canon.Lift.Thms
import Silmaril.Wasm.Component.Reference.Canon.Lower.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.RecordEffects

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Machine
  Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored (Signature)
open Silmaril.Wasm.Game.HandleAccept.Wit
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims (State)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open Silmaril.Wasm.Game.HandleAccept.Wit.Async (Channel Element Channel.endKind Endpoint)

variable {sig : Signature} {grow : SingleThreaded.GrowOracle}
  {prof : ProfileKind} {ready : HostReady (HostState sig)}
  {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}

theorem enter_steps (config : Config (core3 grow) (HostState sig))
    (thread : Option Runtime.ThreadId) (segments : List (Seg (core3 grow) (HostState sig)))
    (rest : List (Activation (core3 grow) (HostState sig))) (bindings : List (Binding sig))
    (name : String) (type : V1.FuncType) (args : List FlatValue)
    (pending : config.ctl = ⟨thread, .prog (.flat <$> dispatchImport bindings name type args), segments⟩ :: rest) :
    Steps prof ready dispatch config [.tau, .tau]
      { config with
        host := config.host.enter name type args
        ctl := ⟨thread, .prog (.flat <$> route config.host.nextTicket bindings name type args), segments⟩ :: rest } :=
  .cons (.hostGet pending) (.cons (.hostSet rfl) (.refl _))

theorem write_completion_steps (config : Config (core3 grow) (HostState sig))
    (thread : Option Runtime.ThreadId) (segments : List (Seg (core3 grow) (HostState sig)))
    (rest : List (Activation (core3 grow) (HostState sig))) (reply : Event × List FlatValue)
    (pending : config.ctl = ⟨thread, .prog (.flat <$> writeCompletion reply), segments⟩ :: rest) :
    Steps prof ready dispatch config [.tau, .tau]
      { config with
        host := config.host.record reply.1
        ctl := ⟨thread, .prog (.pure (.flat reply.2)), segments⟩ :: rest } :=
  .cons (.hostGet pending) (.cons (.hostSet rfl) (.refl _))

theorem finish_steps (config : Config (core3 grow) (HostState sig))
    (thread : Option Runtime.ThreadId) (segments : List (Seg (core3 grow) (HostState sig)))
    (rest : List (Activation (core3 grow) (HostState sig)))
    (ticket : Nat) (result : Except Issue Nat)
    (pending : config.ctl = ⟨thread, .prog (.flat <$> finish ticket result), segments⟩ :: rest) :
    Steps prof ready dispatch config [.tau, .tau]
      { config with
        host := config.host.record (completion ticket result).1
        ctl := ⟨thread, .prog (.pure (.flat (completion ticket result).2)), segments⟩ :: rest } :=
  write_completion_steps config thread segments rest _ pending

private theorem steps_append {first middle last : Config (core3 grow) (HostState sig)}
    {earlier later : List (Label (core3 grow) (HostState sig))}
    (started : Steps prof ready dispatch first earlier middle) (continued : Steps prof ready dispatch middle later last) :
    Steps prof ready dispatch first (earlier ++ later) last := by
  induction started with
  | refl => exact continued
  | cons step _ ih => exact .cons step (ih continued)

private theorem accept_load_steps (config : Config (core3 grow) (HostState sig))
    (thread : Option Runtime.ThreadId) (segments : List (Seg (core3 grow) (HostState sig)))
    (rest : List (Activation (core3 grow) (HostState sig))) (ticket : Nat)
    (loadNode : Stored.OwnedMemory.Claims.Core.World grow sig →
      CStore (core3 grow) × Except Stored.OwnedMemory.Claims.Core.Issue (Stored.OwnedMemory.Tree sig))
    (updated : CStore (core3 grow))
    (loaded : Except Stored.OwnedMemory.Claims.Core.Issue (Stored.OwnedMemory.Tree sig))
    (outcome : loadNode ⟨config.store, config.host.writer⟩ = (updated, loaded))
    (pending : config.ctl = ⟨thread,
      .prog (.flat <$> (do finish ticket (← acceptWith ticket loadNode))), segments⟩ :: rest) :
    Steps prof ready dispatch config [.tau, .tau, .tau]
      { config with
        store := updated
        ctl := ⟨thread, .prog (.flat <$> ((match loaded with
          | .error issue => pure (.error (.accept issue))
          | .ok tree => publishRoot ticket tree) >>= finish ticket)), segments⟩ :: rest } := by
  refine .cons (.hostGet pending) (.cons (.get rfl) ?_)
  change Steps prof ready dispatch
    { config with ctl := ⟨thread, .prog (.flat <$> ((do
        let outcome := loadNode ⟨config.store, config.host.writer⟩
        modifyStore fun _ => outcome.1
        match outcome.2 with
        | .error reason => pure (.error (.accept reason))
        | .ok tree => publishRoot ticket tree) >>= finish ticket)), segments⟩ :: rest } _ _
  rw [outcome]
  exact .cons (.modify rfl) (.refl _)

theorem accept_refusal_steps (config : Config (core3 grow) (HostState sig))
    (thread : Option Runtime.ThreadId) (segments : List (Seg (core3 grow) (HostState sig)))
    (rest : List (Activation (core3 grow) (HostState sig))) (ticket : Nat)
    (loadNode : Stored.OwnedMemory.Claims.Core.World grow sig →
      CStore (core3 grow) × Except Stored.OwnedMemory.Claims.Core.Issue (Stored.OwnedMemory.Tree sig))
    (updated : CStore (core3 grow)) (issue : Stored.OwnedMemory.Claims.Core.Issue)
    (refused : loadNode ⟨config.store, config.host.writer⟩ = (updated, .error issue))
    (pending : config.ctl = ⟨thread,
      .prog (.flat <$> (do finish ticket (← acceptWith ticket loadNode))), segments⟩ :: rest) :
    Steps prof ready dispatch config [.tau, .tau, .tau, .tau, .tau]
      { config with
        store := updated
        host := config.host.record (.refused ticket (.accept issue))
        ctl := ⟨thread, .prog (.pure (.flat [i32Flat 1, i32Flat 0])), segments⟩ :: rest } :=
  steps_append (accept_load_steps config thread segments rest ticket loadNode updated (.error issue) refused pending)
    (finish_steps _ thread segments rest ticket (.error (.accept issue)) rfl)

theorem accept_success_steps (config : Config (core3 grow) (HostState sig))
    (thread : Option Runtime.ThreadId) (segments : List (Seg (core3 grow) (HostState sig)))
    (rest : List (Activation (core3 grow) (HostState sig))) (ticket : Nat)
    (loadNode : Stored.OwnedMemory.Claims.Core.World grow sig →
      CStore (core3 grow) × Except Stored.OwnedMemory.Claims.Core.Issue (Stored.OwnedMemory.Tree sig))
    (updated : CStore (core3 grow)) (tree : Stored.OwnedMemory.Tree sig) (writer : State sig)
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
        ctl := ⟨thread, .prog (.pure (.flat [i32Flat 0, i32Flat handle])), segments⟩ :: rest } := by
  dsimp only
  refine steps_append (accept_load_steps config thread segments rest ticket loadNode updated (.ok tree) loaded pending) ?_
  refine .cons (.hostGet rfl) ?_
  change Steps prof ready dispatch
    { config with store := updated, ctl := ⟨thread, .prog (.flat <$> ((match config.host.writer.register tree with
      | .error issue => pure (.error (.accept (.claims issue)))
      | .ok writer => do
        if writer.accepted.length ≥ 2 ^ 32 then return .error (.accept (.boundary .exhaustedHandles))
        hostSet (({ config.host with writer } : HostState sig).record
          (.published ticket writer.accepted.length))
        return .ok writer.accepted.length) >>= finish ticket)), segments⟩ :: rest } _ _
  rw [registered]
  simp only [ite_eq_right (Nat.not_le.mpr fits)]
  exact .cons (.hostSet rfl) (finish_steps _ thread segments rest ticket (.ok _) rfl)

theorem accept_registration_refusal_steps (config : Config (core3 grow) (HostState sig))
    (thread : Option Runtime.ThreadId) (segments : List (Seg (core3 grow) (HostState sig)))
    (rest : List (Activation (core3 grow) (HostState sig))) (ticket : Nat)
    (loadNode : Stored.OwnedMemory.Claims.Core.World grow sig →
      CStore (core3 grow) × Except Stored.OwnedMemory.Claims.Core.Issue (Stored.OwnedMemory.Tree sig))
    (updated : CStore (core3 grow)) (tree : Stored.OwnedMemory.Tree sig)
    (issue : Stored.OwnedMemory.Claims.Issue)
    (loaded : loadNode ⟨config.store, config.host.writer⟩ = (updated, .ok tree))
    (rejected : config.host.writer.register tree = .error issue)
    (pending : config.ctl = ⟨thread,
      .prog (.flat <$> (do finish ticket (← acceptWith ticket loadNode))), segments⟩ :: rest) :
    Steps prof ready dispatch config [.tau, .tau, .tau, .tau, .tau, .tau]
      { config with
        store := updated
        host := config.host.record (.refused ticket (.accept (.claims issue)))
        ctl := ⟨thread, .prog (.pure (.flat [i32Flat 1, i32Flat 0])), segments⟩ :: rest } := by
  refine steps_append (accept_load_steps config thread segments rest ticket loadNode updated (.ok tree) loaded pending) ?_
  refine .cons (.hostGet rfl) ?_
  change Steps prof ready dispatch
    { config with store := updated, ctl := ⟨thread, .prog (.flat <$> ((match config.host.writer.register tree with
      | .error issue => pure (.error (.accept (.claims issue)))
      | .ok writer => do
        if writer.accepted.length ≥ 2 ^ 32 then return .error (.accept (.boundary .exhaustedHandles))
        hostSet (({ config.host with writer } : HostState sig).record
          (.published ticket writer.accepted.length))
        return .ok writer.accepted.length) >>= finish ticket)), segments⟩ :: rest } _ _
  rw [rejected]
  exact finish_steps _ thread segments rest ticket (.error (.accept (.claims issue))) rfl

theorem publish_exhausted_steps (config : Config (core3 grow) (HostState sig))
    (thread : Option Runtime.ThreadId) (segments : List (Seg (core3 grow) (HostState sig)))
    (rest : List (Activation (core3 grow) (HostState sig))) (ticket : Nat)
    (tree : Stored.OwnedMemory.Tree sig) (writer : State sig)
    (registered : config.host.writer.register tree = .ok writer) (exhausted : 2 ^ 32 ≤ writer.accepted.length)
    (pending : config.ctl = ⟨thread,
      .prog (.flat <$> (do finish ticket (← publishRoot ticket tree))), segments⟩ :: rest) :
    Steps prof ready dispatch config [.tau, .tau, .tau]
      { config with
        host := config.host.record (.refused ticket (.accept (.boundary .exhaustedHandles)))
        ctl := ⟨thread, .prog (.pure (.flat [i32Flat 1, i32Flat 0])), segments⟩ :: rest } := by
  refine .cons (.hostGet pending) ?_
  change Steps prof ready dispatch
    { config with ctl := ⟨thread, .prog (.flat <$> ((match config.host.writer.register tree with
      | .error issue => pure (.error (.accept (.claims issue)))
      | .ok writer => do
        if writer.accepted.length ≥ 2 ^ 32 then return .error (.accept (.boundary .exhaustedHandles))
        hostSet (({ config.host with writer } : HostState sig).record (.published ticket writer.accepted.length))
        return .ok writer.accepted.length) >>= finish ticket)), segments⟩ :: rest } _ _
  rw [registered]
  simp only [ite_eq_left exhausted]
  exact finish_steps _ thread segments rest ticket (.error (.accept (.boundary .exhaustedHandles))) rfl

theorem flatCompletion_type (ticket : Nat) (shape : List NumType) (result : Except Issue (List FlatValue)) :
    (flatCompletion ticket shape result).2.map Stored.flatType = .int .i32 :: shape := by
  have zeroTypes : (shape.map zeroWord).map Stored.flatType = shape := by
    induction shape with
    | nil => rfl
    | cons head tail ih =>
      change Stored.flatType (zeroWord head) :: (tail.map zeroWord).map Stored.flatType = head :: tail
      rw [ih]
      cases head with
      | int kind => cases kind <;> rfl
      | float kind => cases kind <;> rfl
  cases result with
  | error issue => exact congrArg (.int .i32 :: ·) zeroTypes
  | ok values =>
    by_cases typed : values.map Stored.flatType = shape
    · simp only [flatCompletion, ite_eq_left typed]
      exact congrArg (.int .i32 :: ·) typed
    · simp only [flatCompletion, ite_eq_right typed]
      exact congrArg (.int .i32 :: ·) zeroTypes

theorem binding_trap_steps (config : Config (core3 grow) (HostState sig))
    (thread : Option Runtime.ThreadId) (segments : List (Seg (core3 grow) (HostState sig)))
    (rest : List (Activation (core3 grow) (HostState sig))) (ticket : Nat) (issue : Issue)
    (pending : config.ctl = ⟨thread, .prog (.flat <$> rejectBinding ticket issue), segments⟩ :: rest) :
    Steps prof ready dispatch config [.tau, .tau, .trap (.hostTrap "invalid mixed acceptor import binding")]
      (StepDefs.trapCfg { config with host := config.host.record (.bindingTrap ticket issue) }) := by
  exact .cons (.hostGet pending) (.cons (.hostSet rfl) (.cons (.trap rfl) (.refl _)))

theorem import_binding_trap_steps (config : Config (core3 grow) (HostState sig))
    (thread : Option Runtime.ThreadId) (segments : List (Seg (core3 grow) (HostState sig)))
    (rest : List (Activation (core3 grow) (HostState sig))) (bindings : List (Binding sig))
    (name : String) (type : V1.FuncType) (args : List FlatValue) (issue : Issue)
    (unresolved : resolveBinding bindings name type = .error issue)
    (pending : config.ctl = ⟨thread, .prog (.flat <$> dispatchImport bindings name type args), segments⟩ :: rest) :
    Steps prof ready dispatch config [.tau, .tau, .tau, .tau, .trap (.hostTrap "invalid mixed acceptor import binding")]
      (StepDefs.trapCfg { config with
        host := (config.host.enter name type args).record (.bindingTrap config.host.nextTicket issue) }) := by
  have entered := enter_steps (prof := prof) (ready := ready) (dispatch := dispatch)
    config thread segments rest bindings name type args pending
  simp only [route, unresolved] at entered
  exact steps_append entered (binding_trap_steps _ thread segments rest config.host.nextTicket issue rfl)

private abbrev Safe {Value : Type} (program : Session grow sig Value) := HostSafe CheckedWrite none program

private theorem readOnly {Value : Type} {program : Session grow sig Value}
    (safe : P.InvW (fun _ => True) (fun _ => False) program) : Safe program :=
  HostWrite.hostSafe_of_invW safe _

private theorem publication_refl (state : HostState sig) : PublicationDelta state state :=
  ⟨[], by simp, by simp, by simp⟩

private theorem publication_trans {first middle last : HostState sig}
    (earlier : PublicationDelta first middle) (later : PublicationDelta middle last) :
    PublicationDelta first last := by
  obtain ⟨earlierEntries, middleEntries, middleCount, earlierHandle⟩ := earlier
  obtain ⟨suffix, lastEntries, lastCount, laterHandle⟩ := later
  refine ⟨earlierEntries ++ suffix, by simp [lastEntries, middleEntries, List.append_assoc],
    by simp [lastCount, middleCount, Nat.add_assoc], ?_⟩
  intro index ticket handle entry
  by_cases inEarlier : index < earlierEntries.length
  · rw [List.getElem?_append_left inEarlier] at entry
    exact earlierHandle index ticket handle entry
  · rw [List.getElem?_append_right (Nat.le_of_not_gt inEarlier)] at entry
    have position : middle.writer.accepted.length + (index - earlierEntries.length) + 1 =
        first.writer.accepted.length + index + 1 := by omega
    simpa only [position] using laterHandle (index - earlierEntries.length) ticket handle entry

private theorem record_safe (state : HostState sig) (event : Event) (notPublication : event.publication = none) :
    CheckedWrite state (state.record event) :=
  ⟨⟨by simp [HostState.transcript, HostState.record], le_rfl⟩, .same _,
    ⟨[], by simp [HostState.publications, HostState.transcript, HostState.record, notPublication],
      by simp [HostState.record], by simp⟩⟩

private theorem spend_safe (update : Stored.OwnedMemory.Claims.Spend) :
    Safe ((claims (grow := grow) (sig := sig)).spend update) :=
  .get none fun state => .set ⟨⟨List.prefix_rfl, le_rfl⟩, .spend _ _,
    by cases update <;> exact publication_refl state⟩ (.pure none ())

private theorem read_safe : Safe ((claims (grow := grow) (sig := sig)).read) :=
  .get none fun state => .pure _ state.writer

private theorem publish_at_safe (ticket : Nat) (tree : Stored.OwnedMemory.Tree sig) (expected : Option Nat) :
    Safe (publishRootAt (grow := grow) ticket tree expected) := by
  refine .get none fun current => ?_
  change HostSafe CheckedWrite (some current) ((match current.writer.register tree with
    | .error issue => pure (.error (.accept (.claims issue)))
    | .ok writer => do
      let handle := writer.accepted.length
      if expected.any (· != handle) then return .error .wrongResultType
      if handle ≥ 2 ^ 32 then return .error (.accept (.boundary .exhaustedHandles))
      hostSet (({ current with writer } : HostState sig).record (.published ticket handle))
      return .ok handle) : Session grow sig (Except Issue Nat))
  split <;> rename_i writer registered
  · exact .pure (some current) _
  · dsimp only
    split
    · exact .pure (some current) _
    split
    · exact .pure (some current) _
    · rename_i exhausted
      refine .set ⟨⟨by simp [HostState.transcript, HostState.record], le_rfl⟩, .publish _ registered, ?_⟩
        (.pure none _)
      have accepted := (Stored.OwnedMemory.Claims.register_claims registered).1
      refine ⟨[(ticket, writer.accepted.length)],
        by simp [HostState.publications, HostState.transcript, HostState.record, Event.publication],
        by simp [HostState.record, accepted], ?_⟩
      intro index eventTicket handle entry
      cases index with
      | zero =>
        have equal : handle = writer.accepted.length := congrArg Prod.snd (Option.some.inj entry).symm
        exact ⟨by simp [equal, accepted], equal ▸ Nat.lt_of_not_ge exhausted⟩
      | succ index => simp at entry

private theorem publish_safe (ticket : Nat) (tree : Stored.OwnedMemory.Tree sig) :
    Safe (publishRoot (grow := grow) ticket tree) :=
  publish_at_safe _ _ _

private theorem accept_with_safe (ticket : Nat)
    (loadNode : Stored.OwnedMemory.Claims.Core.World grow sig →
      CStore (core3 grow) × Except Stored.OwnedMemory.Claims.Core.Issue (Stored.OwnedMemory.Tree sig)) :
    Safe (acceptWith ticket loadNode) := by
  unfold acceptWith
  refine HostWrite.bind (readOnly P.Inv.hostGet) fun state => ?_
  refine HostWrite.bind (readOnly P.Inv.getStore) fun reference => ?_
  refine HostWrite.bind (readOnly (P.Inv.modifyStore (fun _ _ => trivial))) fun _ => ?_
  split
  · exact .pure none _
  · exact publish_safe _ _

private theorem commitOwner_safe (cx : LiftLowerContext (core3 grow)) (resource : RtId)
    (id : HandleObjId) (representation : Nat) :
    Safe (Stored.OwnedMemory.Claims.commitOwner ((claims (sig := sig)).spend (.owner id))
      Limits.spec cx resource representation) := by
  unfold Stored.OwnedMemory.Claims.commitOwner
  exact HostWrite.bind (spend_safe (.owner id)) fun _ =>
    readOnly (P.Inv.lowerOwn (fun _ _ _ => trivial) (fun _ _ _ _ => trivial) _ _ _ _)

private theorem give_safe (cx : LiftLowerContext (core3 grow)) (resource : RtId) (id : HandleObjId) :
    Safe ((claims (sig := sig)).give Limits.spec cx resource id) := by
  unfold Stored.OwnedMemory.Claims.Access.give
  refine HostWrite.bind read_safe fun state => ?_
  split
  · exact .pure none _
  · exact HostWrite.bind (commitOwner_safe cx resource id _) fun _ => .pure none _

private theorem giveEndpoint_safe (cx : LiftLowerContext (core3 grow)) (channel : Channel) (element : Element)
    (endpoint : Endpoint (channel.endKind .read) element) :
    Safe ((claims (sig := sig)).giveEndpoint Limits.spec cx channel element endpoint) := by
  unfold Stored.OwnedMemory.Claims.Access.giveEndpoint
  refine HostWrite.bind read_safe fun _ => ?_
  split
  · exact .pure none _
  · refine HostWrite.bind (readOnly P.Inv.getStore) fun _ => ?_
    split
    · exact .pure none _
    · refine HostWrite.bind (spend_safe _) fun _ => ?_
      refine HostWrite.bind (readOnly (P.Inv.lowerAsyncValue (fun _ _ _ _ => trivial)
        (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial) _ _ _ _)) fun _ => .pure none _

private theorem drop_safe (resource : RtId) (id : HandleObjId) :
    Safe ((claims (grow := grow) (sig := sig)).drop (destructorCall Limits.spec Quirks.none) resource id) := by
  unfold Stored.OwnedMemory.Claims.Access.drop
  refine HostWrite.bind read_safe fun _ => ?_
  split
  · exact .pure none _
  · refine HostWrite.bind (readOnly Builtins.Inv.resourceEnter) fun inst => ?_
    refine HostWrite.bind (readOnly (P.Inv.dropHandleTail (by intros; trivial) _ _)) fun request => ?_
    cases request with
    | none => exact readOnly (P.Inv.internal _)
    | some request =>
      refine HostWrite.bind (spend_safe _) fun _ => ?_
      have hyps : LiftHyps (E := core3 grow) (fun _ => True) := by
        repeat' (first | (intro) | constructor)
      exact HostWrite.bind (readOnly (P.Inv.destructorCall hyps _ _ inst request)) fun _ => .pure none _

private theorem record_prepare_safe (cx : LiftLowerContext (core3 grow)) (plan : List Stored.Endpoints.RecordLower.Object) :
    Safe ((Stored.OwnedMemory.Claims.Record.authority (recordClaims (sig := sig)) Limits.spec cx).prepare plan) :=
  HostWrite.bind (readOnly P.Inv.getStore) fun _ => HostWrite.bind read_safe fun _ => .pure none _

private theorem record_transfer_safe (cx : LiftLowerContext (core3 grow)) (index : Nat)
    (object : Stored.Endpoints.RecordLower.Object) :
    Safe ((Stored.OwnedMemory.Claims.Record.authority (recordClaims (sig := sig)) Limits.spec cx).transfer index object) := by
  refine HostWrite.bind read_safe fun state => ?_
  cases object with
  | owner receipt =>
    dsimp only
    split
    · exact .pure none _
    · exact HostWrite.bind (commitOwner_safe cx receipt.1 (Stored.OwnedMemory.Claims.receiptId receipt) _)
        fun _ => .pure none _
  | shared object =>
    cases object with
    | endpoint channel element id =>
      refine HostWrite.bind (readOnly P.Inv.getStore) fun _ => ?_
      split
      · exact .pure none _
      · refine HostWrite.bind (spend_safe _) fun _ => ?_
        exact HostWrite.bind (readOnly (P.Inv.lowerAsyncValue (fun _ _ _ _ => trivial)
          (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial) _ _ _ _)) fun _ => .pure none _
    | errorContext id =>
      refine HostWrite.bind (readOnly P.Inv.getStore) fun _ => ?_
      split
      · exact .pure none _
      · exact HostWrite.bind (readOnly (P.Inv.lowerErrorContext (fun _ _ _ _ => trivial) _ _ _)) fun _ => .pure none _

private theorem lower_root_safe (cx : LiftLowerContext (core3 grow)) (tree : Stored.OwnedMemory.Tree sig)
    (output : Stored.Lower.Output) :
    Safe (Stored.OwnedMemory.Claims.Record.lowerRoot recordClaims Limits.spec Quirks.none cx tree output) := by
  cases tree with
  | atom impossible => exact impossible.elim
  | tag label children arity =>
    exact RecordEffects.compiled_safe _ _ _ _ _ _ _ _ (record_prepare_safe cx) (record_transfer_safe cx)

private theorem lower_payload_safe (cx : LiftLowerContext (core3 grow)) (tree : Stored.OwnedMemory.Tree sig)
    (output : Stored.Lower.Output) :
    Safe (Stored.OwnedMemory.Claims.Record.lowerPayloadRoot recordClaims Limits.spec Quirks.none cx tree output) := by
  cases tree with
  | atom impossible => exact impossible.elim
  | tag label children arity =>
    exact RecordEffects.compiled_value_safe _ _ _ _ _ _ _ _ (record_prepare_safe cx) (record_transfer_safe cx)

private theorem give_memory_safe (inst : InstId) (destination : RecordDestination) (args : List FlatValue)
    (lower : LiftLowerContext (core3 grow) → Stored.OwnedMemory.Tree sig → Nat →
      Session grow sig (Except Stored.Endpoints.RecordLower.Issue Unit))
    (diagnose : Stored.Endpoints.RecordLower.Issue → Issue)
    (safe : ∀ cx tree ptr, Safe (lower cx tree ptr)) :
    Safe (giveToMemory inst destination args lower diagnose) := by
  unfold giveToMemory
  split
  · split
    · exact .pure none _
    · refine HostWrite.bind (readOnly P.Inv.getStore) fun _ => ?_
      split
      · exact .pure none _
      · refine HostWrite.bind (.get none fun _ => .pure _ _) fun selected => ?_
        cases selected with
        | none => exact .pure none _
        | some tree => exact HostWrite.bind (safe _ tree _) fun _ => .pure none _
  · exact .pure none _

private theorem withTree_safe (args : List FlatValue)
    (use : Stored.OwnedMemory.Tree sig → Nat → Session grow sig (Except Issue Nat))
    (safe : ∀ tree index, Safe (use tree index)) : Safe (withTree args use) := by
  unfold withTree
  split
  · refine HostWrite.bind (.get none fun _ => .pure _ _) fun selected => ?_
    cases selected with
    | none => exact .pure none _
    | some tree => exact safe tree _
  · exact .pure none _

private theorem give_flat_safe (inst : InstId) (destination : RecordDestination) (payload : Stored.TypeOf)
    (args : List FlatValue) : Safe (giveFlat (grow := grow) (sig := sig) inst destination payload args) := by
  unfold giveFlat
  refine HostWrite.bind (readOnly P.Inv.currentInst?) fun current => ?_
  refine HostWrite.bind (readOnly P.Inv.getStore) fun store => ?_
  dsimp only
  split
  · exact .pure none _
  · split
    · refine HostWrite.bind (readOnly P.Inv.getStore) fun store => ?_
      split
      · exact .pure none _
      · refine HostWrite.bind (.get none fun _ => .pure _ _) fun selected => ?_
        cases selected with
        | none => exact .pure none _
        | some tree =>
          change Safe (if (!rootHasSchema tree payload) = true then pure (Except.error Issue.wrongPayloadType) else _)
          split
          · exact .pure none _
          · exact HostWrite.bind (lower_payload_safe _ tree .flat) fun _ => .pure none _
    · exact .pure none _

private theorem invoke_safe (ticket : Nat) (binding : Binding sig) (args : List FlatValue) :
    Safe (Stored.OwnedMemory.Claims.Core.Scheduled.invoke (grow := grow) ticket binding args) := by
  unfold Stored.OwnedMemory.Claims.Core.Scheduled.invoke
  refine HostWrite.bind (readOnly P.Inv.currentInst?) fun current => ?_
  refine HostWrite.bind (readOnly P.Inv.getStore) fun store => ?_
  dsimp only
  split
  · exact .pure none _
  · cases binding.action <;> dsimp only
    case accept =>
      split
      · exact .pure none _
      · exact accept_with_safe _ _
    case acceptFlat =>
      split
      · exact .pure none _
      · exact accept_with_safe _ _
    case giveOwner =>
      apply withTree_safe
      intro tree position
      split
      · exact HostWrite.bind (give_safe _ _ _) fun _ => .pure none _
      · exact .pure none _
    case dropOwner =>
      apply withTree_safe
      intro tree position
      split
      · exact HostWrite.bind (drop_safe _ _) fun _ => .pure none _
      · exact .pure none _
    case giveEndpoint =>
      apply withTree_safe
      intro tree position
      split
      · exact HostWrite.bind (giveEndpoint_safe _ _ _ _) fun _ => .pure none _
      · exact .pure none _
    case giveRecord => exact give_memory_safe _ _ _ _ _ fun cx tree ptr => lower_root_safe cx tree (.memory ptr)
    case givePayload => exact give_memory_safe _ _ _ _ _ fun cx tree ptr => lower_payload_safe cx tree (.memory ptr)
    case giveFlat => exact .pure none _

private theorem write_completion_safe (reply : Event × List FlatValue) (notPublication : reply.1.publication = none) :
    Safe (writeCompletion (grow := grow) (sig := sig) reply) :=
  .get none fun state => .set (record_safe state _ notPublication) (.pure none _)

private theorem finish_safe (ticket : Nat) (result : Except Issue Nat) :
    Safe (finish (grow := grow) (sig := sig) ticket result) :=
  write_completion_safe _ (by cases result <;> rfl)

private theorem flat_completion_safe (ticket : Nat) (shape : List NumType)
    (result : Except Issue (List FlatValue)) : Safe (writeCompletion (grow := grow) (sig := sig)
      (flatCompletion ticket shape result)) := by
  apply write_completion_safe
  unfold flatCompletion
  split
  · rfl
  · split <;> rfl

private theorem binding_trap_safe (ticket : Nat) (issue : Issue) :
    Safe (rejectBinding (grow := grow) (sig := sig) ticket issue) :=
  .get none fun state => .set (record_safe state _ rfl) (readOnly (P.Inv.trap _))

private theorem route_safe (ticket : Nat) (bindings : List (Binding sig)) (name : String)
    (type : V1.FuncType) (args : List FlatValue) : Safe (route (grow := grow) ticket bindings name type args) := by
  unfold route
  split
  · exact binding_trap_safe _ _
  · split
    · exact HostWrite.bind (give_flat_safe _ _ _ _) (flat_completion_safe _ _)
    · exact HostWrite.bind (invoke_safe _ _ _) (finish_safe _)

private theorem host_safe (bindings : List (Binding sig)) :
    HostImplSafe CheckedWrite (host (grow := grow) bindings) := by
  constructor
  · intro name caller; exact readOnly (P.Inv.internal _)
  · intro name type args
    refine .get none fun state => .set ?_ (route_safe _ _ _ _ _)
    exact ⟨⟨by simp [HostState.enter, HostState.transcript], Nat.le_succ _⟩, .same _,
      ⟨[], by simp [HostState.publications, HostState.enter, HostState.transcript, Event.publication],
        by simp [HostState.enter], by simp⟩⟩
  · intro name thread; exact readOnly (P.Inv.internal _)
  · intro buffer; exact readOnly (P.Inv.internal _)
  · intro cancel; exact .pure none ()

private theorem forget_writer {Result : Type} {pending : Option (HostState sig)}
    {program : Session grow sig Result} (safe : HostSafe CheckedWrite pending program) :
    HostSafe Extends pending program := by
  induction safe with
  | pure pending value => exact .pure pending value
  | op pending plain _ next => exact .op pending plain next
  | get pending _ next => exact .get pending next
  | set relation _ next => exact .set relation.1 next

theorem extends_of_steps (bindings : List (Binding sig))
    {initial final : Config (core3 grow) (HostState sig)}
    {labels : List (Label (core3 grow) (HostState sig))}
    (steps : Steps prof ready (specDispatch ready (host bindings)) initial labels final)
    (safe : CfgSafe Extends initial) (runSafe : RunSafe Extends labels) : Extends initial.host final.host := by
  have checked := host_safe (grow := grow) bindings
  have hostExt : HostImplSafe Extends (host (grow := grow) bindings) :=
    ⟨fun _ _ => forget_writer (checked.funcs _ _), fun _ _ _ => forget_writer (checked.embedder _ _ _),
      fun _ _ => forget_writer (checked.threadBody _ _), fun _ => forget_writer (checked.buffer _),
      fun _ => forget_writer (checked.cancel _)⟩
  have dispatchExt := HostWrite.hostSafe_dispatch hostExt Limits.spec Quirks.none ready
  induction steps with
  | refl => exact ⟨List.prefix_rfl, le_rfl⟩
  | cons first _ ih =>
    have nextSafe := HostWrite.step_cfgSafe dispatchExt first safe
      (fun program equal => runSafe program (by simp [equal]))
    have tail := ih nextSafe (fun program member => runSafe program (List.mem_cons_of_mem _ member))
    rcases HostWrite.step_host first safe with same | extended
    · rwa [same] at tail
    · exact ⟨extended.1.trans tail.1, le_trans extended.2 tail.2⟩

private theorem checked_host_of_steps {implementation : HostImpl (core3 grow) (HostState sig)}
    (hostSafe : HostImplSafe CheckedWrite implementation)
    {initial final : Config (core3 grow) (HostState sig)}
    {labels : List (Label (core3 grow) (HostState sig))}
    (steps : Steps prof ready (specDispatch ready implementation) initial labels final)
    (safe : CfgSafe CheckedWrite initial) (runSafe : RunSafe CheckedWrite labels) :
    Extends initial.host final.host ∧ WriterRun initial.host.writer final.host.writer ∧
      PublicationDelta initial.host final.host := by
  have checked := HostWrite.hostSafe_dispatch hostSafe Limits.spec Quirks.none ready
  induction steps with
  | refl => exact ⟨⟨List.prefix_rfl, le_rfl⟩, .refl _, publication_refl _⟩
  | cons first _ ih =>
    have nextSafe := HostWrite.step_cfgSafe checked first safe (fun program equal => runSafe program (by simp [equal]))
    have tail := ih nextSafe (fun program member => runSafe program (List.mem_cons_of_mem _ member))
    rcases HostWrite.step_host first safe with same | extended
    · rwa [same] at tail
    · exact ⟨⟨extended.1.1.trans tail.1.1, le_trans extended.1.2 tail.1.2⟩, .cons extended.2.1 tail.2.1,
        publication_trans extended.2.2 tail.2.2⟩

theorem checked_cfgSafe_of_steps (bindings : List (Binding sig))
    {initial final : Config (core3 grow) (HostState sig)}
    {labels : List (Label (core3 grow) (HostState sig))}
    (steps : Steps prof ready (specDispatch ready (host bindings)) initial labels final)
    (safe : CfgSafe CheckedWrite initial) (runSafe : RunSafe CheckedWrite labels) :
    CfgSafe CheckedWrite final :=
  HostWrite.steps_cfgSafe (HostWrite.hostSafe_dispatch (host_safe bindings) Limits.spec Quirks.none ready)
    steps safe runSafe

theorem checked_of_steps (bindings : List (Binding sig))
    {initial final : Config (core3 grow) (HostState sig)}
    {labels : List (Label (core3 grow) (HostState sig))}
    (steps : Steps prof ready (specDispatch ready (host bindings)) initial labels final)
    (safe : CfgSafe CheckedWrite initial) (runSafe : RunSafe CheckedWrite labels) :
    Extends initial.host final.host ∧ WriterRun initial.host.writer final.host.writer ∧
      PublicationDelta initial.host final.host :=
  checked_host_of_steps (host_safe bindings) steps safe runSafe

private theorem safe_of_map {Source Target : Type} {pending : Option (HostState sig)}
    {program : Session grow sig Source} {project : Source → Target}
    (safe : HostSafe CheckedWrite pending (project <$> program)) :
    HostSafe CheckedWrite pending program := by
  rw [map_eq_pure_bind] at safe
  induction program generalizing pending with
  | pure value => exact .pure pending value
  | op effect next ih =>
    change HostSafe CheckedWrite pending (.op effect (fun reply => next reply >>= fun value => pure (project value))) at safe
    cases safe with
    | op _ plain tail => exact .op _ plain fun reply => ih reply (by simpa only [map_eq_pure_bind] using tail reply)
    | get _ tail => exact .get _ fun state => ih state (by simpa only [map_eq_pure_bind] using tail state)
    | set allowed tail => exact .set allowed (ih () (by simpa only [map_eq_pure_bind] using tail))

namespace Component

open ComponentCall
open Stored.OwnedMemory (Observed observeLowerOnStart projectLowerOnStart)

private theorem lowerPres : P.Inv.LowerPres (fun _ : CStore (core3 grow) => True) := by
  constructor <;> first | (intros; exact True.intro) | (constructor <;> (repeat intro) <;> exact True.intro)

private theorem resolve_safe (caller : CallerId) (values : List Value.Val) :
    Safe (lowerOnResolve (E := core3 grow) (σ := HostState sig) Limits.spec Quirks.none caller (some values)) :=
  readOnly (P.Inv.lowerOnResolve lowerPres _ _ _ _)

private theorem observe_safe (caller : CallerId) : Safe (observeLowerOnStart
    (E := core3 grow) (World := HostState sig) Limits.spec Quirks.none caller) := by
  apply safe_of_map (project := List.map Observed.value)
  rw [projectLowerOnStart]
  exact readOnly (P.Inv.lowerOnStart lowerPres _ _ _)

private theorem reject_safe (ticket : Nat) (issue : Issue) :
    Safe (ComponentCall.reject (grow := grow) (sig := sig) ticket issue) :=
  HostWrite.bind (binding_trap_safe _ _) fun _ => .pure none _

private theorem progress_frame (subtask : SubtaskId) (before : CStore (core3 grow))
    {allow : HostState sig → Prop} :
    P.InvW (SameAuthority before) allow (maybeOnProgress subtask) := by
  unfold maybeOnProgress
  refine P.Inv.bind (P.Inv.getObj _ _) fun _ => ?_
  split
  · exact P.Inv.modifyStore (fun _ same => same)
  · exact P.Inv.pure _

theorem skip_arguments_frame (caller : CallerId) (before : CStore (core3 grow))
    {allow : HostState sig → Prop} :
    P.InvW (SameAuthority before) allow
      (skipArguments (grow := grow) (sig := sig) caller) := by
  unfold skipArguments Stored.OwnedMemory.lowerOnStartWith
  refine P.Inv.bind (P.Inv.getObj _ _) fun record => ?_
  cases record
  case lower subtask _ _ _ _ _ _ =>
    exact P.Inv.bind (progress_frame subtask before) fun _ => P.Inv.bind (P.Inv.modifyStore (fun _ same => same)) fun _ =>
      P.Inv.bind (P.Inv.pure _) fun _ => P.Inv.bind (P.Inv.modifyStore (fun _ same => same)) fun _ =>
        P.Inv.pure _
  all_goals exact P.Inv.internal _

private theorem write_frame (before : CStore (core3 grow)) (memory ptr : Nat) (bytes : ByteArray)
    (after : CStore (core3 grow)) (same : SameAuthority before after) :
    SameAuthority before (writeMemSt memory ptr bytes after) := by
  unfold writeMemSt
  split <;> exact same

private theorem error_result_store_frame (before : CStore (core3 grow))
    (cx : LiftLowerContext (core3 grow)) (ptr : Nat) {allow : HostState sig → Prop} :
    P.InvW (SameAuthority before) allow
      (store Limits.spec Quirks.none cx (.record [.variant 1 none]) (.tuple [resultType]) ptr) := by
  simp only [store, storeTuple, resultType, storeOpt]
  refine P.Inv.bind (P.Inv.ptrType _) fun _ => P.Inv.bind ?_ fun _ => P.Inv.pure _
  refine P.Inv.bind (P.Inv.ptrType _) fun _ => ?_
  exact P.Inv.bind (P.Inv.storeVariantHead _ _ _ _ _ (write_frame before)) fun _ => P.Inv.pure _

theorem lower_refusal_frame (before : CStore (core3 grow)) (cx : LiftLowerContext (core3 grow))
    (cursor : FlatCursor) (maxResults : Nat) (indirect : maxResults ≤ 1) {allow : HostState sig → Prop} :
    P.InvW (SameAuthority before) allow
      (lowerFlatValues Limits.spec Quirks.none cx maxResults [.variant 1 none] [resultType] (some cursor)) := by
  unfold lowerFlatValues
  refine P.Inv.bind (P.Inv.ptrType _) fun width => ?_
  have widthCount : (ABI.flattenTypes width [resultType]).length = 2 := by
    simp [resultType, ABI.flattenTypes, ABI.flatten, ABI.flattenOption, ABI.flattenPrimitive]
  simp only [widthCount, show maxResults < 2 by omega, ite_true]
  refine P.Inv.bind ?_ fun (ptr, _) => P.Inv.bind (P.Inv.trapIf _ _) fun _ =>
    P.Inv.bind (P.Inv.checkInBounds _ _ _) fun _ =>
    P.Inv.bind (error_result_store_frame before cx ptr) fun _ => P.Inv.pure _
  exact P.Inv.bind (P.Inv.next cursor _) fun _ => P.Inv.pure _

private theorem error_safety (ticket : Nat) (caller : CallerId) :
    Safe (resolveError (grow := grow) (sig := sig) ticket caller) := by
  unfold resolveError
  refine HostWrite.bind (readOnly (P.Inv.getObj _ _)) fun _ => ?_
  split
  · split
    · exact reject_safe _ _
    · split
      · exact reject_safe _ _
      · rename_i indirect
        exact HostWrite.bind (HostWrite.hostSafe_of_invW (progress_frame _ CStore.empty) none) fun _ =>
          HostWrite.bind (HostWrite.hostSafe_of_invW (lower_refusal_frame CStore.empty _ _ _ (by omega)) none)
            fun _ => HostWrite.bind (readOnly (P.Inv.modifyStore (fun _ _ => trivial))) fun _ => .pure none _
  · exact reject_safe _ _

private theorem refused_safe (ticket : Nat) (caller : CallerId) (issue : Issue) :
    Safe (resolveRefused (grow := grow) (sig := sig) ticket caller issue) :=
  .get none fun state => .set (record_safe state _ rfl) (error_safety _ _)

private theorem reject_frame (ticket : Nat) (issue : Issue) (before : CStore (core3 grow)) :
    P.InvW (SameAuthority before) (fun _ => True) (reject (grow := grow) (sig := sig) ticket issue) := by
  unfold reject rejectBinding
  refine P.Inv.bind (P.Inv.bind P.Inv.hostGet fun _ =>
    P.Inv.bind (P.Inv.hostSet _ trivial) fun _ => P.Inv.trap _) fun _ => P.Inv.pure _

theorem refusal_frame (ticket : Nat) (caller : CallerId) (issue : Issue) (before : CStore (core3 grow)) :
    P.InvW (SameAuthority before) (fun _ => True) (refuseBeforeLift (grow := grow) (sig := sig) ticket caller issue) := by
  unfold refuseBeforeLift resolveRefused
  refine P.Inv.bind (skip_arguments_frame _ _) fun _ => P.Inv.bind P.Inv.hostGet fun _ =>
    P.Inv.bind (P.Inv.hostSet _ trivial) fun _ => ?_
  unfold resolveError
  refine P.Inv.bind (P.Inv.getObj _ _) fun _ => ?_
  split
  · split
    · exact reject_frame _ _ _
    · split
      · exact reject_frame _ _ _
      · rename_i indirect
        exact P.Inv.bind (progress_frame _ before) fun _ =>
          P.Inv.bind (lower_refusal_frame before _ _ _ (by omega)) fun _ =>
            P.Inv.bind (P.Inv.modifyStore (fun _ same => same)) fun _ => P.Inv.pure _
  · exact reject_frame _ _ _

theorem resolve_error_agrees (ticket : Nat) (caller : CallerId) (snapshot : CStore (core3 grow))
    (subtask : SubtaskId) (cx : LiftLowerContext (core3 grow)) (args : List FlatValue) (pos : Nat)
    (ft : WIT.FuncType Empty RtId) (limits results : Nat)
    (record : ArenaField.callers.get? snapshot caller = some (.lower subtask cx args pos ft limits results))
    (type : ft.result = some resultType) (mode : results ≤ 1) :
    ∃ checked reference : CStore (core3 grow) → Session grow sig (Ret (core3 grow)),
      resolveError ticket caller = .op (S := Eff (core3 grow) (HostState sig)) .get checked ∧
      (do
        lowerOnResolve Limits.spec Quirks.none caller (some [.variant 1 none])
        pure (Ret.cancel (E := core3 grow) .none)) = .op (S := Eff (core3 grow) (HostState sig)) .get reference ∧
      checked snapshot = reference snapshot := by
  refine ⟨_, _, rfl, rfl, ?_⟩
  simp [Prog.bind, record, type, show ¬ results > 1 by omega, Quirks.none, Prog.bind_assoc]

private theorem before_lift_safe (ticket : Nat) (caller : CallerId) (issue : Issue) :
    Safe (refuseBeforeLift (grow := grow) (sig := sig) ticket caller issue) :=
  HostWrite.bind (HostWrite.hostSafe_of_invW (skip_arguments_frame caller CStore.empty) none)
    (fun _ => refused_safe _ _ _)

private theorem tree_safe (ticket : Nat) (caller : CallerId) (tree : Stored.OwnedMemory.Tree sig) :
    Safe (resolveTree (grow := grow) ticket caller tree) := by
  unfold resolveTree completeResolvedTree
  apply HostWrite.bind (readOnly P.Inv.hostGet)
  intro state
  split
  · dsimp only
    split
    · exact reject_safe _ _
    · refine HostWrite.bind (resolve_safe _ _) fun _ => HostWrite.bind (publish_at_safe _ _ _) fun result => ?_
      cases result
      · exact reject_safe _ _
      · exact HostWrite.bind (write_completion_safe _ rfl) fun _ => .pure none _
  · exact refused_safe _ _ _

private theorem accept_caller_safe (callee : Callee sig) (caller : CallerId) (ticket : Nat)
    (history : List (Stored.OwnedMemory.Tree sig)) (store : CStore (core3 grow))
    (cx : LiftLowerContext (core3 grow)) (args : List FlatValue) :
    Safe (acceptCaller callee caller ticket history store cx args) := by
  unfold acceptCaller
  split
  · exact before_lift_safe _ _ _
  split
  · exact before_lift_safe _ _ _
  split
  · exact before_lift_safe _ _ _
  · refine HostWrite.bind (observe_safe _) fun _ => ?_
    split
    · split
      · split
        · exact refused_safe _ _ _
        · exact tree_safe _ _ _
      · exact reject_safe _ _
    · exact reject_safe _ _

private theorem invoke_lower_safe (callee : Callee sig) (caller : CallerId) (state : HostState sig)
    (subtask : SubtaskId) (cx : LiftLowerContext (core3 grow)) (args : List FlatValue) (pos : Nat)
    (ft : WIT.FuncType Empty RtId) (limits results : Nat) :
    Safe (invokeLower callee caller state subtask cx args pos ft limits results) := by
  unfold invokeLower
  refine HostWrite.bind (readOnly P.Inv.getStore) fun store => HostWrite.bind (readOnly P.Inv.currentInst?) fun _ => ?_
  split
  · exact reject_safe _ _
  split
  · exact reject_safe _ _
  · exact accept_caller_safe _ _ _ _ _ _ _

private theorem enter_safe (state : HostState sig) (name : String) (type : V1.FuncType) (args : List FlatValue) :
    CheckedWrite state (state.enter name type args) :=
  ⟨⟨by simp [HostState.enter, HostState.transcript], Nat.le_succ _⟩, .same _,
    ⟨[], by simp [HostState.publications, HostState.enter, HostState.transcript, Event.publication],
      by simp [HostState.enter], by simp⟩⟩

private theorem invoke_safe (callee : Callee sig) (caller : CallerId) :
    Safe (ComponentCall.invoke (grow := grow) callee caller) := by
  unfold ComponentCall.invoke
  refine HostWrite.bind (readOnly (P.Inv.getObj _ _)) fun record => .get none fun state => ?_
  cases record <;> refine .set (enter_safe _ _ _ _) ?_
  case lower => exact invoke_lower_safe _ _ _ _ _ _ _ _ _ _
  all_goals exact reject_safe _ _

theorem hostWithComponent_safe (bindings : List (Binding sig)) (callees : List (Callee sig)) :
    HostImplSafe CheckedWrite (hostWithComponent (grow := grow) bindings callees) := by
  refine { host_safe bindings with funcs := ?_ }
  intro id caller
  change Safe ((hostWithComponent bindings callees).funcs id caller)
  unfold hostWithComponent
  simp only
  split
  · exact invoke_safe _ _
  · exact .get none fun state => .set (enter_safe _ _ _ _) (reject_safe _ _)

theorem checked_of_component_steps (bindings : List (Binding sig)) (callees : List (Callee sig))
    {initial final : Config (core3 grow) (HostState sig)}
    {labels : List (Label (core3 grow) (HostState sig))}
    (steps : Steps prof ready (specDispatch ready (hostWithComponent bindings callees)) initial labels final)
    (safe : CfgSafe CheckedWrite initial) (runSafe : RunSafe CheckedWrite labels) :
    Extends initial.host final.host ∧ WriterRun initial.host.writer final.host.writer ∧
      PublicationDelta initial.host final.host :=
  checked_host_of_steps (hostWithComponent_safe bindings callees) steps safe runSafe

namespace Deferred

open ComponentCall.Deferred

private theorem rebase {Result : Type} {program : Session grow sig Result} {pending : Option (HostState sig)}
    (safe : Safe program) : HostSafe CheckedWrite pending program := by
  cases safe with
  | pure _ value => exact .pure pending value
  | op _ plain tail => exact .op pending plain tail
  | get _ tail => exact .get pending tail

private theorem queue_safe (state : HostState sig) (entry : PendingAccept) :
    CheckedWrite state (ComponentCall.Deferred.HostState.queue state entry) :=
  record_safe state (.queued entry.ticket) rfl

private theorem take_safe (state : HostState sig) (entry : PendingAccept) :
    CheckedWrite state (ComponentCall.Deferred.HostState.take state entry) :=
  ⟨⟨List.prefix_rfl, le_rfl⟩, .same _, publication_refl _⟩

private theorem table_full_steps (config : Config (core3 grow) (HostState sig))
    (thread : Option Runtime.ThreadId) (segments : List (Seg (core3 grow) (HostState sig)))
    (rest : List (Activation (core3 grow) (HostState sig))) (ticket : Nat)
    (pending : config.ctl = ⟨thread, .prog (refuseTableFull ticket), segments⟩ :: rest) :
    Steps prof ready dispatch config [.tau, .tau]
      { config with
        host := config.host.record (.refused ticket .subtaskTableFull)
        ctl := ⟨thread, .prog (.pure (.cancel .none)), segments⟩ :: rest } :=
  .cons (.hostGet pending) (.cons (.hostSet rfl) (.refl _))

theorem reference_table_full_steps (config : Config (core3 grow) (HostState sig))
    (thread : Option Runtime.ThreadId) (segments : List (Seg (core3 grow) (HostState sig)))
    (rest : List (Activation (core3 grow) (HostState sig))) (inst : InstId) (subtask : SubtaskId)
    (instance_ : InstState) (live : config.store.inst? inst = some instance_)
    (full : instance_.addHandle? (.waitable (.subtask subtask)) = none)
    (next : Nat → Session grow sig (Ret (core3 grow)))
    (pending : config.ctl = ⟨thread, .prog (handlesAddSubtask inst subtask >>= next), segments⟩ :: rest) :
    Steps prof ready dispatch config [.tau, .trap .tableFull] (StepDefs.trapCfg config) := by
  refine .cons (.get pending) ?_
  have liveAt : ArenaField.insts.get? config.store inst = some instance_ := live
  simp only [Prog.pure_eq, Prog.bind, liveAt, full]
  exact .cons (.trap rfl) (.refl _)

theorem stage_table_full_steps (config : Config (core3 grow) (HostState sig))
    (thread : Runtime.ThreadId) (segments : List (Seg (core3 grow) (HostState sig)))
    (rest : List (Activation (core3 grow) (HostState sig))) (callee : Callee sig)
    (caller : CallerId) (ticket : Nat) (subtask : SubtaskId) (cx : LiftLowerContext (core3 grow))
    (args : List FlatValue) (pos : Nat) (ft : WIT.FuncType Empty RtId) (limits results : Nat)
    (threadInfo : Runtime.Thread) (task : Task (core3 grow)) (instance_ : InstState)
    (onThread : config.store.thread? thread = some threadInfo)
    (onTask : config.store.task? threadInfo.task = some task) (current : task.inst = callee.inst)
    (live : config.store.inst? callee.inst = some instance_)
    (async : callee.async_ = true)
    (checked : callee.check config.store subtask cx args pos ft (limits, results) = .ok ())
    (schema : Stored.OwnedMemory.checkSchema (sig.payload callee.tag) = .ok ())
    (full : instance_.addHandle? (.waitable (.subtask subtask)) = none)
    (pending : config.ctl = ⟨some thread,
      .prog (stage callee caller ticket subtask cx args pos ft limits results), segments⟩ :: rest) :
    Steps prof ready dispatch config [.tau, .tau, .tau, .tau, .tau, .tau]
      { config with
        host := config.host.record (.refused ticket .subtaskTableFull)
        ctl := ⟨some thread, .prog (.pure (.cancel .none)), segments⟩ :: rest } := by
  simp only [stage, async, Bool.not_true, Bool.false_eq_true, ite_false] at pending
  refine .cons (.get pending) (.cons (.currentThread rfl) (.cons (.get rfl) ?_))
  have onThreadAt : ArenaField.threads.get? config.store thread = some threadInfo := onThread
  simp only [Prog.pure_eq, Prog.bind, onThreadAt]
  refine .cons (.get rfl) ?_
  have onTaskAt : ArenaField.tasks.get? config.store threadInfo.task = some task := onTask
  simp only [Prog.pure_eq, Prog.bind, onTaskAt, current, bne_self_eq_false, Bool.false_eq_true,
    ite_false, checked, live, schema, full, Option.isNone_none, ite_true]
  exact table_full_steps _ _ segments rest ticket rfl

private theorem stage_safe (callee : Callee sig) (caller : CallerId) (ticket : Nat) (subtask : SubtaskId)
    (cx : LiftLowerContext (core3 grow)) (args : List FlatValue) (pos : Nat)
    (ft : WIT.FuncType Empty RtId) (limits results : Nat) :
    Safe (stage callee caller ticket subtask cx args pos ft limits results) := by
  unfold stage
  split
  · exact reject_safe _ _
  refine HostWrite.bind (readOnly P.Inv.getStore) fun _ => HostWrite.bind (readOnly P.Inv.currentInst?) fun _ => ?_
  split
  · exact reject_safe _ _
  split
  · exact reject_safe _ _
  split
  · split
    · exact before_lift_safe _ _ _
    split
    · exact .get none fun current => .set (record_safe current _ rfl) (.pure none _)
    refine .get none fun current => ?_
    dsimp only [Prog.bind]
    split
    · exact rebase (reject_safe _ _)
    · exact .set (queue_safe _ _) (.pure none _)
  · exact reject_safe _ _

theorem stage_frame (callee : Callee sig) (caller : CallerId) (ticket : Nat) (subtask : SubtaskId)
    (cx : LiftLowerContext (core3 grow)) (args : List FlatValue) (pos : Nat)
    (ft : WIT.FuncType Empty RtId) (limits results : Nat) (before : CStore (core3 grow)) :
    P.InvW (SameAuthority before) (fun _ => True) (stage callee caller ticket subtask cx args pos ft limits results) := by
  unfold stage
  split
  · exact reject_frame _ _ _
  refine P.Inv.bind P.Inv.getStore fun _ => P.Inv.bind P.Inv.currentInst? fun _ => ?_
  split
  · exact reject_frame _ _ _
  split
  · exact reject_frame _ _ _
  split
  · split
    · exact refusal_frame _ _ _ _
    split
    · exact P.Inv.bind P.Inv.hostGet fun current =>
        P.Inv.bind (P.Inv.hostSet (current.record (.refused ticket .subtaskTableFull)) trivial) fun _ => P.Inv.pure _
    refine P.Inv.bind P.Inv.hostGet fun _ => ?_
    split
    · exact reject_frame _ _ _
    · exact P.Inv.bind (P.Inv.hostSet _ trivial) fun _ => P.Inv.pure _
  · exact reject_frame _ _ _

private theorem begin_safe (callee : Callee sig) (caller : CallerId) :
    Safe (begin (grow := grow) callee caller) := by
  unfold begin
  refine HostWrite.bind (readOnly (P.Inv.getObj _ _)) fun record => .get none fun state => ?_
  cases record <;> refine .set (enter_safe _ _ _ _) ?_
  case lower => exact stage_safe _ _ _ _ _ _ _ _ _ _
  all_goals exact reject_safe _ _

private theorem start_safe (callees : List (Callee sig)) (ticket index : Nat) :
    Safe (start (grow := grow) callees ticket index) := by
  unfold start
  refine HostWrite.bind (readOnly P.Inv.getStore) fun _ =>
    HostWrite.bind (readOnly P.Inv.currentInst?) fun _ => .get none fun state => ?_
  dsimp only [Prog.bind]
  split
  · exact rebase (binding_trap_safe _ _)
  · split
    · exact rebase (binding_trap_safe _ _)
    · exact .set (take_safe _ _)
        (HostWrite.bind (next := fun _ => writeCompletion (.returned ticket 0, [i32Flat 0]))
          (accept_caller_safe _ _ _ _ _ _ _) (fun _ => write_completion_safe _ rfl))

private theorem cancel_safe (token : Nat) : Safe (ComponentCall.Deferred.cancel (grow := grow) (sig := sig) token) := by
  unfold ComponentCall.Deferred.cancel
  have failure : Safe (rejectCancellation (grow := grow) (sig := sig)) := by
    unfold rejectCancellation
    refine .get none fun state => .set (enter_safe state _ _ _) ?_
    exact HostWrite.bind (next := fun _ => pure ())
      (binding_trap_safe state.nextTicket .stalePendingAccept) (fun _ => .pure none ())
  refine HostWrite.bind (readOnly P.Inv.getStore) fun _ =>
    HostWrite.bind (readOnly P.Inv.currentInst?) fun _ => .get none fun state => ?_
  dsimp only [Prog.bind]
  split
  · exact rebase failure
  · exact rebase (HostWrite.bind (readOnly (P.Inv.lowerOnResolve lowerPres _ _ _ _)) fun _ =>
      .get none fun current => .set (record_safe current _ rfl) (.pure none ()))

private theorem lower_cancel_frame (caller : CallerId) (before : CStore (core3 grow)) :
    P.InvW (SameAuthority before) (fun _ : HostState sig => True)
      (lowerOnResolve Limits.spec Quirks.none caller none) := by
  unfold lowerOnResolve
  refine P.Inv.bind (P.Inv.getObj _ _) fun _ => ?_
  split
  · refine P.Inv.bind (progress_frame _ before) fun _ => P.Inv.bind (P.Inv.pure _) fun _ => ?_
    refine P.Inv.bind (P.Inv.getObj _ _) fun _ => ?_
    split <;> exact P.Inv.modifyStore (fun _ same => same)
  · exact P.Inv.internal _

theorem cancel_frame (token : Nat) (before : CStore (core3 grow)) :
    P.InvW (SameAuthority before) (fun _ => True) (ComponentCall.Deferred.cancel (grow := grow) (sig := sig) token) := by
  unfold ComponentCall.Deferred.cancel
  refine P.Inv.bind P.Inv.getStore fun _ => P.Inv.bind P.Inv.currentInst? fun _ =>
    P.Inv.bind P.Inv.hostGet fun _ => ?_
  split
  · unfold rejectCancellation rejectBinding
    exact P.Inv.bind P.Inv.hostGet fun _ => P.Inv.bind (P.Inv.hostSet _ trivial) fun _ =>
      P.Inv.bind (P.Inv.bind P.Inv.hostGet fun _ => P.Inv.bind (P.Inv.hostSet _ trivial) fun _ => P.Inv.trap _) fun _ =>
        P.Inv.pure _
  · exact P.Inv.bind (lower_cancel_frame _ _) fun _ => P.Inv.bind P.Inv.hostGet fun _ => P.Inv.hostSet _ trivial

private theorem dispatch_start_safe (bindings : List (Binding sig)) (callees : List (Callee sig))
    (control name : String) (type : V1.FuncType) (args : List FlatValue) :
    Safe (dispatchStart (grow := grow) bindings callees control name type args) := by
  unfold dispatchStart
  split
  · exact (host_safe bindings).embedder _ _ _
  · refine .get none fun state => .set (enter_safe _ _ _ _) ?_
    split
    · exact binding_trap_safe _ _
    split
    · exact binding_trap_safe _ _
    split
    · exact start_safe _ _ _
    · exact binding_trap_safe _ _

theorem host_safe (bindings : List (Binding sig)) (callees : List (Callee sig))
    (deferred : List HostFuncId) (control : String) :
    HostImplSafe CheckedWrite (hostWithDeferred (grow := grow) bindings callees deferred control) := by
  have eager := hostWithComponent_safe (grow := grow) bindings callees
  unfold hostWithDeferred
  dsimp only
  split
  · exact eager
  refine { eager with funcs := ?_, embedder := dispatch_start_safe _ _ _, cancel := cancel_safe }
  intro id caller
  dsimp only
  split
  · split
    · exact begin_safe _ _
    · exact eager.funcs _ _
  · exact eager.funcs _ _

theorem checked_of_steps (bindings : List (Binding sig)) (callees : List (Callee sig))
    (deferred : List HostFuncId) (control : String)
    {initial final : Config (core3 grow) (HostState sig)}
    {labels : List (Label (core3 grow) (HostState sig))}
    (steps : Steps prof ready (specDispatch ready (hostWithDeferred bindings callees deferred control))
      initial labels final) (safe : CfgSafe CheckedWrite initial) (runSafe : RunSafe CheckedWrite labels) :
    Extends initial.host final.host ∧ WriterRun initial.host.writer final.host.writer ∧
      PublicationDelta initial.host final.host :=
  checked_host_of_steps (host_safe bindings callees deferred control) steps safe runSafe

end Deferred

end Component

theorem owner_retired {before after : Stored.OwnedMemory.Claims.State sig} {id : HandleObjId}
    (run : WriterRun before after) (retired : before.retiredOwner id) : after.retiredOwner id := by
  induction run with
  | refl => exact retired
  | cons step _ ih =>
    apply ih
    cases step with
    | same => exact retired
    | publish _ registered => exact Stored.OwnedMemory.Claims.register_retains_retirement registered retired
    | spend update =>
      cases update with
      | endpoint => exact retired
      | owner =>
        refine ⟨retired.1, fun member => retired.2 ?_⟩
        obtain ⟨receipt, contained, equal⟩ := List.mem_map.mp member
        exact List.mem_map.mpr ⟨receipt, (List.mem_filter.mp contained).1, equal⟩

theorem endpoint_publications {before after : Stored.OwnedMemory.Claims.State sig}
    (run : WriterRun before after) :
    ∃ roots, after.accepted = roots ++ before.accepted ∧
      ∀ id ∈ after.endpoints, id ∈ before.endpoints ∨
        id ∈ roots.flatMap Stored.OwnedMemory.Claims.rootEndpoints := by
  induction run with
  | refl => exact ⟨[], rfl, fun _ member => .inl member⟩
  | cons step _ ih =>
    obtain ⟨roots, accepted, support⟩ := ih
    cases step with
    | same => exact ⟨roots, accepted, support⟩
    | publish tree registered =>
      have published := Stored.OwnedMemory.Claims.register_claims registered
      refine ⟨roots ++ [tree], by simp [accepted, published.1, List.append_assoc], ?_⟩
      intro id member
      rcases support id member with prior | newer
      · rw [published.2.2] at prior
        rcases List.mem_append.mp prior with atRoot | old
        · exact .inr (by simp [List.flatMap_append, atRoot])
        · exact .inl old
      · exact .inr (by simp [List.flatMap_append, newer])
    | spend update =>
      refine ⟨roots, ?_, ?_⟩
      · rw [accepted]; cases update <;> rfl
      · intro id member
        rcases support id member with earlier | published
        · apply Or.inl
          cases update with
          | owner => exact earlier
          | endpoint => exact (List.mem_filter.mp earlier).1
        · exact .inr published

theorem publication_targets {before after : HostState sig}
    (run : WriterRun before.writer after.writer) (journal : PublicationDelta before after) :
    ∃ entries roots, after.publications = before.publications ++ entries ∧
      after.writer.accepted = roots ++ before.writer.accepted ∧ entries.length = roots.length ∧
      ∀ index ticket handle, entries[index]? = some (ticket, handle) →
        ∃ tree, roots[roots.length - (index + 1)]? = some tree ∧
          Stored.Endpoints.Core.childFromHistory after.writer.accepted (BitVec.ofNat 32 handle) = some tree := by
  obtain ⟨entries, transcript, count, issued⟩ := journal
  obtain ⟨roots, accepted, _⟩ := endpoint_publications run
  have sized : entries.length = roots.length := by
    have lengths := congrArg List.length accepted
    simp only [List.length_append] at lengths
    omega
  refine ⟨entries, roots, transcript, accepted, sized, ?_⟩
  intro index ticket handle entry
  have indexBound : index < entries.length := by
    by_contra! beyond
    rw [List.getElem?_eq_none beyond] at entry
    contradiction
  obtain ⟨position, inWord⟩ := issued index ticket handle entry
  have positive : 0 < handle := by omega
  have within : handle ≤ after.writer.accepted.length := by omega
  have offset : after.writer.accepted.length - handle = roots.length - (index + 1) := by omega
  have inRoots : roots.length - (index + 1) < roots.length := by omega
  refine ⟨roots[roots.length - (index + 1)], List.getElem?_eq_getElem inRoots, ?_⟩
  have asWord : (BitVec.ofNat 32 handle).toNat = handle := Nat.mod_eq_of_lt inWord
  simp only [Stored.Endpoints.Core.childFromHistory, asWord]
  simp [positive, within]
  rw [offset, accepted, List.getElem?_append_left inRoots, List.getElem?_eq_getElem inRoots]

theorem retained_target {before after : State sig} (run : WriterRun before after)
    {handle : BitVec 32} {tree : Stored.OwnedMemory.Tree sig}
    (selected : Stored.Endpoints.Core.childFromHistory before.accepted handle = some tree) :
    Stored.Endpoints.Core.childFromHistory after.accepted handle = some tree := by
  obtain ⟨roots, accepted, _⟩ := endpoint_publications run
  by_cases valid : 0 < handle.toNat ∧ handle.toNat ≤ before.accepted.length
  · have size : after.accepted.length = roots.length + before.accepted.length := by simp [accepted]
    have within : handle.toNat ≤ after.accepted.length := by omega
    have oldOffset : roots.length ≤ after.accepted.length - handle.toNat := by omega
    have offset : after.accepted.length - handle.toNat - roots.length = before.accepted.length - handle.toNat := by
      omega
    simp [Stored.Endpoints.Core.childFromHistory, valid.1, valid.2] at selected
    simp [Stored.Endpoints.Core.childFromHistory, valid.1, within]
    rw [show after.accepted[after.accepted.length - handle.toNat]? =
      before.accepted[before.accepted.length - handle.toNat]? by
      conv_lhs => enter [1]; rw [accepted]
      rw [List.getElem?_append_right oldOffset, offset]]
    exact selected
  · simp [Stored.Endpoints.Core.childFromHistory, valid] at selected

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
      Stored.Endpoints.Core.childFromHistory published.host.writer.accepted (BitVec.ofNat 32 handle) = some tree ∧
      Stored.Endpoints.Core.childFromHistory final.host.writer.accepted (BitVec.ofNat 32 handle) = some tree := by
  have checkedFirst := checked_of_steps bindings first safe firstSafe
  have checkedLater := checked_of_steps bindings later
    (checked_cfgSafe_of_steps bindings first safe firstSafe) laterSafe
  obtain ⟨entries, roots, journal, accepted, sized, targets⟩ :=
    publication_targets checkedFirst.2.1 checkedFirst.2.2
  have singleton : entries = [(ticket, handle)] := List.append_cancel_left (journal.symm.trans recorded)
  subst entries
  have one : roots.length = 1 := sized.symm
  have onlyRoot : ∃ tree, roots = [tree] := by
    cases roots with
    | nil => simp at one
    | cons root tail =>
      cases tail with
      | nil => exact ⟨root, rfl⟩
      | cons next remaining => simp at one
  obtain ⟨tree, rfl⟩ := onlyRoot
  obtain ⟨selected, same, lookup⟩ := targets 0 ticket handle rfl
  have sameTree : selected = tree := Option.some.inj same.symm
  subst selected
  obtain ⟨laterEntries, laterJournal, _⟩ := checkedLater.2.2
  refine ⟨tree, accepted, ?_, lookup, retained_target checkedLater.2.1 lookup⟩
  rw [laterJournal, recorded, List.append_assoc, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

theorem publication_lookup_iff {before after : HostState sig}
    (journal : PublicationDelta before after) {handle : BitVec 32}
    (fresh : before.writer.accepted.length < handle.toNat) :
    (Stored.Endpoints.Core.childFromHistory after.writer.accepted handle).isSome = true ↔
      ∃ ticket, after.publications[before.publications.length +
        (handle.toNat - (before.writer.accepted.length + 1))]? = some (ticket, handle.toNat) := by
  obtain ⟨entries, appended, size, issued⟩ := journal
  let index := handle.toNat - (before.writer.accepted.length + 1)
  have position : handle.toNat = before.writer.accepted.length + index + 1 := by
    dsimp [index]
    omega
  have positive : 0 < handle.toNat := by omega
  change _ ↔ ∃ ticket, after.publications[before.publications.length + index]? = some (ticket, handle.toNat)
  rw [appended, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
  constructor
  · intro found
    have within : handle.toNat ≤ after.writer.accepted.length := by
      by_contra! notWithin
      simp [Stored.Endpoints.Core.childFromHistory, positive, Nat.not_le.mpr notWithin] at found
    have inEntries : index < entries.length := by omega
    let item := entries[index]
    have entry : entries[index]? = some (item.1, item.2) := List.getElem?_eq_getElem inEntries
    have valid := (issued index item.1 item.2 entry).1
    exact ⟨item.1, by simpa only [show item.2 = handle.toNat by omega] using entry⟩
  · rintro ⟨ticket, entry⟩
    have inEntries : index < entries.length := by
      by_contra! outOfRange
      simp [List.getElem?_eq_none outOfRange] at entry
    have within : handle.toNat ≤ after.writer.accepted.length := by omega
    have offset : after.writer.accepted.length - handle.toNat < after.writer.accepted.length := by omega
    simp [Stored.Endpoints.Core.childFromHistory, positive, within, List.getElem?_eq_getElem offset]

private theorem writer_growth {before after : State sig} (step : WriterStep before after)
    (grows : before.accepted.length < after.accepted.length) :
    ∃ tree, before.register tree = .ok after ∧ after.accepted = tree :: before.accepted := by
  cases step with
  | same => exact (Nat.lt_irrefl _ grows).elim
  | spend update => cases update <;> exact (Nat.lt_irrefl _ grows).elim
  | publish tree registered => exact ⟨tree, registered, (Stored.OwnedMemory.Claims.register_claims registered).1⟩

theorem publication_origin {implementation : HostImpl (core3 grow) (HostState sig)}
    (hostSafe : HostImplSafe CheckedWrite implementation)
    {initial final : Config (core3 grow) (HostState sig)}
    {labels : List (Label (core3 grow) (HostState sig))}
    (steps : Steps prof ready (specDispatch ready implementation) initial labels final)
    (safe : CfgSafe CheckedWrite initial) (runSafe : RunSafe CheckedWrite labels)
    {handle : BitVec 32} {tree : Stored.OwnedMemory.Tree sig}
    (fresh : initial.host.writer.accepted.length < handle.toNat)
    (selected : Stored.Endpoints.Core.childFromHistory final.host.writer.accepted handle = some tree) :
    PublicationCut (prof := prof) (ready := ready) (dispatch := specDispatch ready implementation)
      initial labels final handle tree := by
  have checked := HostWrite.hostSafe_dispatch hostSafe Limits.spec Quirks.none ready
  induction steps with
  | refl =>
    simp [Stored.Endpoints.Core.childFromHistory, Nat.not_le.mpr fresh] at selected
  | @cons current next final label suffix first tail ih =>
    have nextSafe := HostWrite.step_cfgSafe checked first safe (fun program equal => runSafe program (by simp [equal]))
    have safeTail : RunSafe CheckedWrite suffix := fun program member => runSafe program (List.mem_cons_of_mem _ member)
    by_cases within : handle.toNat ≤ next.host.writer.accepted.length
    · have grows : current.host.writer.accepted.length < next.host.writer.accepted.length := by omega
      have allowed : CheckedWrite current.host next.host := by
        rcases HostWrite.step_host first safe with same | allowed
        · rw [same] at grows
          exact (Nat.lt_irrefl _ grows).elim
        · exact allowed
      obtain ⟨root, registered, accepted⟩ := writer_growth allowed.2.1 grows
      have count : next.host.writer.accepted.length = current.host.writer.accepted.length + 1 := by simp [accepted]
      have handleNumber : handle.toNat = current.host.writer.accepted.length + 1 := by omega
      have atRoot : Stored.Endpoints.Core.childFromHistory next.host.writer.accepted handle = some root := by
        have positive : 0 < handle.toNat := by omega
        have offset : next.host.writer.accepted.length - handle.toNat = 0 := by omega
        simp [Stored.Endpoints.Core.childFromHistory, positive, within, offset]
        simp [accepted]
      have keeps := retained_target (checked_host_of_steps hostSafe tail nextSafe safeTail).2.1 atRoot
      have sameRoot : root = tree := Option.some.inj (keeps.symm.trans selected)
      subst root
      obtain ⟨entries, appended, size, numbered⟩ := allowed.2.2
      have single : entries.length = 1 := by omega
      obtain ⟨⟨ticket, number⟩, rfl⟩ := List.length_eq_one_iff.mp single
      have numberEq : number = handle.toNat := (numbered 0 ticket number rfl).1.trans (by simp [handleNumber])
      exact ⟨[], label, suffix, current, next, ticket, rfl, .refl _, first, tail,
        handleNumber, registered, by simpa only [numberEq] using appended⟩
    · obtain ⟨earlier, event, rest, before, after, ticket, split, enters, publishes, continues, number, registered,
        journal⟩ := ih nextSafe safeTail (Nat.lt_of_not_ge within) selected
      exact ⟨label :: earlier, event, rest, before, after, ticket, congrArg (label :: ·) split,
        .cons first enters, publishes, continues, number, registered, journal⟩

theorem publication_cut_target {implementation : HostImpl (core3 grow) (HostState sig)}
    (hostSafe : HostImplSafe CheckedWrite implementation)
    {initial final : Config (core3 grow) (HostState sig)}
    {labels : List (Label (core3 grow) (HostState sig))}
    (safe : CfgSafe CheckedWrite initial) (runSafe : RunSafe CheckedWrite labels)
    {handle : BitVec 32} {tree : Stored.OwnedMemory.Tree sig}
    (cut : PublicationCut (prof := prof) (ready := ready) (dispatch := specDispatch ready implementation)
      initial labels final handle tree) :
    Stored.Endpoints.Core.childFromHistory final.host.writer.accepted handle = some tree := by
  obtain ⟨earlier, label, suffix, before, after, _, rfl, enters, publishes, continues, number, registered, _⟩ := cut
  have checked := HostWrite.hostSafe_dispatch hostSafe Limits.spec Quirks.none ready
  have beforeSafe := HostWrite.steps_cfgSafe checked enters safe
    (fun program member => runSafe program (List.mem_append_left _ member))
  have afterSafe := HostWrite.step_cfgSafe checked publishes beforeSafe
    (fun program equal => runSafe program (List.mem_append_right _ (by simp [equal])))
  have tail := checked_host_of_steps hostSafe continues afterSafe
    (fun program member => runSafe program (List.mem_append_right _ (List.mem_cons_of_mem _ member)))
  apply retained_target tail.2.1
  rw [(Stored.OwnedMemory.Claims.register_claims registered).1]
  simp [Stored.Endpoints.Core.childFromHistory, number]

theorem publication_cut_iff {implementation : HostImpl (core3 grow) (HostState sig)}
    (hostSafe : HostImplSafe CheckedWrite implementation)
    {initial final : Config (core3 grow) (HostState sig)}
    {labels : List (Label (core3 grow) (HostState sig))}
    (steps : Steps prof ready (specDispatch ready implementation) initial labels final)
    (safe : CfgSafe CheckedWrite initial) (runSafe : RunSafe CheckedWrite labels)
    {handle : BitVec 32} {tree : Stored.OwnedMemory.Tree sig}
    (fresh : initial.host.writer.accepted.length < handle.toNat) :
    Stored.Endpoints.Core.childFromHistory final.host.writer.accepted handle = some tree ↔
    PublicationCut (prof := prof) (ready := ready) (dispatch := specDispatch ready implementation)
      initial labels final handle tree :=
  ⟨publication_origin hostSafe steps safe runSafe fresh, publication_cut_target hostSafe safe runSafe⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.ScheduledTranscript

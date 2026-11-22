module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadLeaf.Local.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Plain.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.CanonicalTree.Defs
public import Silmaril.Wasm.Component.Reference.Engine.Core3.Grows.Defs
public import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Occurrence.Defs
import Silmaril.Wasm.Component.Reference.Canon.Prog.Thms
import Silmaril.Wasm.Component.Reference.Canon.Flat.Thms
import Silmaril.Wasm.Component.Reference.Machine.CoreGrowth.Thms
import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Occurrence.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Plain.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadLeaf.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LocalLeaf

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
  Silmaril.Wasm.Component.AsyncRef
open Silmaril.Wasm.Game.HandleAccept.Wit Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open Silmaril.Wasm.Component.Machine.ReturnFrame.Occurrence

variable {E : CoreEngine} {Host Result : Type}

local notation "LocalProg" => Prog.Every (S := Eff E Host) LocalStoreOp

theorem eval {body : P E Host Result} (only : LocalProg body) (thread : Option ThreadId) (store : CStore E) :
    ∃ (reached : CStore E) (outcome : Except TrapReason Result), ∀ host,
      Plain.runBody body store host (some thread) = (reached, host, outcome.mapError .trapped) := by
  induction only generalizing store with
  | pure value => exact ⟨store, .ok value, fun _ => rfl⟩
  | @op op next allowed continuation ih =>
    cases op <;> try contradiction
    · exact ih store store
    · rename_i update
      exact ih () (update store)
    · rename_i reason
      exact ⟨store, .error reason, fun _ => rfl⟩
    · exact ih thread store

private theorem localGet : LocalProg (getStore : P E Host (CStore E)) :=
  .op trivial (fun _ => .pure _)

private theorem localModify (update : CStore E → CStore E) : LocalProg (modifyStore (σ := Host) update) :=
  .op trivial (fun _ => .pure _)

private theorem localTrap (reason : TrapReason) : LocalProg (trap reason : P E Host Result) :=
  .op trivial (fun answer => nomatch answer)

private theorem localOrTrap (reason : TrapReason) (value : Option Result) :
    LocalProg (orTrap reason value : P E Host Result) := by
  cases value
  · exact localTrap reason
  · exact .pure _

private theorem localInst (inst : InstId) : LocalProg (getInst inst : P E Host InstState) := by
  unfold getInst getObj
  refine localGet.bind fun store => ?_
  cases ArenaField.insts.get? store inst
  · exact localTrap _
  · exact .pure _

private theorem localAdd (inst : InstId) (entry : HandleEntry) :
    LocalProg (handlesAdd inst entry : P E Host Nat) := by
  unfold handlesAdd
  refine (localInst inst).bind fun state => ?_
  split
  · exact localTrap _
  · exact (localModify _).bind (fun _ => .pure _)

private theorem localRemove (inst : InstId) (slot : Nat) : LocalProg (handlesRemove inst slot : P E Host HandleEntry) := by
  unfold handlesRemove
  refine (localInst inst).bind fun state => ?_
  cases state.removeHandle? slot with
  | none => exact localTrap _
  | some removed => cases removed; exact (localModify _).bind fun _ => .pure _

private theorem localTrapIf (guard : Bool) (reason : TrapReason) : LocalProg (trapIf guard reason : P E Host Unit) := by
  cases guard
  · exact .pure ()
  · exact localTrap reason

theorem localTake (limits : Component.Limits) (cx : LiftLowerContext E) (rt : RtId) (slot : Nat) :
    LocalProg (Resources.take (World := Host) limits cx rt slot) := by
  unfold Resources.take Resources.takeWith
  refine (localRemove cx.inst slot).bind fun entry => ?_
  cases entry with
  | resource identity =>
    simp only [expectResource, Prog.bind_eq, Prog.pure_eq, Prog.pure_bind']
    have fetched : LocalProg (getResHandle identity : P E Host ResourceHandle) := by
      unfold getResHandle getObj
      refine localGet.bind fun store => ?_
      cases ArenaField.resHandles.get? store identity
      · exact localTrap _
      · exact .pure _
    exact fetched.bind (fun handle =>
      (localTrapIf (handle.rt != rt) .resourceTypeMismatch).bind fun _ =>
      (localTrapIf (handle.numLends != 0) .ownLent).bind fun _ =>
      (localTrapIf (!handle.own) .notOwnHandle).bind fun _ => .pure (Resources.Owned.mk identity handle.rep))
  | waitable _ | wset _ | errCtx _ =>
    simp only [expectResource, Prog.bind_eq, trap]
    exact .op trivial (fun answer => nomatch answer)

private theorem localOwn (limits : Component.Limits) (cx : LiftLowerContext E) (rt : RtId) (rep : Nat) :
    LocalProg (lowerOwn limits cx rt rep : P E Host Nat) :=
  localGet.bind fun _ => (localModify _).bind fun _ => localAdd cx.inst _

private theorem localEnd (limits : Component.Limits) (kind : EndKind) (cx : LiftLowerContext E) (id : EndId) :
    LocalProg (lowerAsyncValue limits kind cx id : P E Host Nat) :=
  (localModify _).bind fun _ => (localAdd cx.inst _).bind fun _ => (localModify _).bind fun _ => .pure _

private theorem localWord (cx : LiftLowerContext E) (word : Nat) (ptr : Nat) :
    LocalProg (storeInt cx word ptr 4 : P E Host Unit) := by
  unfold storeInt writeMem memAddr
  refine (localOrTrap _ _).bind fun address => localGet.bind fun store => ?_
  split
  · exact localTrap _
  · exact localModify _

theorem localHandle (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E)
    (width : AddrType) (item : Field) (output : Stored.Lower.Output) (handle : CanonicalHandle item) :
    LocalProg (CanonicalTree.leaf limits quirks cx width item output : P E Host output.Result) := by
  cases item with
  | owner receipt =>
    have lower := localOwn (Host := Host) limits cx receipt.1 receipt.2.representation
    cases output with
    | memory ptr =>
      simp only [CanonicalTree.leaf, Field.type, Field.value, store]
      exact lower.bind fun word => localWord cx word ptr
    | flat => exact lower.bind fun _ => .pure _
  | endpoint channel element id =>
    cases channel <;> cases output
    · rename_i ptr
      simp only [CanonicalTree.leaf, Field.type, Field.value, Stored.Endpoints.ListLower.endpointType, store]
      exact (localEnd limits .readableStream cx id).bind fun word => localWord cx word ptr
    · exact (localEnd limits .readableStream cx id).bind fun _ => .pure _
    · rename_i ptr
      simp only [CanonicalTree.leaf, Field.type, Field.value, Stored.Endpoints.ListLower.endpointType, store]
      exact (localEnd limits .readableFuture cx id).bind fun word => localWord cx word ptr
    · exact (localEnd limits .readableFuture cx id).bind fun _ => .pure _
  | context id =>
    cases output with
    | memory ptr =>
      simp only [CanonicalTree.leaf, Field.type, Field.value, store]
      exact (localAdd cx.inst (.errCtx id)).bind fun word => localWord cx word ptr
    | flat => exact (localAdd cx.inst (.errCtx id)).bind fun _ => .pure _
  | _ => contradiction

private theorem executePair {profile : ProfileKind} {ready : HostReady Host}
    {dispatch reference : Call E → P E Host (Ret E)} {body : P E Host Result} (only : LocalProg body)
    (left right : Config E Host) (reached : CStore E) (outcome : Except TrapReason Result)
    (checkNext canonNext : Result → P E Host (Ret E)) {thread checkFrames checkRest canonFrames canonRest}
    (same : left.store = right.store)
    (checkAt : left.ctl = ⟨thread, .prog (body >>= checkNext), checkFrames⟩ :: checkRest)
    (canonAt : right.ctl = ⟨thread, .prog (body >>= canonNext), canonFrames⟩ :: canonRest)
    (evaluated : Plain.runBody body left.store left.host (some thread) =
      (reached, left.host, outcome.mapError .trapped)) :
    ∃ labels, LocalLeafLabels outcome labels ∧ PairedLeafSteps profile ready dispatch reference left right labels
      (localLeafEnd left left.host reached thread checkFrames checkRest checkNext outcome)
      (localLeafEnd right right.host reached thread canonFrames canonRest canonNext outcome) := by
  induction only generalizing left right with
  | pure value =>
    cases outcome <;> simp [Plain.runBody, Except.mapError] at evaluated
    obtain ⟨rfl, rfl⟩ := evaluated
    have leftEnd : localLeafEnd left left.host left.store thread checkFrames checkRest checkNext (.ok value) = left := by
      cases left; simp_all [localLeafEnd]
    have rightEnd : localLeafEnd right right.host left.store thread canonFrames canonRest canonNext (.ok value) = right := by
      cases right; simp_all [localLeafEnd]
    rw [leftEnd, rightEnd]
    exact ⟨[], by simp [LocalLeafLabels], .done same⟩
  | @op operation next allowed children ih =>
    have advance (response : operation.Resp) (leftStore rightStore : CStore E)
        (store : leftStore = rightStore)
        (checkStep : Step profile ready dispatch left .tau
          { left with store := leftStore, ctl := ⟨thread, .prog (next response >>= checkNext), checkFrames⟩ :: checkRest })
        (canonStep : Step profile ready reference right .tau
          { right with store := rightStore, ctl := ⟨thread, .prog (next response >>= canonNext), canonFrames⟩ :: canonRest })
        (checkEdit : transitionEdit left .tau = .same) (canonEdit : transitionEdit right .tau = .same)
        (evaluated : Plain.runBody (next response) leftStore left.host (some thread) =
          (reached, left.host, outcome.mapError .trapped)) :
        ∃ labels, LocalLeafLabels outcome labels ∧ PairedLeafSteps profile ready dispatch reference left right labels
          (localLeafEnd left left.host reached thread checkFrames checkRest checkNext outcome)
          (localLeafEnd right right.host reached thread canonFrames canonRest canonNext outcome) := by
      obtain ⟨labels, kind, tail⟩ := ih response
        { left with store := leftStore, ctl := ⟨thread, .prog (next response >>= checkNext), checkFrames⟩ :: checkRest }
        { right with store := rightStore, ctl := ⟨thread, .prog (next response >>= canonNext), canonFrames⟩ :: canonRest }
        store rfl rfl evaluated
      refine ⟨.tau :: labels, ?_, ?_⟩
      · cases outcome with
        | ok value => simpa [LocalLeafLabels] using kind
        | error reason =>
          obtain ⟨count, rfl⟩ := kind
          exact ⟨count + 1, by rw [List.replicate_succ, List.cons_append]⟩
      · cases outcome <;> exact .step same checkStep canonStep rfl rfl checkEdit (canonEdit.trans checkEdit.symm) tail
    cases operation <;> try contradiction
    case get =>
      exact advance left.store left.store right.store same (.get checkAt) (by rw [same]; exact .get canonAt)
        (by rw [transitionEdit, checkAt]; rfl) (by rw [transitionEdit, canonAt]; rfl) evaluated
    case modify update =>
      exact advance () (update left.store) (update right.store) (congrArg update same) (.modify checkAt) (.modify canonAt)
        (by rw [transitionEdit, checkAt]; rfl) (by rw [transitionEdit, canonAt]; rfl) evaluated
    case trap reason =>
      cases outcome <;> simp [Plain.runBody, Except.mapError] at evaluated
      obtain ⟨rfl, rfl⟩ := evaluated
      rw [show localLeafEnd right right.host left.store thread canonFrames canonRest canonNext (.error reason) =
        StepDefs.trapCfg right by rw [same]; rfl]
      exact ⟨[.trap reason], ⟨0, rfl⟩, .step same (.trap checkAt) (.trap canonAt) rfl rfl rfl rfl
        (.done (congrArg StepDefs.lockdownSt same))⟩
    case currentThread =>
      exact advance thread left.store right.store same (.currentThread checkAt) (.currentThread canonAt)
        (by rw [transitionEdit, checkAt]; rfl) (by rw [transitionEdit, canonAt]; rfl) evaluated

private theorem pairTracks {profile : ProfileKind} {ready : HostReady Host}
    {dispatch reference : Call E → P E Host (Ret E)} {left right reached peer labels} {outcome : Except TrapReason Result}
    (path : PairedLeafSteps profile ready dispatch reference left right labels reached peer)
    (kind : LocalLeafLabels outcome labels) (mark : Option Location) :
    Trail profile ready dispatch left mark labels reached (localOccurrenceEnd outcome mark) ∧
    Trail profile ready reference right mark labels peer (localOccurrenceEnd outcome mark) := by
  induction path generalizing mark with
  | done =>
    cases outcome with
    | ok => exact ⟨.done _ _, .done _ _⟩
    | error reason => obtain ⟨count, empty⟩ := kind; simp at empty
  | @step left right middle actual reached peer label labels _ checked raw _ _ checkedEdit sameEdit tail ih =>
    cases label with
    | tau =>
      have kindTail : LocalLeafLabels outcome labels := by
        cases outcome with
        | ok value => simpa [LocalLeafLabels] using kind
        | error reason =>
          obtain ⟨count, shape⟩ := kind
          cases count with
          | zero => simp at shape
          | succ count => exact ⟨count, by simpa [List.replicate_succ] using shape⟩
      obtain ⟨ltrack, rtrack⟩ := ih kindTail mark
      exact ⟨.step checked (by rw [checkedEdit]; cases mark <;> exact ltrack),
        .step raw (by rw [sameEdit, checkedEdit]; cases mark <;> exact rtrack)⟩
    | trap reason =>
      cases outcome with
      | ok value => simp [LocalLeafLabels] at kind
      | error stopped =>
        obtain ⟨count, shape⟩ := kind
        cases count with
        | succ count => simp [List.replicate_succ] at shape
        | zero =>
          simp at shape
          obtain ⟨rfl, rfl⟩ := shape
          cases tail
          exact ⟨.step checked (by rw [checkedEdit]; cases mark with | none => exact .done _ _ | some place => cases place <;> exact .done _ _),
            .step raw (by rw [sameEdit, checkedEdit]; cases mark with | none => exact .done _ _ | some place => cases place <;> exact .done _ _)⟩
    | core | host | choice | obs =>
      cases outcome with
      | ok value => simp [LocalLeafLabels] at kind
      | error reason =>
        obtain ⟨count, shape⟩ := kind
        cases count <;> simp [List.replicate_succ] at shape

variable {grow : SingleThreaded.GrowOracle} {sig : Stored.Signature}
  {profile : ProfileKind} {ready : HostReady (HostState sig)}
  {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}

private theorem chain {before middle after : Config (core3 grow) (HostState sig)} {front back}
    (left : Steps profile ready dispatch before front middle) (right : Steps profile ready dispatch middle back after) :
    Steps profile ready dispatch before (front ++ back) after := by
  induction left with
  | refl => exact right
  | cons step _ ih => exact .cons step (ih right)

private theorem runBody_keeps {keep : CStore E → Prop} {body : P E Host Result}
    (invariant : P.Inv keep body) (thread : Option ThreadId) (reference : CStore E) (host : Host)
    (valid : keep reference) : keep (Plain.runBody body reference host (some thread)).1 := by
  induction invariant generalizing reference host with
  | pure result => exact valid
  | @op operation next admitted _ ih =>
    cases operation <;> simp only [Plain.runBody]
    all_goals first
      | exact valid
      | exact ih reference reference host valid
      | exact ih () _ host (admitted reference valid)
      | exact ih host reference host valid
      | exact ih () reference _ valid
      | exact ih thread reference host valid

private theorem canonical_growth (base : CStore (core3 grow)) (destination : RecordDestination) (inst : InstId)
    (item : Field) (output : Stored.Lower.Output) :
    P.Inv (fun (store : CStore (core3 grow)) => Core3.Grows base.core store.core)
      (CanonicalTree.leaf Component.Limits.spec Quirks.none (destination.context inst) destination.width item output :
        Session grow sig output.Result) := by
  let keep := fun (store : CStore (core3 grow)) => Core3.Grows base.core store.core
  have laws : P.Inv.StorePres keep :=
    ⟨fun mem ptr bytes store valid => valid.trans (writeMemSt_grows store mem ptr bytes),
      fun _ _ valid => valid, fun _ _ _ valid => valid, fun _ _ valid => valid,
      fun _ _ _ valid => valid, fun _ _ _ valid => valid⟩
  cases output with
  | memory ptr => exact P.Inv.store laws _ _ _ _ _ ptr
  | flat => exact P.Inv.lowerFlatAt laws _ _ _ _ _ _

theorem compare {reference : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    {checked canonical : Config (core3 grow) (HostState sig)}
    (sameStore : checked.store = canonical.store) (destination : RecordDestination) (inst : InstId)
    (item : Field) (handle : CanonicalHandle item) (index : Nat) (output : Stored.Lower.Output)
    (checkNext : Except Stored.Endpoints.RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow))) {thread checkFrames checkRest canonFrames canonRest}
    (checkAt : checked.ctl = ⟨thread, .prog (Record.Effects.checkedLeaf recordClaims Component.Limits.spec Quirks.none
      (destination.context inst) destination.width item index output >>= checkNext), checkFrames⟩ :: checkRest)
    (canonAt : canonical.ctl = ⟨thread, .prog (CanonicalTree.leaf Component.Limits.spec Quirks.none
      (destination.context inst) destination.width item output >>= canonNext), canonFrames⟩ :: canonRest) :
    match liveLeafPlan checked.store checked.host.writer index item with
    | .error issue => ∃ labels, (∀ label ∈ labels, label = .tau) ∧ LeafGuardSteps profile ready dispatch checked labels
        { checked with ctl := ⟨thread, .prog (checkNext (.error issue)), checkFrames⟩ :: checkRest } none
    | .ok plan =>
      let host := plan.elim checked.host (fun spend => { checked.host with writer := spend.apply checked.host.writer })
      ∃ reached outcome leading checkLabels canonLabels,
        Core3.Grows canonical.store.core reached.core ∧
        (∀ label ∈ leading, label = .tau) ∧ LocalLeafLabels outcome checkLabels ∧ LocalLeafLabels outcome canonLabels ∧
        Steps profile ready dispatch checked (leading ++ checkLabels)
          (localLeafEnd checked host reached thread checkFrames checkRest (fun result => checkNext (.ok result)) outcome) ∧
        Steps profile ready reference canonical canonLabels
          (localLeafEnd canonical canonical.host reached thread canonFrames canonRest canonNext outcome) ∧
        (∀ mark, Trail profile ready dispatch checked mark (leading ++ checkLabels)
          (localLeafEnd checked host reached thread checkFrames checkRest (fun result => checkNext (.ok result)) outcome)
          (localOccurrenceEnd outcome mark) ∧
          Trail profile ready reference canonical mark canonLabels
            (localLeafEnd canonical canonical.host reached thread canonFrames canonRest canonNext outcome)
            (localOccurrenceEnd outcome mark)) ∧
        (∀ value, outcome = .ok value →
          RetainsActiveSlots profile ready dispatch checked (leading ++ checkLabels)
            (localLeafEnd checked host reached thread checkFrames checkRest (fun result => checkNext (.ok result)) (.ok value)) ∧
          RetainsActiveSlots profile ready reference canonical canonLabels
            (localLeafEnd canonical canonical.host reached thread canonFrames canonRest canonNext (.ok value))) ∧
        GuardedLeafSteps profile ready dispatch reference checked canonical leading checkLabels canonLabels
          (localLeafEnd checked host reached thread checkFrames checkRest (fun result => checkNext (.ok result)) outcome)
          (localLeafEnd canonical canonical.host reached thread canonFrames canonRest canonNext outcome) plan ∧
        ∀ update, plan = some update → ExclusiveLeafWriterFlow update checked.host canonical.host
          (localLeafEnd checked host reached thread checkFrames checkRest (fun result => checkNext (.ok result)) outcome).host
          (localLeafEnd canonical canonical.host reached thread canonFrames canonRest canonNext outcome).host := by
  let body := (CanonicalTree.leaf Component.Limits.spec Quirks.none (destination.context inst)
    destination.width item output : Session grow sig output.Result)
  obtain ⟨guardLabels, guardSilent, guardSteps⟩ := RecordDestination.checked_leaf_prefix
    (profile := profile) (ready := ready) (dispatch := dispatch) checked destination inst item index output checkNext checkAt
  cases verdict : liveLeafPlan checked.store checked.host.writer index item with
  | error issue =>
    exact ⟨guardLabels, guardSilent, by simpa only [verdict, Except.toOption, Option.join, Option.bind] using guardSteps⟩
  | ok plan =>
    let host := plan.elim checked.host (fun spend => { checked.host with writer := spend.apply checked.host.writer })
    let checkedNext := { checked with host, ctl := ⟨thread, .prog (body >>= fun result => checkNext (.ok result)),
      checkFrames⟩ :: checkRest }
    have guard : LeafGuardSteps profile ready dispatch checked guardLabels checkedNext plan := by
      cases plan <;> simpa only [verdict, checkedNext, host, body, Option.elim, Except.toOption, Option.join, Option.bind, id] using guardSteps
    have prefixTracks := guard.tracks
    obtain ⟨reached, outcome, evaluated⟩ := eval
      (localHandle Component.Limits.spec Quirks.none (destination.context inst) destination.width item output handle)
      thread checked.store
    have checkedEval : Plain.runBody body checkedNext.store checkedNext.host (some thread) =
        (reached, checkedNext.host, outcome.mapError .trapped) := evaluated host
    have canonEval : Plain.runBody body canonical.store canonical.host (some thread) =
        (reached, canonical.host, outcome.mapError .trapped) := sameStore ▸ evaluated canonical.host
    have grown : Core3.Grows canonical.store.core reached.core := by
      have kept := runBody_keeps (canonical_growth (sig := sig) canonical.store destination inst item output)
        thread canonical.store canonical.host (Core3.Grows.refl _)
      change Core3.Grows canonical.store.core (Plain.runBody body canonical.store canonical.host (some thread)).1.core at kept
      rw [canonEval] at kept
      exact kept
    obtain ⟨labels, trace, bodyRun⟩ := executePair (profile := profile) (ready := ready) (dispatch := dispatch) (reference := reference)
      (localHandle Component.Limits.spec Quirks.none (destination.context inst) destination.width item output handle)
      checkedNext canonical reached outcome (fun result => checkNext (.ok result)) canonNext sameStore rfl canonAt checkedEval
    have tracks := pairTracks bodyRun trace
    have guardRun := (prefix_survives (prefixTracks (.active 0 0))).1
    refine ⟨reached, outcome, guardLabels, labels, labels, grown, guardSilent, trace, trace,
      ?_, (tracks none).2.steps, ?_, ?_, ⟨checkedNext, guard, rfl, ?_⟩, ?_⟩
    · cases outcome <;> exact chain guardRun (tracks none).1.steps
    · intro mark
      refine ⟨?_, (tracks mark).2⟩
      have stitched (startMark) : Trail profile ready dispatch checked startMark guardLabels checkedNext startMark := by
        cases startMark with
        | none => exact Trail.absent guardRun
        | some place => exact (prefixTracks place).toTrail
      cases outcome <;> exact (stitched mark).append (tracks mark).1
    · intro value success
      cases success
      have retained (place : Location) := tracks (some place)
      refine ⟨fun depth => ?_, fun depth => ?_⟩
      · obtain ⟨place, equal, path⟩ := (retained (.active 0 depth)).1.survives
        cases equal
        exact (prefixTracks _).append path
      · obtain ⟨place, equal, path⟩ := (retained (.active 0 depth)).2.survives
        cases equal
        exact path
    · cases outcome <;> exact bodyRun
    · intro update chosen
      subst plan
      have live := liveLeafPlan_spend_live verdict
      cases outcome <;> exact ⟨live, rfl, rfl, fun agrees => agrees.asymmetricSpend live⟩

theorem endpoint_registration_split {sig : Stored.Signature} {id : EndId}
    {left right checked canonical : HostState sig}
    (flow : ExclusiveLeafWriterFlow (.endpoint id) left right checked canonical)
    (agrees : left.writer.LiveClaimsAgree right.writer) (tree : Stored.OwnedMemory.Tree sig)
    (unowned : rootReceipts tree = []) (one : rootEndpoints tree = [id]) :
    ∃ registered, checked.writer.register tree = .ok registered ∧ canonical.writer.register tree = .error .alias := by
  have peerLive := (agrees.endpoints id).mp flow.live
  rw [flow.checkedHost, flow.canonicalHost]
  let spent := (Spend.endpoint id).apply left.writer
  have absent : id ∉ spent.endpoints := (Spend.endpoint id).not_live left.writer
  refine ⟨⟨tree :: spent.accepted, spent.held, [id] ++ spent.endpoints⟩, ?_, ?_⟩
  · change spent.register tree = _
    simp [State.register, unowned, one, absent]
  · simp [State.register, unowned, one, peerLive]

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LocalLeaf

module

public import Silmaril.Wasm.Component.Reference.Machine.CoreGrowth.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Context.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Dispatch.Defs
import Silmaril.Wasm.Component.Reference.Canon.Lift.Thms
import Silmaril.Wasm.Component.Reference.Canon.Lower.Thms
import Silmaril.Wasm.Component.Reference.Canon.Callout.Thms
import Silmaril.Wasm.Component.Reference.Machine.Config.Thms
import Silmaril.Wasm.Component.Reference.Machine.Step.Thms
import Silmaril.Wasm.Component.Reference.Engine.Core3.StepLaws.Grows.Defs
import Silmaril.Wasm.Component.Reference.Engine.Core3.Store.Defs

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.MachineCoreGrowth

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Execution.Core

variable {grow : SingleThreaded.GrowOracle} {Host : Type}
  {profile : ProfileKind} {ready : HostReady Host}
  {dispatch : Call (core3 grow) → P (core3 grow) Host (Ret (core3 grow))}
  {before after : Config (core3 grow) Host} {label : Label (core3 grow) Host}
  {trace : List (Label (core3 grow) Host)}

theorem step_grows (step : Step profile ready dispatch before label after)
    (updates : CoreUpdateGrows before) : Core3.Grows before.store.core after.store.core := by
  cases step <;> try exact Core3.Grows.refl _
  case hostDone =>
    unfold StepDefs.hostFinish
    split <;> exact Core3.Grows.refl _
  case coreInternal internal => exact Core3.internal_grows internal
  case modify focused => simpa only [CoreUpdateGrows, focused] using updates
  case newThread allocated =>
    cases allocated
    exact Core3.Grows.refl _
  case emit =>
    unfold StepDefs.observe
    split <;> exact Core3.Grows.refl _

theorem update_of_inv {thread segments rest} (program : P (core3 grow) Host (Ret (core3 grow)))
    (focused : before.ctl = ⟨thread, .prog program, segments⟩ :: rest)
    (preserves : P.Inv (fun store => Core3.Grows before.store.core store.core) program) :
    CoreUpdateGrows before := by
  rw [CoreUpdateGrows, focused]
  cases program with
  | pure => trivial
  | op op _ =>
    cases op <;> try trivial
    cases preserves with
    | op update _ => exact update _ (Core3.Grows.refl _)

theorem steps (run : CoreGrowthSteps profile ready dispatch before trace after) :
    Steps profile ready dispatch before trace after := by
  induction run with
  | refl => exact .refl _
  | cons _ step _ tail => exact .cons step tail

theorem of_core_steps (run : Steps profile ready dispatch before trace after)
    (coreOnly : ∀ label ∈ trace, label = .core) :
    CoreGrowthSteps profile ready dispatch before trace after ∧ after.host = before.host := by
  induction run with
  | refl => exact ⟨.refl _, rfl⟩
  | cons step _ tail =>
    have atCore := coreOnly _ (.head _)
    subst atCore
    obtain ⟨certified, hostEq⟩ := tail (fun label member => coreOnly label (.tail _ member))
    refine ⟨.cons ?_ step certified, hostEq.trans ?_⟩ <;> cases step
    · rename_i focused _ _ _
      simp [CoreUpdateGrows, focused]
    · rfl

theorem writeMemSt_grows (store : CStore (core3 grow)) (memory ptr : Nat) (bytes : ByteArray) :
    Core3.Grows store.core (writeMemSt memory ptr bytes store).core := by
  unfold writeMemSt
  split
  · rename_i wrote
    exact Core3.memWrite?_grows wrote
  · exact Core3.Grows.refl _

private theorem releaseLenders_core {E : CoreEngine} (store : CStore E) (lenders : List HandleObjId) :
    (lenders.foldl (fun current id => ArenaField.resHandles.modify current id
      fun handle => { handle with numLends := handle.numLends - 1 }) store).core = store.core := by
  induction lenders generalizing store with
  | nil => rfl
  | cons _ _ tail => exact tail _

private theorem deliverResolve_core {E : CoreEngine} (store : CStore E) (subtask : SubtaskId) :
    (store.deliverResolveSt subtask).core = store.core := by
  unfold CStore.deliverResolveSt
  split
  · rfl
  · exact releaseLenders_core _ _

private theorem takeWaitableEvent_core {E : CoreEngine} (store : CStore E) (waitable : Waitable) :
    (store.takeWaitableEventSt waitable).core = store.core := by
  cases waitable with
  | end_ endpoint =>
    simp only [CStore.takeWaitableEventSt, CStore.takeWaitableEvent]
    unfold takeEvent
    repeat' split
    all_goals first | rfl | (unfold deliver; split <;> rfl)
  | subtask subtask =>
    simp only [CStore.takeWaitableEventSt, CStore.takeWaitableEvent]
    repeat' split
    all_goals try rfl
    unfold CStore.subtaskEvent
    split
    · rfl
    · split <;> first | rfl | exact deliverResolve_core _ _

private theorem task_frame (base : CStore (core3 grow)) :
    Task.InvHyps (fun store : CStore (core3 grow) => Core3.Grows base.core store.core) := by
  constructor <;> intros
  all_goals try assumption
  case registerThread =>
    rename_i task thread store growth
    unfold CStore.registerThreadSt
    cases taskEntry : store.task? task with
    | none => exact growth
    | some info =>
      dsimp only
      split <;> exact growth
  case unregisterThread =>
    unfold CStore.unregisterThreadSt
    split <;> assumption

private theorem lift_frame (base : CStore (core3 grow)) :
    LiftHyps (fun store : CStore (core3 grow) => Core3.Grows base.core store.core) := by
  refine ⟨task_frame base, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · intro store inst index growth
      exact growth
    · intros; assumption
    · intros; assumption
  · constructor
    · intro memory ptr bytes store grows
      exact grows.trans (writeMemSt_grows store memory ptr bytes)
    · intro store handle growth
      exact growth
    · intro store inst entry growth
      exact growth
    all_goals intros; assumption
  all_goals try (intros; assumption)
  · intro waitable store grows
    simpa only [takeWaitableEvent_core] using grows

theorem realloc_local_grows (ready : HostReady Host) (host : HostImpl (core3 grow) Host)
    (base : CStore (core3 grow)) (context : LiftLowerContext (core3 grow))
    (old oldLen align newLen : Nat) :
    P.Inv (fun store => Core3.Grows base.core store.core)
      (specDispatch ready host (.reallocate context old oldLen align newLen)) :=
  P.Inv.reallocProg (lift_frame base) _ _ _ _ _ _ _

private theorem lower_frame (base : CStore (core3 grow)) :
    P.Inv.LowerPres (fun store : CStore (core3 grow) => Core3.Grows base.core store.core) := by
  have lift := lift_frame base
  refine ⟨lift.load, lift.store, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try (intros; assumption)
  · intro subtask store grows
    unfold LowerSt.releaseLendsSt
    split
    · exact grows
    · split
      · exact grows
      · rename_i lenders _
        change Core3.Grows base.core (lenders.foldl
          (fun current handle => ArenaField.resHandles.modify current handle fun owner =>
            { owner with numLends := owner.numLends - 1 }) store).core
        simpa only [releaseLenders_core] using grows
  · intro waitable event store grows
    cases waitable <;> exact grows
  · intro subtask store grows
    simpa only [deliverResolve_core] using grows
  · intro inst subtask index store grows
    unfold LowerSt.addSubtaskSt
    split <;> exact grows

theorem allocator_dispatch_growing (ready : HostReady Host) (host : HostImpl (core3 grow) Host)
    {call : Call (core3 grow)} (kind : AllocatorCall call) : CoreGrowing (specDispatch ready host call) := by
  intro base
  let initial : CStore (core3 grow) := { core := base }
  have frame := lift_frame initial
  cases kind with
  | realloc => exact realloc_local_grows ready host initial _ _ _ _ _
  | liftThread => exact P.Inv.liftThreadBody frame _ _ _ _
  | liftLoop => exact P.Inv.syncLiftLoopBody frame _ _
  | start caller =>
    change P.Inv _ (callerOnStart Limits.spec Quirks.none caller)
    unfold callerOnStart
    refine P.Inv.bind (P.Inv.getObj _ _) fun entry => ?_
    cases entry with
    | host =>
      dsimp only
      exact P.Inv.ite (P.Inv.bind (P.Inv.emit _) fun _ => P.Inv.pure _) (P.Inv.pure _)
    | lower => exact P.Inv.bind (P.Inv.lowerOnStart (lower_frame initial) _ _ _) fun _ => P.Inv.pure _
    | sub sub => cases sub <;> first | exact P.Inv.pure _ | exact P.Inv.onStartProg _
  | resolve caller results =>
    change P.Inv _ (callerOnResolve Limits.spec Quirks.none caller results)
    unfold callerOnResolve
    refine P.Inv.bind (P.Inv.getObj _ _) fun entry => ?_
    cases entry with
    | host =>
      dsimp only
      exact P.Inv.ite (P.Inv.bind (P.Inv.emit _) fun _ => P.Inv.pure _) (P.Inv.pure _)
    | lower => exact P.Inv.bind (P.Inv.lowerOnResolve (lower_frame initial) _ _ _ _) fun _ => P.Inv.pure _
    | sub sub =>
      cases sub <;> first
        | exact P.Inv.bind (P.Inv.modifyObj _ _ _ (fun _ growth => growth)) fun _ => P.Inv.pure _
        | exact P.Inv.onResolveProg frame _ _

theorem embedder_dispatch_growing (ready : HostReady Host) (host : HostImpl (core3 grow) Host)
    (name : String) (type : V1.FuncType) (args : List FlatValue)
    (embedder : CoreGrowing (host.embedder name type args)) :
    CoreGrowing (specDispatch ready host (.hostCallout (.embedder name type) args)) := by
  intro base
  change P.Inv _ (hostCalloutProg Limits.spec Quirks.none ready host (.embedder name type) args)
  unfold hostCalloutProg
  refine P.Inv.bind P.Inv.currentThread fun thread => P.Inv.bind P.Inv.getStore fun store => ?_
  split
  · exact P.Inv.trap _
  · unfold calloutBody
    dsimp only
    exact P.Inv.ite (P.Inv.bind (embedder base) fun _ => P.Inv.pure _)
      (P.Inv.bind (P.Inv.confine _ _) fun _ => P.Inv.pure _)

theorem grows (run : CoreGrowthSteps profile ready dispatch before trace after) :
    Core3.Grows before.store.core after.store.core := by
  induction run with
  | refl => exact .refl _
  | cons updates step _ tail => exact (step_grows step updates).trans tail

theorem append {middle : Config (core3 grow) Host} {suffix : List (Label (core3 grow) Host)}
    (prefixSteps : CoreGrowthSteps profile ready dispatch before trace middle)
    (suffixSteps : CoreGrowthSteps profile ready dispatch middle suffix after) :
    CoreGrowthSteps profile ready dispatch before (trace ++ suffix) after := by
  induction prefixSteps with
  | refl => exact suffixSteps
  | cons updates step _ tail => exact .cons updates step (tail suffixSteps)

theorem linked_region (run : CoreGrowthSteps profile ready dispatch before trace after)
    (context : LiftLowerContext (core3 grow)) {memory start length size : Nat} {width : AddrType}
    (linked : context.opts.memory = some memory)
    (present : (core3 grow).memAddrType? before.store.core memory = some width)
    (sized : (core3 grow).memSize? before.store.core memory = some size)
    (bounds : start + length ≤ size) :
    ptrTypeIn before.store context = width ∧ ptrTypeIn after.store context = width ∧
      ∃ reachedSize, (core3 grow).memSize? after.store.core memory = some reachedSize ∧
        size ≤ reachedSize ∧ start + length ≤ reachedSize := by
  have growth := grows run
  have reached := growth.memAddrType present
  obtain ⟨reachedSize, sized', larger⟩ := growth.memSize sized
  refine ⟨?_, ?_, reachedSize, sized', larger, bounds.trans larger⟩
  · simp [ptrTypeIn, CanonOpts.ptrType, linked, present]
  · change (core3 grow).memAddrType? after.store.core memory = some width at reached
    simp [ptrTypeIn, CanonOpts.ptrType, linked, reached]

open StepDefs

private theorem continuation {op : Op (core3 grow) Host}
    {next : (Eff (core3 grow) Host).Resp op → P (core3 grow) Host (Ret (core3 grow))}
    (growing : CoreGrowing (.op op next)) (result : (Eff (core3 grow) Host).Resp op) :
    CoreGrowing (next result) := by
  intro base
  cases growing base with
  | op _ tails => exact tails result

private theorem split_control {active : Activation (core3 grow) Host} {rest}
    (growing : before.CoreGrowing) (focused : before.ctl = active :: rest) :
    active.CoreGrowing ∧ ∀ other ∈ rest, Activation.CoreGrowing other :=
  List.forall_mem_cons.mp (focused ▸ growing.1)

private theorem change_focus {active next : Activation (core3 grow) Host} {rest}
    (growing : before.CoreGrowing) (focused : before.ctl = active :: rest)
    (update : active.CoreGrowing → next.CoreGrowing) (store : CStore (core3 grow)) :
    Config.CoreGrowing { before with store, ctl := next :: rest } :=
  ⟨List.forall_mem_cons.mpr ⟨update (split_control growing focused).1,
    (split_control growing focused).2⟩, growing.2⟩

private theorem after_op {thread segments op next}
    (growing : Activation.CoreGrowing (grow := grow) (Host := Host)
      ⟨thread, .prog (.op op next), segments⟩) (result : (Eff (core3 grow) Host).Resp op) :
    Activation.CoreGrowing ⟨thread, .prog (next result), segments⟩ :=
  ⟨continuation growing.1 result, growing.2⟩

private theorem set_saved
    (saved : ∀ thread active, before.cont? thread = some active → Activation.CoreGrowing active)
    {thread : ThreadId} {value : Option (Activation (core3 grow) Host)}
    (install : ∀ active, value = some active → Activation.CoreGrowing active) :
    ∀ target active, (before.setCont thread value).cont? target = some active → Activation.CoreGrowing active := by
  intro target active found
  by_cases equal : target = thread
  · subst target
    exact install _ (by simpa only [Config.cont?_setCont_self] using found)
  · exact saved _ _ (by simpa only [Machine.Config.cont?_setCont_ne _ _ _ _ equal] using found)

private theorem new_host (growing : before.CoreGrowing) {program : P (core3 grow) Host (Ret (core3 grow))}
    (certified : CoreGrowing program) : Config.CoreGrowing { before with ctl := [.ofProg none program] } :=
  ⟨List.forall_mem_cons.mpr ⟨⟨certified, fun _ absent => nomatch absent⟩,
    fun _ absent => nomatch absent⟩, growing.2⟩

private theorem invoke_growing (caller : CallId) (func : FuncId) (args : List Value.Val) :
    CoreGrowing (grow := grow) (Host := Host) (invokeProg caller func args) := fun _ =>
  P.Inv.bind (P.Inv.allocObj _ _ (fun _ growth => growth)) fun _ =>
    P.Inv.bind (P.Inv.modifyStore (fun _ growth => growth)) fun _ =>
    P.Inv.bind (P.Inv.callRet _) fun _ =>
    P.Inv.bind (P.Inv.modifyStore (fun _ growth => growth)) fun _ => P.Inv.pure _

private theorem tick_growing (ready : HostReady Host) : CoreGrowing (grow := grow) (tickProg ready) := by
  intro base
  unfold tickProg
  refine P.Inv.bind (P.Inv.modifyStore (fun _ growth => growth)) fun _ => ?_
  refine P.Inv.bind P.Inv.getStore fun _ => P.Inv.bind P.Inv.hostGet fun _ => ?_
  have leave : P.Inv (fun store => Core3.Grows base store.core)
      (modifyStore (E := core3 grow) (σ := Host) leaveHostSt >>= fun _ => pure (Ret.unit (E := core3 grow))) :=
    P.Inv.bind (P.Inv.modifyStore (fun _ growth => growth)) fun _ => P.Inv.pure _
  dsimp only
  split
  · exact leave
  · exact P.Inv.bind (P.Inv.pickTick _ _) fun thread =>
      P.Inv.bind (Thread.resume_inv thread (fun _ growth => growth)) fun _ => leave

private theorem cancel_growing (cancel : CancelRef) :
    CoreGrowing (grow := grow) (Host := Host) (cancelProg cancel) := fun _ =>
  P.Inv.bind (P.Inv.modifyStore (fun _ growth => growth)) fun _ =>
    P.Inv.bind (P.Inv.callRet _) fun _ =>
    P.Inv.bind (P.Inv.modifyStore (fun _ growth => growth)) fun _ => P.Inv.pure _

theorem control_growing (step : Step profile ready dispatch before label after)
    (growing : before.CoreGrowing) (install : CoreGrowthInstall dispatch before label) :
    after.CoreGrowing := by
  cases step with
  | popProg focused =>
    refine change_focus growing focused ?_ _
    exact fun current => ⟨current.2 _ List.mem_cons_self _, fun _ inside => current.2 _ (List.mem_cons_of_mem _ inside)⟩
  | popCore focused =>
    refine change_focus growing focused ?_ _
    exact fun current => ⟨current.2 _ List.mem_cons_self, fun _ inside => current.2 _ (List.mem_cons_of_mem _ inside)⟩
  | threadExit focused => exact ⟨(split_control growing focused).2, growing.2⟩
  | hostDone focused =>
    unfold hostFinish
    split <;> exact ⟨(split_control growing focused).2, growing.2⟩
  | call focused =>
    refine change_focus growing focused ?_ _
    intro current
    refine ⟨?_, List.forall_mem_cons.mpr ⟨continuation current.1, current.2⟩⟩
    simpa only [Focus.CoreGrowing, CoreGrowthInstall, focused] using install
  | callCore focused =>
    refine change_focus growing focused ?_ _
    exact fun current => ⟨continuation current.1, current.2⟩
  | coreInternal focused _ _ =>
    refine change_focus growing focused ?_ _
    exact fun current => current
  | coreReturned focused _ =>
    refine change_focus growing focused ?_ _
    exact fun current => ⟨current.1 _, current.2⟩
  | coreTrap _ _ => exact ⟨(fun _ absent => nomatch absent), growing.2⟩
  | coreCallout focused calling =>
    refine change_focus growing focused ?_ _
    intro current
    refine ⟨?_, List.forall_mem_cons.mpr ⟨current.1, current.2⟩⟩
    simpa only [Focus.CoreGrowing, CoreGrowthInstall, focused, calling] using install
  | get focused => exact change_focus growing focused (fun current => after_op current _) _
  | modify focused => exact change_focus growing focused (fun current => after_op current ()) _
  | trap _ => exact ⟨(fun _ absent => nomatch absent), growing.2⟩
  | choose result focused _ => exact change_focus growing focused (fun current => after_op current result) _
  | currentThread focused => exact change_focus growing focused (fun current => after_op current _) _
  | newThread focused _ =>
    obtain ⟨current, rest⟩ := split_control growing focused
    refine ⟨List.forall_mem_cons.mpr ⟨after_op current _, rest⟩, set_saved growing.2 ?_⟩
    intro active equal
    cases equal
    refine ⟨?_, fun _ absent => nomatch absent⟩
    simpa only [threadAct, Activation.ofProg, Focus.CoreGrowing, CoreGrowthInstall, focused] using install
  | block focused =>
    obtain ⟨current, rest⟩ := split_control growing focused
    exact ⟨rest, set_saved growing.2 (fun _ equal => Option.some.inj equal ▸ after_op current ())⟩
  | @blockSwitch thread _ _ _ _ _ focused found =>
    obtain ⟨current, rest⟩ := split_control growing focused
    have saved := set_saved growing.2 (thread := thread) (fun _ equal => Option.some.inj equal ▸ after_op current ())
    exact ⟨List.forall_mem_cons.mpr ⟨saved _ _ found, rest⟩, set_saved saved (fun _ absent => nomatch absent)⟩
  | resumeThread focused found =>
    obtain ⟨current, rest⟩ := split_control growing focused
    exact ⟨List.forall_mem_cons.mpr ⟨growing.2 _ _ found,
      List.forall_mem_cons.mpr ⟨after_op current (), rest⟩⟩, set_saved growing.2 (fun _ absent => nomatch absent)⟩
  | hostGet focused => exact change_focus growing focused (fun current => after_op current _) _
  | hostSet focused =>
    obtain ⟨current, rest⟩ := split_control growing focused
    exact ⟨List.forall_mem_cons.mpr ⟨after_op current (), rest⟩, growing.2⟩
  | emit focused =>
    obtain ⟨current, rest⟩ := split_control growing focused
    refine ⟨List.forall_mem_cons.mpr ⟨after_op current (), rest⟩, ?_⟩
    unfold observe
    split <;> exact growing.2
  | fault _ => exact ⟨(fun _ absent => nomatch absent), growing.2⟩
  | hostInvoke _ _ => exact new_host ⟨growing.1, growing.2⟩ (invoke_growing _ _ _)
  | hostTick _ => exact new_host growing (tick_growing ready)
  | hostCancel _ _ _ => exact new_host ⟨growing.1, growing.2⟩ (cancel_growing _)
  | hostRun _ => exact new_host growing (fun base => P.Inv.bind (install base) fun _ => P.Inv.pure _)

theorem control_update (growing : before.CoreGrowing) : CoreUpdateGrows before := by
  cases focused : before.ctl with
  | nil => simp [CoreUpdateGrows, focused]
  | cons active rest =>
    cases active with
    | mk thread focus segments =>
      cases focus with
      | core => simp [CoreUpdateGrows, focused]
      | prog program => exact update_of_inv program focused ((split_control growing focused).1.1 _)

theorem of_installs (run : Steps profile ready dispatch before trace after) (growing : before.CoreGrowing)
    (installs : ∀ {reached next leading label}, Steps profile ready dispatch before leading reached →
      Step profile ready dispatch reached label next → CoreGrowthInstall dispatch reached label) :
    CoreGrowthSteps profile ready dispatch before trace after ∧ after.CoreGrowing := by
  induction run with
  | refl => exact ⟨.refl _, growing⟩
  | cons step _ tail =>
    have install := installs (.refl _) step
    obtain ⟨steps, control⟩ := tail (control_growing step growing install) fun leading next =>
      installs (.cons step leading) next
    exact ⟨.cons (control_update growing) step steps, control⟩

theorem replace_core_focus {thread initial reached next segments rest}
    (growing : before.CoreGrowing)
    (focused : before.ctl = ⟨thread, .core initial next, segments⟩ :: rest)
    (updatedHost : Host) :
    Config.CoreGrowing { before with
      host := updatedHost
      ctl := ⟨thread, .core reached next, segments⟩ :: rest } := by
  obtain ⟨active, tail⟩ := split_control growing focused
  exact ⟨List.forall_mem_cons.mpr ⟨active, tail⟩, growing.2⟩

end Silmaril.Proofs.Wasm.Component.Reference.MachineCoreGrowth

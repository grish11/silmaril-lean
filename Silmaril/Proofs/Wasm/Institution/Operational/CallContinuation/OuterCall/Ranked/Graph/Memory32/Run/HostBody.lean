module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Host.Body.Defs
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Host.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Native.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.HostProofs

open Execution.Runtime (Callout EvalCtx Frame MemAddr MemInst Value)
open Computed
open Wasm.V1.Execution

theorem prefix_entry {fn : Function} {args stack : List Value} {ops : List Prefix.Op}
    {signature : Wasm.V1.FuncType} {tail : List Op} {fallthrough : List NumType}
    {labels : List (List NumType)} (parameters : args.map Value.type = fn.declaration.params)
    (checked : fn.checkHostPrefix (Prefix.stackTypes stack) ops signature tail fallthrough labels = true) :
    HostPrefixTyped fn (fn.declaration.frame args) stack ops signature tail fallthrough labels := by
  refine ⟨rfl, ?_, checked⟩
  simp [Declaration.frame, parameters, Value.zero, List.map_map, Function.comp_def]

theorem check_prefix_preserves {locals stack next : List Value} {op : Prefix.Op}
    {rest : List Prefix.Op} {signature : Wasm.V1.FuncType} {resume : List NumType → Bool}
    (checked : checkHostPrefixWith (locals.map Value.type) (Prefix.stackTypes stack) (op :: rest) signature resume = true)
    (move : Prefix.Reduce locals stack op (.values next)) :
    checkHostPrefixWith (locals.map Value.type) (Prefix.stackTypes next) rest signature resume = true := by
  simpa only [checkHostPrefixWith, Prefix.check, Prefix.checkOp_result move, Option.bind_some] using checked

theorem check_prefix_resume {locals : List NumType} {saved args : List Value}
    {signature : Wasm.V1.FuncType} {resume : List NumType → Bool}
    (checked : checkHostPrefixWith locals (Prefix.stackTypes (saved ++ args)) [] signature resume = true)
    (typed : args.map Value.type = signature.params) :
    resume (signature.results.reverse ++ Prefix.stackTypes saved) = true := by
  have count : (Prefix.stackTypes args).length = signature.params.length := by
    simpa [Prefix.stackTypes] using congrArg List.length typed
  have split : Prefix.stackTypes (saved ++ args) = Prefix.stackTypes args ++ Prefix.stackTypes saved := by
    simp [Prefix.stackTypes]
  simp only [checkHostPrefixWith, Prefix.check, Option.map_some, Option.getD_some, Bool.and_eq_true_iff,
    split, ← count, List.drop_left] at checked
  exact checked.2

theorem check_prefix_arguments {locals : List NumType} {stack : List Value}
    {signature : Wasm.V1.FuncType} {resume : List NumType → Bool}
    (checked : checkHostPrefixWith locals (Prefix.stackTypes stack) [] signature resume = true) :
    ∃ saved args, stack = saved ++ args ∧ args.map Value.type = signature.params ∧
      resume (signature.results.reverse ++ Prefix.stackTypes saved) = true := by
  have shape := checked
  simp only [checkHostPrefixWith, Prefix.check, Option.map_some, Option.getD_some,
    Bool.and_eq_true_iff, decide_eq_true_eq] at shape
  obtain ⟨saved, args, rfl, argTypes⟩ := Graph.SuffixTyped.split shape.1
  exact ⟨saved, args, rfl, argTypes, check_prefix_resume checked argTypes⟩

theorem prefix_preserves {fn : Function} {caller : Frame} {stack next : List Value}
    {op : Prefix.Op} {rest : List Prefix.Op} {signature : Wasm.V1.FuncType}
    {tail : List Op} {fallthrough : List NumType} {labels : List (List NumType)}
    (typed : HostPrefixTyped fn caller stack (op :: rest) signature tail fallthrough labels)
    (move : Prefix.Reduce caller.locals stack op (.values next)) :
    HostPrefixTyped fn caller next rest signature tail fallthrough labels := by
  refine ⟨typed.scope, typed.locals, ?_⟩
  unfold Function.checkHostPrefix
  rw [← typed.locals]
  exact check_prefix_preserves (by simpa only [Function.checkHostPrefix, typed.locals] using typed.code) move

theorem host_arguments {H : Type} {fn : Function} {caller : Frame} {stack : List Value}
    {site : HostCall.V1.Site H} {s : Store H} {tail : List Op}
    {fallthrough : List NumType} {labels : List (List NumType)}
    (typed : HostPrefixTyped fn caller stack [] site.signature tail fallthrough labels)
    (linked : fn.declaration.module.funcs[site.index.toNat]? = some site.address)
    (allocated : s.funcs[site.address.value]? = some (.host site.signature site.target))
    (scalar : site.signature.results.length ≤ 1) :
    ∃ saved args, stack = saved ++ args ∧ site.Checked s caller args ∧
      ∀ payload : List Value, payload.map Value.type = site.signature.results →
        fn.checkRegion (Prefix.stackTypes (saved ++ payload)) fallthrough tail labels = true := by
  have check := typed.code
  unfold Function.checkHostPrefix at check
  obtain ⟨saved, args, rfl, argTypes, resume⟩ := check_prefix_arguments check
  refine ⟨saved, args, rfl, ⟨typed.scope ▸ linked, allocated, argTypes, scalar⟩, ?_⟩
  intro payload payloadTypes
  simpa [Prefix.stackTypes, payloadTypes] using resume

theorem prefix_step_iff {H : Type} {host : HostSemantics H} {s : Store H} {caller : Frame}
    {stack : List Value} {op : Prefix.Op} {tail : List Admin} {dst : Config H} :
    Step host ⟨s, caller, values stack ++ Prefix.emit v1Syntax op :: tail⟩ dst ↔
      ∃ out, Prefix.Reduce caller.locals stack op out ∧
        dst = ⟨s, caller, Prefix.outcomeCode values .trap tail out⟩ := by
  rw [Step.internal_iff_of_not_callout]
  · exact Prefix.v1_step_iff
  · intro call atHead
    have found := exists_callout_iff.mp ⟨call, atHead⟩
    cases op <;> simp [decompose?, Prefix.emit, v1Syntax, asValue?] at found

private def inContext {H : Type} (k : EvalCtx Wasm.V1.Instr) (outer : Frame)
    (cfg : Config H) : Config H :=
  ⟨cfg.store, outer, k.plug value cfg.code⟩

private def inContextCallout {H : Type} (site : HostCall.V1.Site H) (k : EvalCtx Wasm.V1.Instr)
    (saved args : List Value) (tail : List Admin) : Callout H Wasm.V1.Instr :=
  ⟨k.comp (.seq saved .hole tail), site.address, site.signature, site.target, args⟩

theorem host_pending_step_iff {H : Type} {host : HostSemantics H} {site : HostCall.V1.Site H}
    {s : Store H} {outer : Frame} {k : EvalCtx Wasm.V1.Instr} {saved args : List Value}
    {tail : List Admin} {dst : Config H} (checked : site.Checked s (k.activeFrame outer) args) :
    Step host ⟨s, outer, k.plug value (site.pending s (k.activeFrame outer) saved args tail).code⟩ dst ↔
      (∃ s' r, host site.target s args (.returned s' r) ∧
        dst = ⟨s', outer, k.plug value (HostCall.V1.resumed s' (k.activeFrame outer) saved tail r).code⟩) ∨
      (host site.target s args .diverged ∧
        dst = ⟨s, outer, k.plug value (site.pending s (k.activeFrame outer) saved args tail).code⟩) := by
  have atHead : CalloutAt (inContext k outer (site.pending s (k.activeFrame outer) saved args tail))
      (inContextCallout site k saved args tail) := by
    refine ⟨?_, checked.allocated, ?_⟩
    · simp [inContext, inContextCallout, Callout.fill, Callout.redex, EvalCtx.plug_comp, EvalCtx.plug,
        HostCall.V1.Site.pending, coding, values, List.append_assoc]
    · simpa [inContextCallout] using congrArg List.length checked.arguments
  simpa [inContext, inContextCallout, resume, Callout.fill, EvalCtx.plug_comp, EvalCtx.plug,
    HostCall.V1.Site.pending, HostCall.V1.resumed, coding, values, List.append_assoc] using
    (atHead.step_iff (host := host) (b := dst)).trans Answer.iff

private theorem no_host_callout {H : Type} {mode : MemoryMode} {program : Program}
    {memory : MemAddr} {calls : CallMode} {s : Store H} {initial : MemInst}
    (layout : Layout program s memory initial) (call : Callout H Wasm.V1.Instr)
    (allocated : s.funcs[call.function.value]? = some (.host call.type call.host))
    {rank : Nat} {callerModule : Execution.Runtime.ModuleInst} :
    ¬ CodeAllowedFor mode program memory calls rank callerModule
      (call.context.plug value (call.redex coding)) := by
  generalize call.context = k
  induction k generalizing rank callerModule with
  | hole =>
    intro allowed
    have invoked := allowed (.invoke call.function) (by simp [EvalCtx.plug, Callout.redex])
    cases invoked with
    | invoke found _ => simp [layout.functions _ _ found] at allocated
  | seq vs k tail ih =>
    exact fun allowed => ih (fun x hx => allowed x (by simp [EvalCtx.plug, hx]))
  | label n cont k ih =>
    intro allowed
    have within := allowed (.label n cont (k.plug value (call.redex coding))) (by simp [EvalCtx.plug])
    cases within with
    | label _ inside => exact ih inside
    | loopLabel _ inside => exact ih inside
  | frame n f k ih =>
    intro allowed
    have within := allowed (.frame n f (k.plug value (call.redex coding))) (by simp [EvalCtx.plug])
    cases within with
    | frame _ _ _ _ inside => exact ih inside
    | enteredFrame _ _ inside => exact ih inside

theorem ready_internal_iff {H : Type} {host : HostSemantics H} {mode : MemoryMode}
    {program : Program} {memory : MemAddr} {calls : CallMode} {base : Store H}
    {initial : MemInst} (layout : Layout program base memory initial) {state : State} {rank : Nat}
    (ready : ReadyFor mode program memory calls rank initial.data.size state) {dst : Config H} :
    Step host (render base memory initial state) dst ↔
      Internal (render base memory initial state) dst := by
  apply Step.internal_iff_of_not_callout
  intro call located
  have prohibited := no_host_callout (layout.with_bytes state.bytes) call located.found
    (rank := rank) (callerModule := state.frame.module) (mode := mode) (calls := calls)
  apply prohibited
  intro x hx
  apply ready.2
  have code := located.plugged
  change state.code = call.context.plug value (call.redex coding) at code
  exact code ▸ hx

theorem ready_run_iff {H : Type} {host : HostSemantics H} {mode : MemoryMode} {calls : CallMode}
    {program : Program} {memory : MemAddr} {base : Store H} {initial : MemInst}
    (checked : program.checkV1 memory mode calls = true) (layout : Layout program base memory initial)
    (matched : mode.matches initial) {src : State} {rank : Nat}
    (ready : ReadyFor mode program memory calls rank initial.data.size src) {dst : Config H} :
    Steps host (render base memory initial src) dst ↔
      ∃ out, RunsAt mode program memory src out ∧ ReadyFor mode program memory calls rank initial.data.size out ∧
        dst = render base memory initial out := by
  constructor
  · intro run
    generalize first : render base memory initial src = start at run
    induction run using Relation.ReflTransGen.head_induction_on generalizing src with
    | refl => exact ⟨src, .refl, ready, first.symm⟩
    | head step rest ih =>
      rw [← first] at step
      have internal := (ready_internal_iff layout ready).mp step
      obtain ⟨next, moved, nextReady, eq⟩ := (v1_step_iff_at checked layout matched ready).mp internal
      obtain ⟨out, ran, outReady, rendered⟩ := ih nextReady eq.symm
      exact ⟨out, ran.head moved, outReady, rendered⟩
  · intro run
    exact Steps.of_internal ((v1_run_iff_at checked layout matched ready).mpr run)

theorem host_pending_run_iff {H : Type} {host : HostSemantics H} {site : HostCall.V1.Site H}
    {s : Store H} {outer : Frame} {k : EvalCtx Wasm.V1.Instr} {saved args : List Value}
    {tail : List Admin} {dst : Config H} (checked : site.Checked s (k.activeFrame outer) args)
    {mode : MemoryMode} {memory : MemAddr} {initial : MemInst}
    (contract : site.ReturnContract host (HostStoreEffect mode memory initial) s args) :
    let pending : Config H := ⟨s, outer, k.plug value (site.pending s (k.activeFrame outer) saved args tail).code⟩
    Steps host pending dst ↔ dst = pending ∨
      ∃ s' r, host site.target s args (.returned s' r) ∧
        HostCall.V1.ResultTyped site.signature.results r ∧ HostStoreEffect mode memory initial s s' ∧
        Steps host ⟨s', outer, k.plug value (HostCall.V1.resumed s' (k.activeFrame outer) saved tail r).code⟩ dst := by
  dsimp only
  constructor
  · intro run
    generalize eq : (⟨s, outer, k.plug value (site.pending s (k.activeFrame outer) saved args tail).code⟩ :
      Config H) = first at run
    induction run using Relation.ReflTransGen.head_induction_on with
    | refl => exact .inl rfl
    | head step rest ih =>
      rw [← eq] at step
      rcases (host_pending_step_iff checked).mp step with ⟨s', r, returned, rfl⟩ | ⟨_, again⟩
      · obtain ⟨typed, effect⟩ := contract s' r returned
        exact .inr ⟨s', r, returned, typed, effect, rest⟩
      · rw [← eq, ← again]
        exact ih again.symm
  · rintro (rfl | ⟨s', r, returned, _, _, rest⟩)
    · exact .refl
    · exact rest.head ((host_pending_step_iff checked).mpr (.inl ⟨s', r, returned, rfl⟩))

theorem host_graph_run_iff {H : Type} {host : HostSemantics H} {site : HostCall.V1.Site H}
    {mode : MemoryMode} {calls : CallMode} {program : Program} {memory : MemAddr}
    {base : Store H} {initial : MemInst} {bytes : ByteArray}
    (checked : program.checkV1 memory mode calls = true) (layout : Layout program base memory initial)
    (matched : mode.matches initial) (extent : mode.extent initial.data.size bytes)
    {k : EvalCtx Wasm.V1.Instr} {outer : Frame} {saved args : List Value} {tail : List Admin}
    {rank outerRank : Nat}
    (siteChecked : site.Checked (storeWithBytes base memory initial bytes) (k.activeFrame outer) args)
    (contract : site.ReturnContract host (HostStoreEffect mode memory initial)
      (storeWithBytes base memory initial bytes) args)
    (tailAllowed : CodeAllowedFor mode program memory calls rank (k.activeFrame outer).module tail)
    (wrap : ∀ code, CodeAllowedFor mode program memory calls rank (k.activeFrame outer).module code →
      CodeAllowedFor mode program memory calls outerRank outer.module (k.plug value code))
    {dst : Config H} :
    let live := storeWithBytes base memory initial bytes
    let pending : Config H := ⟨live, outer, k.plug value (site.pending live (k.activeFrame outer) saved args tail).code⟩
    Steps host pending dst ↔ dst = pending ∨
      ∃ s' r next out, host site.target live args (.returned s' r) ∧
        HostCall.V1.ResultTyped site.signature.results r ∧
        s' = storeWithBytes base memory initial next ∧ bytes.size ≤ next.size ∧
        ReadyFor mode program memory calls outerRank initial.data.size
          ⟨next, outer, k.plug value (values saved ++ result r ++ tail)⟩ ∧
        RunsAt mode program memory ⟨next, outer, k.plug value (values saved ++ result r ++ tail)⟩ out ∧
        ReadyFor mode program memory calls outerRank initial.data.size out ∧ dst = render base memory initial out := by
  dsimp only
  have boundary := host_pending_run_iff (saved := saved) (tail := tail) (dst := dst) siteChecked contract
  dsimp only at boundary
  rw [boundary]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨s', r, returned, _, _, run⟩
    obtain ⟨next, typed, mono, _, ready, rendered⟩ := layout.host_return extent contract returned tailAllowed
      (saved := saved)
    have eq : s' = storeWithBytes base memory initial next := congrArg (fun cfg : Config H => cfg.store) rendered
    have outerReady : ReadyFor mode program memory calls outerRank initial.data.size
        ⟨next, outer, k.plug value (values saved ++ result r ++ tail)⟩ :=
      ⟨ready.1, wrap _ ready.2⟩
    have resumed : (⟨s', outer, k.plug value (HostCall.V1.resumed s' (k.activeFrame outer) saved tail r).code⟩ :
        Config H) = render base memory initial ⟨next, outer, k.plug value (values saved ++ result r ++ tail)⟩ := by
      rw [eq]
      rfl
    rw [resumed] at run
    obtain ⟨out, edges, finalReady, final⟩ := (ready_run_iff checked layout matched outerReady).mp run
    exact ⟨s', r, next, out, returned, typed, eq, mono, outerReady, edges, finalReady, final⟩
  · rintro ⟨s', r, next, out, returned, typed, eq, _, outerReady, edges, finalReady, final⟩
    obtain ⟨_, effect⟩ := contract s' r returned
    refine ⟨s', r, returned, typed, effect, ?_⟩
    rw [eq]
    exact (ready_run_iff checked layout matched outerReady).mpr ⟨out, edges, finalReady, final⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.HostProofs

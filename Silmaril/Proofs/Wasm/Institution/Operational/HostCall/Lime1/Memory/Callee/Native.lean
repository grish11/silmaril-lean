module

public import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Memory.Callee.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.HostCall.Lime1.Memory.Callee.Preservation
import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Memory.Thms
import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Thms
import Silmaril.Wasm.Institution.Operational.MemoryWrite.Native.Lime1Context.Thms
import Silmaril.Wasm.Institution.Operational.MemoryQuery.Thms
import Silmaril.Wasm.Institution.Operational.MemoryGrow.Native.Thms
import Silmaril.Wasm.Institution.Operational.MemoryWrite.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.Native.Thms
import Silmaril.Wasm.Institution.Operational.Blocks.Context.Thms
import Silmaril.Wasm.Institution.Operational.BranchExit.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Native.Thms
import Silmaril.Wasm.Lime1.Execution.Callout.Properties

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.HostCall.Lime1.MemoryCallee.Proofs

open Execution.Runtime (EvalCtx Frame FuncInst Result Value)
open Wasm.Lime1.Execution
open CallContinuation
open CallContinuation.OuterCall (CallTarget Declaration)
open CallContinuation.OuterCall.Ranked
open CallContinuation.OuterCall.Computed

set_option backward.isDefEq.respectTransparency false

variable {H : Type} {base : Store H} {mem : Memory32 base} {host : HostSemantics H} {callee : MemoryTarget} {site : IndirectSite}
  {caller : Frame} {saved : List Value} {tail : List Admin} {bytes : ByteArray} {dst : Config H}
  {arity : Nat} {types : List NumType} {labels : List (List NumType)}

local notation "resultCount" => arity
local notation "cfg" => configAt mem caller saved tail callee arity
local notation "regionCfg" => configAt mem caller saved tail callee types.length

@[simp] private theorem code_nil : code [] = [] := rfl

@[simp] private theorem code_cons (op : Graph.Memory32.Op) (ops : List Graph.Memory32.Op) :
    code (op :: ops) = .source op.v1.toLime :: code ops := rfl

private theorem enter_iff {args : List Value} (allocated : callee.Allocated base)
    (typed : args.map Value.type = callee.fn.declaration.params) :
    Step CallFrame.limeNoHost (config mem caller saved tail callee bytes (.invoke args)) dst ↔ dst = config mem caller saved tail callee bytes (.body args callee.fn.initial callee.fn.code) := by
  have count : args.length = callee.fn.declaration.params.length := by simpa using congrArg List.length typed
  have exactInvoke {mid : Config H} :=
    CallFrame.lime_invoke_wasm_prefix_iff (s := mem.store bytes) (caller := caller)
      (saved := saved) (args := args) (dst := mid) allocated count
  have body : expression callee.code.body = values callee.fn.initial ++ code callee.fn.code := by
    have literal (v : Value) :
        (Execution.Runtime.AdminInstr.source (Graph.v1CodeSyntax.ops.value v).toLime : Admin) = value v := by
      rcases v with ⟨type, bits⟩
      cases type <;> rfl
    simp [MemoryTarget.code, Graph.Memory32.Function.v1Func, Wasm.V1.Func.toLime,
      Wasm.V1.Expr.toLime_eq_map, expression, values, code, List.map_map, Function.comp_def, literal]
  constructor
  · intro move
    obtain ⟨mid, invoked, rfl⟩ := CallContinuation.lime_invoke_strip_suffix
      (stack := saved ++ args) (rest := tail) (a := callee.address)
      (by simpa only [configAt, renderUnder, frameCode, values_append, List.append_assoc, List.singleton_append] using move)
    obtain rfl := exactInvoke.mp invoked
    simp [configAt, renderUnder, frameCode, Declaration.frame, Declaration.type, MemoryTarget.code, Graph.Memory32.Function.v1Func, Wasm.V1.Func.toLime, ← body]
  · rintro rfl
    have step := exactInvoke.mpr rfl
    have locals : callee.code.locals = callee.fn.declaration.locals := rfl
    rw [body, locals] at step
    simpa [configAt, renderUnder, frameCode, values, List.append_assoc, Declaration.frame, Declaration.type] using
      Step.context step [] tail

private theorem body_iff {args : List Value} {body : List Admin}
    (stays : ∀ out, ¬ PureStep callee.fn.declaration.module.types [.label resultCount [] body] out) :
    Step CallFrame.limeNoHost ⟨mem.store bytes, caller, MemoryWrite.limeActivationCode resultCount (callee.fn.declaration.frame args) saved tail body⟩ dst ↔
      ∃ mid, Step CallFrame.limeNoHost ⟨mem.store bytes, callee.fn.declaration.frame args, body⟩ mid ∧
        dst = ⟨mid.store, caller, MemoryWrite.limeActivationCode resultCount mid.frame saved tail mid.code⟩ := by
  constructor
  · intro move
    obtain ⟨mid, step, rfl⟩ := CallContinuation.lime_frame_context_inv move
    rcases lime_body_step_cases step with ⟨next, inside, rfl⟩ | ⟨out, pop, _⟩
    · exact ⟨next, inside, by simp [MemoryWrite.limeActivationCode, List.append_assoc]⟩
    · exact (stays out pop).elim
  · rintro ⟨mid, step, rfl⟩
    simpa only [MemoryWrite.limeActivationCode, List.append_assoc, List.singleton_append] using
      Step.context (Step.frame (Step.label step resultCount []) resultCount caller) saved tail

private theorem leave_label_iff {args : List Value} {out : Result} :
    Step CallFrame.limeNoHost ⟨mem.store bytes, caller, MemoryWrite.limeActivationCode resultCount (callee.fn.declaration.frame args) saved tail (result out)⟩ dst ↔
      dst = cfg bytes (.exit args out) := by
  constructor
  · intro move
    obtain ⟨mid, step, rfl⟩ := CallContinuation.lime_frame_context_inv move
    rcases lime_body_step_cases step with ⟨_, inside, _⟩ | ⟨after, pop, rfl⟩
    · cases out with
      | values vs => exact (Nested.lime_result_stuck (r := .values vs) inside).elim
      | trap => exact (Nested.lime_result_stuck (r := .trap) inside).elim
    · cases out with
      | values vs => rw [Nested.lime_label_result (r := .values vs) pop]; rfl
      | trap => rw [Nested.lime_label_result (r := .trap) pop]; rfl
  · rintro rfl
    cases out with
    | values vs =>
      simpa only [configAt, renderUnder, frameCode, result, MemoryWrite.limeActivationCode, List.append_assoc, List.singleton_append] using
        Step.context (Step.frame (Step.pure (host := CallFrame.limeNoHost) (mem.store bytes)
          (callee.fn.declaration.frame args) (.labelDone resultCount [] vs)) resultCount caller) saved tail
    | trap =>
      simpa only [configAt, renderUnder, frameCode, result, MemoryWrite.limeActivationCode, List.append_assoc, List.singleton_append] using
        Step.context (Step.frame (Step.pure (host := CallFrame.limeNoHost) (mem.store bytes)
          (callee.fn.declaration.frame args) (.labelTrap resultCount [])) resultCount caller) saved tail

private theorem leave_frame_iff {args : List Value} {out : Result}
    (countEq : arity = types.length) (typed : resultTyped types out) :
    Step CallFrame.limeNoHost (cfg bytes (.exit args out)) dst ↔ dst = cfg bytes (.done out) := by
  constructor
  · intro move
    obtain ⟨mid, step, rfl⟩ := CallContinuation.lime_frame_context_inv
      (by simpa only [configAt, renderUnder, frameCode, List.append_assoc, List.singleton_append] using move)
    cases out with
    | values vs => obtain rfl := Nested.lime_frame_result (r := .values vs) step; rfl
    | trap => obtain rfl := Nested.lime_frame_result (r := .trap) step; rfl
  · rintro rfl
    cases out with
    | values vs =>
      have count : vs.length = resultCount := by simpa [countEq] using congrArg List.length typed
      exact Step.context (.pure _ _ (.frameDone resultCount (callee.fn.declaration.frame args) vs count)) saved tail
    | trap => exact Step.context (.pure _ _ (.frameTrap resultCount (callee.fn.declaration.frame args))) saved tail

private theorem get_iff {args stack : List Value} {index : LocalIdx} {ops : List Graph.Memory32.Op}
    {v : Value} (found : (callee.fn.declaration.frame args).locals[index.toNat]? = some v) :
    Step CallFrame.limeNoHost (cfg bytes (.body args stack (.ranked (.numeric (.get index)) :: ops))) dst ↔
      dst = cfg bytes (.body args (stack ++ [v]) ops) := by
  rw [show cfg bytes (.body args stack (.ranked (.numeric (.get index)) :: ops)) =
      ⟨mem.store bytes, caller, MemoryWrite.limeActivationCode resultCount (callee.fn.declaration.frame args)
        saved tail (values stack ++ .source (.localGet index) :: code ops)⟩ from by
    simp only [configAt, renderUnder, frameCode, code_cons, MemoryWrite.limeActivationCode, List.append_assoc, List.singleton_append]
    rfl]
  rw [body_iff (fun _ => lime_label_stays rfl (by simp) (by simp) (by simp))]
  constructor
  · rintro ⟨mid, step, rfl⟩
    obtain rfl := (lime_local_get_iff found).mp step
    simp [configAt, renderUnder, frameCode, MemoryWrite.limeActivationCode, values, List.append_assoc]
  · rintro rfl
    exact ⟨_, (lime_local_get_iff found).mpr rfl, by
      simp [configAt, renderUnder, frameCode, MemoryWrite.limeActivationCode, values, List.append_assoc]⟩

private theorem load_iff {args stack : List Value} {offset : Fin (2 ^ 32)} {ptr : BitVec 32}
    {ops : List Graph.Memory32.Op} (checked : callee.Checked mem) :
    Step CallFrame.limeNoHost (cfg bytes (.body args (stack ++ [Value.int .i32 ptr]) (.load offset :: ops))) dst ↔
      (∃ bits, MemoryQuery.EdgeAt bytes offset.val (.load ptr) (.value bits) ∧
        dst = cfg bytes (.body args (stack ++ [Value.int .i32 bits]) ops)) ∨
      (MemoryQuery.EdgeAt bytes offset.val (.load ptr) .trap ∧ dst = cfg bytes (.trapped args stack (code ops))) := by
  let arg := Graph.Memory32.immediate offset
  have slot := mem.frameMemory_store (bytes := bytes) (active := callee.fn.declaration.frame args) checked.slot
  have access := MemoryWrite.lime_activation_load_step_iff_at
    (host := CallFrame.limeNoHost) (caller := caller) (arity := resultCount) (callerSaved := saved)
    (callerTail := tail) (saved := stack) (tail := code ops) (immediate := arg) (ptr := ptr) (dst := dst) slot
  rw [show cfg bytes (.body args (stack ++ [Value.int .i32 ptr]) (.load offset :: ops)) =
      ⟨mem.store bytes, caller, MemoryWrite.limeActivationCode resultCount (callee.fn.declaration.frame args)
        saved tail (values stack ++ MemoryQuery.limeCodeAt arg (.load ptr) ++ code ops)⟩ from by
    simp only [configAt, renderUnder, frameCode, code_cons, MemoryWrite.limeActivationCode, MemoryQuery.limeCodeAt,
      values_append, List.append_assoc, List.singleton_append]
    rfl]
  rw [access]
  constructor
  · rintro ⟨out, edge, rfl⟩
    cases out with
    | value bits =>
      exact .inl ⟨bits, edge, by
        simp [configAt, renderUnder, frameCode, values, MemoryWrite.limeActivationCode, MemoryQuery.limeCodeAt,
          value, Value.int, List.append_assoc]⟩
    | trap =>
      exact .inr ⟨edge, by simp [configAt, renderUnder, frameCode, MemoryWrite.limeActivationCode, MemoryQuery.limeCodeAt,
        List.append_assoc]⟩
    | size | load => cases MemoryQuery.invert_at edge
  · rintro (⟨bits, edge, rfl⟩ | ⟨edge, rfl⟩)
    · exact ⟨.value bits, edge, by simp [configAt, renderUnder, frameCode, MemoryWrite.limeActivationCode,
        MemoryQuery.limeCodeAt, values, value, Value.int, List.append_assoc]⟩
    · exact ⟨.trap, edge, by simp [configAt, renderUnder, frameCode, MemoryWrite.limeActivationCode, MemoryQuery.limeCodeAt,
        List.append_assoc]⟩

private theorem store_iff {args stack : List Value} {offset : Fin (2 ^ 32)} {ptr word : BitVec 32}
    {ops : List Graph.Memory32.Op} (checked : callee.Checked mem) (live : mem.Live bytes) :
    Step CallFrame.limeNoHost (cfg bytes (.body args (stack ++ [Value.int .i32 ptr, Value.int .i32 word]) (.store offset :: ops))) dst ↔
      (∃ written, MemoryWrite.EdgeAt bytes offset.val (.store ptr word) (.written written) ∧ mem.Live written ∧
        dst = cfg written (.body args stack ops)) ∨
      (MemoryWrite.EdgeAt bytes offset.val (.store ptr word) .trap ∧
        dst = cfg bytes (.trapped args stack (code ops))) := by
  let arg := Graph.Memory32.immediate offset
  have access := mem.activation_store_iff_at
    (bytes := bytes) (host := CallFrame.limeNoHost) (caller := caller) (callee := callee.fn.declaration.frame args)
    (arity := resultCount) (callerSaved := saved) (callerTail := tail) (saved := stack) (tail := code ops)
    (arg := arg) (ptr := ptr) (word := word) (dst := dst) checked.slot live
  simpa [configAt, renderUnder, frameCode, Graph.Memory32.Op.v1, Wasm.V1.Instr.toLime, MemoryWrite.limeActivationCode,
    MemoryWrite.limeConfigAt, value, Value.int, values, List.append_assoc, arg, Graph.Memory32.immediate] using access

private theorem size_iff {args stack : List Value} {ops : List Graph.Memory32.Op}
    (checked : callee.Checked mem) :
    Step CallFrame.limeNoHost (cfg bytes (.body args stack (.size :: ops))) dst ↔
      dst = cfg bytes (.body args (stack ++ [pages bytes]) ops) := by
  rw [show cfg bytes (.body args stack (.size :: ops)) =
      ⟨mem.store bytes, caller, MemoryWrite.limeActivationCode resultCount (callee.fn.declaration.frame args)
        saved tail (values stack ++ .source .memorySize :: code ops)⟩ from by
    simp only [configAt, renderUnder, frameCode, code_cons, MemoryWrite.limeActivationCode, List.append_assoc, List.singleton_append]
    rfl]
  rw [body_iff (fun _ => lime_label_stays rfl (by simp) (by simp) (by simp))]
  have slot := mem.frameMemory_store (bytes := bytes) (active := callee.fn.declaration.frame args) checked.slot
  constructor
  · rintro ⟨mid, step, rfl⟩
    obtain ⟨head, size, rfl⟩ := CallContinuation.lime_memorySize_strip step
    obtain ⟨out, edge, rfl⟩ := (MemoryQuery.lime_step_iff_at MemoryQuery.arg slot (query := .size)).mp size
    cases MemoryQuery.invert edge
    simp [configAt, renderUnder, frameCode, MemoryWrite.limeActivationCode, MemoryQuery.limeConfigAt,
      MemoryQuery.limeCodeAt, pages, values, value, Value.int, List.append_assoc]
  · rintro rfl
    have size := MemoryQuery.lime_sound (host := CallFrame.limeNoHost) slot (MemoryQuery.fact .size)
    refine ⟨⟨mem.store bytes, callee.fn.declaration.frame args, values (stack ++ [pages bytes]) ++ code ops⟩,
      ?_, by simp only [configAt, renderUnder, frameCode, MemoryWrite.limeActivationCode, List.append_assoc, List.singleton_append]⟩
    simpa [MemoryQuery.limeConfigAt, MemoryQuery.limeCodeAt, pages, values, value, Value.int, List.append_assoc] using
      Step.context size stack (code ops)

private theorem grow_iff {args stack : List Value} {delta : BitVec 32} {ops : List Graph.Memory32.Op}
    (checked : callee.Checked mem) :
    Step CallFrame.limeNoHost (cfg bytes (.body args (stack ++ [Value.int .i32 delta]) (.grow :: ops))) dst ↔
      (∃ grown, MemoryGrow.Edge (mem.current bytes) (.request delta) (.grown grown) ∧
        dst = cfg grown (.body args (stack ++ [pages bytes]) ops)) ∨
      dst = cfg bytes (.body args (stack ++ [Value.int .i32 (-1)]) ops) := by
  rw [show cfg bytes (.body args (stack ++ [Value.int .i32 delta]) (.grow :: ops)) =
      ⟨mem.store bytes, caller, MemoryWrite.limeActivationCode resultCount (callee.fn.declaration.frame args)
        saved tail (values (stack ++ [Value.int .i32 delta]) ++ .source .memoryGrow :: code ops)⟩ from by
    simp only [configAt, renderUnder, frameCode, code_cons, MemoryWrite.limeActivationCode, List.append_assoc, List.singleton_append]
    rfl]
  rw [body_iff (fun _ => lime_label_stays rfl (by simp) (by simp) (by simp))]
  have slot : frameMemory (mem.store bytes) (callee.fn.declaration.frame args) =
      some (mem.address, mem.current bytes) := mem.frameMemory_store checked.slot
  have storeAgain (grown : ByteArray) :
      setMemory (mem.store bytes) mem.address (mem.current grown) = mem.store grown := by
    simp [Memory32.store, setMemory, List.set_set]
  constructor
  · rintro ⟨mid, step, rfl⟩
    obtain ⟨head, grow, rfl⟩ := CallContinuation.lime_memoryGrow_strip step
    obtain ⟨out, edge, rfl⟩ := (MemoryGrow.lime_step_iff slot (q := .request delta)).mp grow
    cases out with
    | request => cases MemoryGrow.invert edge
    | grown grown =>
      refine .inl ⟨grown, edge, ?_⟩
      simp [configAt, renderUnder, frameCode, MemoryWrite.limeActivationCode, MemoryGrow.limeConfig,
        Memory32.current, pages, values, value, Value.int, List.append_assoc]
      simpa only [Memory32.current] using storeAgain grown
    | failed =>
      exact .inr (by simp [configAt, renderUnder, frameCode, MemoryWrite.limeActivationCode, MemoryGrow.limeConfig,
        values, value, Value.int, List.append_assoc])
  · rintro (⟨grown, edge, rfl⟩ | rfl)
    · have grow := MemoryGrow.lime_sound (host := CallFrame.limeNoHost) slot edge
      refine ⟨⟨mem.store grown, callee.fn.declaration.frame args, values (stack ++ [pages bytes]) ++ code ops⟩,
        ?_, by simp only [configAt, renderUnder, frameCode, MemoryWrite.limeActivationCode, List.append_assoc, List.singleton_append]⟩
      simpa [MemoryGrow.limeConfig, Memory32.current, pages, values, value, Value.int, List.append_assoc,
        show setMemory (mem.store bytes) mem.address { mem.initial with data := grown } = mem.store grown
          from storeAgain grown] using Step.context grow stack (code ops)
    · have grow := MemoryGrow.lime_sound (host := CallFrame.limeNoHost) slot (MemoryGrow.fact (.fail delta))
      refine ⟨⟨mem.store bytes, callee.fn.declaration.frame args,
        values (stack ++ [Value.int .i32 (-1)]) ++ code ops⟩, ?_,
        by simp only [configAt, renderUnder, frameCode, MemoryWrite.limeActivationCode, List.append_assoc, List.singleton_append]⟩
      simpa [MemoryGrow.limeConfig, values, value, Value.int, List.append_assoc] using
        Step.context grow stack (code ops)

private theorem erase_iff {args stack : List Value} {rest : List Admin} (active : stack ≠ [] ∨ rest ≠ []) :
    Step CallFrame.limeNoHost (cfg bytes (.trapped args stack rest)) dst ↔
      ∃ kept removed cut after, stack = kept ++ removed ∧ rest = cut ++ after ∧
        (removed ≠ [] ∨ cut ≠ []) ∧ dst = cfg bytes (.trapped args kept after) := by
  rw [show cfg bytes (.trapped args stack rest) =
      ⟨mem.store bytes, caller, MemoryWrite.limeActivationCode resultCount (callee.fn.declaration.frame args)
        saved tail (values stack ++ .trap :: rest)⟩ from by
    simp [configAt, renderUnder, frameCode, MemoryWrite.limeActivationCode, List.append_assoc]]
  rw [body_iff (fun _ => lime_label_stays rfl (by simp) (by simp) (fun _ => active))]
  constructor
  · rintro ⟨mid, step, rfl⟩
    obtain ⟨kept, removed, cut, after, split, suffix, nonempty, rfl⟩ := lime_trap_front_iff.mp step
    exact ⟨kept, removed, cut, after, split, suffix, nonempty,
      by simp [configAt, renderUnder, frameCode, MemoryWrite.limeActivationCode, List.append_assoc]⟩
  · rintro ⟨kept, removed, cut, after, split, suffix, nonempty, rfl⟩
    exact ⟨_, lime_trap_front_iff.mpr ⟨kept, removed, cut, after, split, suffix, nonempty, rfl⟩,
      by simp [configAt, renderUnder, frameCode, MemoryWrite.limeActivationCode, List.append_assoc]⟩

theorem stays {phase : Phase H} (notDone : ∀ out, phase ≠ .done out)
    {types : List Wasm.Lime1.FuncType} {n : Nat} {cont : Wasm.Lime1.Expr} {out : List Admin} :
    ¬ PureStep types [.label n cont (values saved ++ render callee phase ++ tail)] out := by
  have frameStays {k : Nat} {fr : Frame} {body : List Admin} :
      ¬ PureStep types [.label n cont (values saved ++ .frame k fr body :: tail)] out :=
    lime_label_stays rfl (by simp) (by simp) (by simp)
  cases phase with
  | invoke args =>
    simpa only [renderUnder, values_append, List.append_assoc, List.singleton_append] using
      (lime_label_stays (types := types) (n := n) (cont := cont) (out := out)
        (stack := saved ++ args) (head := .invoke callee.address) (rest := tail) rfl
        (by simp) (by simp) (by simp))
  | body | ifBlock | arm | child | hostInvoke | branch | lowered | trapped | exit => simpa only [renderUnder, frameCode, List.append_assoc, List.singleton_append] using frameStays
  | done out => exact (notDone out rfl).elim

private theorem call_iff {args stack : List Value} {target : CallTarget}
    {rest : List Graph.Memory32.Op}
    (resolves : callee.fn.declaration.module.funcs[target.index.toNat]? = some target.address) :
    Step CallFrame.limeNoHost (cfg bytes (.body args stack (.ranked (.call target) :: rest))) dst ↔
      dst = ⟨mem.store bytes, caller, MemoryWrite.limeActivationCode resultCount (callee.fn.declaration.frame args)
        saved tail (values stack ++ .invoke target.address :: code rest)⟩ := by
  rw [show cfg bytes (.body args stack (.ranked (.call target) :: rest)) =
      ⟨mem.store bytes, caller, MemoryWrite.limeActivationCode resultCount (callee.fn.declaration.frame args)
        saved tail (values stack ++ .source (.call target.index) :: code rest)⟩ from by
    simp only [configAt, renderUnder, frameCode, code_cons, MemoryWrite.limeActivationCode, List.append_assoc, List.singleton_append]
    rfl]
  rw [body_iff (fun _ => lime_label_stays rfl (by simp) (by simp) (by simp))]
  have resolve {mid : Config H} := lime_direct_call_iff (s := mem.store bytes)
    (f := callee.fn.declaration.frame args) (stack := stack) (tail := code rest) (dst := mid) resolves
  constructor
  · rintro ⟨mid, step, rfl⟩
    obtain rfl := resolve.mp step
    rfl
  · rintro rfl
    exact ⟨_, resolve.mpr rfl, rfl⟩

private theorem indirect_linked {index : TypeIdx} {signature : Wasm.V1.FuncType}
    (link : site.MemoryIndirect mem host callee index signature .recursive) :
    (site.memorySite index signature).Linked base callee.fn.declaration.module := by
  refine ⟨link.tableAt, link.signatureAt, rfl, ?_, ?_⟩
  · intro address fn found
    simp [IndirectSite.memorySite, Graph.Program.lookup] at found
  · intro address member
    obtain ⟨fn, allocated, registered⟩ := link.entries address member
    refine ⟨fn, allocated, fun typed => ?_⟩
    cases fn with
    | host => trivial
    | wasm =>
      obtain ⟨child, found, exactAllocation, _⟩ := registered typed
      exact .inr ⟨child, found, exactAllocation⟩

private theorem indirect_iff {args stack : List Value} {index : TypeIdx} {signature : Wasm.V1.FuncType}
    {selector : BitVec 32} {rest : List Graph.Memory32.Op}
    (link : site.MemoryIndirect mem host callee index signature .recursive) :
    Step CallFrame.limeNoHost (cfg bytes (.body args (stack ++ [Value.int .i32 selector])
      (.callIndirect index signature :: rest))) dst ↔
      ∃ target, (site.memorySite index signature).Lookup base selector target ∧
        dst = ⟨mem.store bytes, caller, MemoryWrite.limeActivationCode resultCount
          (callee.fn.declaration.frame args) saved tail
          (values stack ++ IndirectSite.lookupHead target :: code rest)⟩ := by
  rw [show cfg bytes (.body args (stack ++ [Value.int .i32 selector]) (.callIndirect index signature :: rest)) =
      ⟨mem.store bytes, caller, MemoryWrite.limeActivationCode resultCount (callee.fn.declaration.frame args)
        saved tail (values (stack ++ [Value.int .i32 selector]) ++ .source (.callIndirect index) :: code rest)⟩ from by
    simp only [configAt, renderUnder, frameCode, code_cons, MemoryWrite.limeActivationCode, List.append_assoc, List.singleton_append]
    rfl]
  rw [body_iff (fun _ => lime_label_stays rfl (by simp) (by simp) (by simp))]
  have resolve {mid : Config H} := IndirectSite.step_iff (memory := mem) (bytes := bytes)
    (indirect := site.memorySite index signature) (active := callee.fn.declaration.frame args)
    (stack := stack) (selector := selector) (rest := code rest) (dst := mid) (indirect_linked link)
  constructor
  · rintro ⟨mid, step, rfl⟩
    obtain ⟨target, lookup, rfl⟩ := resolve.mp step
    exact ⟨target, lookup, rfl⟩
  · rintro ⟨target, lookup, rfl⟩
    exact ⟨_, resolve.mpr ⟨target, lookup, rfl⟩, rfl⟩

private def activationContext (callee : MemoryTarget) (arity : Nat) (args saved : List Value) (tail : List Admin) :
    EvalCtx Wasm.Lime1.Instr :=
  .seq saved (.frame arity (callee.fn.declaration.frame args)
    (.seq [] (.label arity [] .hole) [])) tail

private def hostContext (callee : MemoryTarget) (arity : Nat) (args saved stack : List Value) (tail : List Admin)
    (rest : List Graph.Memory32.Op) : EvalCtx Wasm.Lime1.Instr :=
  (activationContext callee arity args saved tail).comp (.seq stack .hole (code rest))

private theorem pending_eq {args stack operands : List Value} {target : Site H} {rest : List Graph.Memory32.Op} :
    cfg bytes (.hostInvoke args stack target operands rest) =
      target.pending (mem.store bytes) caller (hostContext callee arity args saved stack tail rest) operands := by
  simp [configAt, renderUnder, frameCode, Site.pending, hostContext, activationContext, EvalCtx.plug_comp, EvalCtx.plug,
    values, List.append_assoc]

private theorem host_iff {args stack operands : List Value} {target : Site H} {rest : List Graph.Memory32.Op}
    (allocated : target.Allocated base) (typed : target.Arguments operands)
    (contract : target.Contract mem host) (live : mem.Live bytes) :
    Step host (cfg bytes (.hostInvoke args stack target operands rest)) dst ↔
      (∃ written vs, mem.Live written ∧ target.TypedResult (.values vs) ∧
        host target.code (mem.store bytes) operands (.returned (mem.store written) (.values vs)) ∧
        dst = cfg written (.body args (stack ++ vs) rest)) ∨
      (∃ written, mem.Live written ∧ host target.code (mem.store bytes) operands (.returned (mem.store written) .trap) ∧
        dst = cfg written (.trapped args stack (code rest))) ∨
      (host target.code (mem.store bytes) operands .diverged ∧
        dst = cfg bytes (.hostInvoke args stack target operands rest)) := by
  have move := Site.step_iff (dst := dst) (outer := caller) (bytes := bytes)
    (context := hostContext callee arity args saved stack tail rest) allocated contract live typed
  rw [← pending_eq] at move
  simp only [hostContext, activationContext, EvalCtx.plug_comp, EvalCtx.plug, List.map_nil,
    List.nil_append, List.append_nil] at move
  constructor
  · intro step
    rcases move.mp step with ⟨written, out, nextLive, valid, answer, rfl⟩ | diverged
    · cases out with
      | values vs =>
        exact .inl ⟨written, vs, nextLive, valid, answer, by simp [configAt, renderUnder, frameCode, result, values]⟩
      | trap => exact .inr (.inl ⟨written, nextLive, answer, by simp [configAt, renderUnder, frameCode, result, values]⟩)
    · exact .inr (.inr diverged)
  · rintro (⟨written, vs, nextLive, valid, answer, rfl⟩ | ⟨written, nextLive, answer, rfl⟩ | diverged)
    · exact move.mpr (.inl ⟨written, .values vs, nextLive, valid, answer,
        by simp [configAt, renderUnder, frameCode, result, values]⟩)
    · exact move.mpr (.inl ⟨written, .trap, nextLive, trivial, answer, by simp [configAt, renderUnder, frameCode, result, values]⟩)
    · exact move.mpr (.inr diverged)

private theorem v1Code_map (ops : List Graph.Memory32.Op) :
    Graph.Memory32.v1Code ops = ops.map Graph.Memory32.Op.v1 := by
  induction ops <;> simp [Graph.Memory32.v1Code, *]

private theorem br_if_iff {args stack : List Value} {depth : LabelIdx} {payload : List NumType} {guard : BitVec 32}
    {rest : List Graph.Memory32.Op} :
    Step CallFrame.limeNoHost (cfg bytes (.body args (stack ++ [Value.int .i32 guard])
      (.ranked (.brIf depth payload) :: rest))) dst ↔
      dst = cfg bytes (afterBrIf args stack depth payload rest guard) := by
  rw [show cfg bytes (.body args (stack ++ [Value.int .i32 guard]) (.ranked (.brIf depth payload) :: rest)) =
    ⟨mem.store bytes, caller, MemoryWrite.limeActivationCode resultCount (callee.fn.declaration.frame args)
      saved tail (values (stack ++ [Value.int .i32 guard]) ++ .source (.brIf depth) :: code rest)⟩ from by
    simp only [configAt, renderUnder, frameCode, code_cons, MemoryWrite.limeActivationCode, List.append_assoc, List.singleton_append]
    rfl]
  rw [body_iff (fun _ => lime_label_stays rfl (by simp) (by simp) (by simp))]
  have localStep {mid : Config H} := lime_br_if_iff (s := mem.store bytes)
    (f := callee.fn.declaration.frame args) (saved := stack) (condition := guard)
    (depth := depth) (rest := code rest) (dst := mid)
  constructor
  · rintro ⟨mid, move, rfl⟩
    obtain rfl := localStep.mp move
    by_cases zero : guard = 0#32 <;>
      simp [zero, configAt, afterBrIf, renderUnder, frameCode, MemoryWrite.limeActivationCode, List.append_assoc]
  · rintro rfl
    refine ⟨_, localStep.mpr rfl, ?_⟩
    by_cases zero : guard = 0#32 <;>
      simp [zero, configAt, afterBrIf, renderUnder, frameCode, MemoryWrite.limeActivationCode, List.append_assoc]

private theorem branch_pop {args stack : List Value} {depth : LabelIdx} {signature : List NumType}
    {rest : List Graph.Memory32.Op}
    (step : Step CallFrame.limeNoHost (cfg bytes (.branch args stack depth signature rest)) dst) :
    ∃ out, PureStep callee.fn.declaration.module.types
      [.label resultCount [] (values stack ++ .source (.br depth) :: code rest)] out ∧
      dst = ⟨mem.store bytes, caller, values saved ++ .frame resultCount (callee.fn.declaration.frame args) out :: tail⟩ := by
  obtain ⟨mid, inside, rfl⟩ := CallContinuation.lime_frame_context_inv
    (by simpa only [configAt, renderUnder, frameCode, List.append_assoc, List.singleton_append] using step)
  rcases lime_body_step_cases inside with ⟨_, stuck, _⟩ | ⟨out, pop, rfl⟩
  · exact (BranchExit.lime_br_vals_stuck stuck).elim
  · exact ⟨out, pop, by simp⟩

private theorem branch_iff {args scratch payload : List Value} {signature : List NumType}
    {rest : List Graph.Memory32.Op} (count : payload.length = resultCount) :
    Step CallFrame.limeNoHost (cfg bytes (.branch args (scratch ++ payload) ⟨0⟩ signature rest)) dst ↔
      dst = cfg bytes (.exit args (.values payload)) := by
  constructor
  · intro step
    obtain ⟨_, pop, rfl⟩ := branch_pop step
    obtain ⟨kept, delivered, split, arity, rfl⟩ := BranchExit.lime_label_br_zero pop
    have same := (List.append_inj' split (count.trans arity.symm)).2
    subst delivered
    simp [configAt, renderUnder, frameCode, result, List.append_assoc]
  · rintro rfl
    have pop := PureStep.labelBranch (types := callee.fn.declaration.module.types)
      resultCount [] scratch payload (code rest) count
    simpa [configAt, renderUnder, frameCode, result, expression, values_append, List.append_assoc] using
      Step.context (Step.frame (Step.pure (host := CallFrame.limeNoHost) (mem.store bytes)
        (callee.fn.declaration.frame args) pop) resultCount caller) saved tail

private theorem branch_lower_iff {args stack : List Value} {depth : LabelIdx} {signature : List NumType}
    {rest : List Graph.Memory32.Op} (positive : 0 < depth.toNat) :
    Step CallFrame.limeNoHost (cfg bytes (.branch args stack depth signature rest)) dst ↔
      dst = cfg bytes (.lowered args stack (lowerLabel depth) signature) := by
  constructor
  · intro step
    obtain ⟨_, pop, rfl⟩ := branch_pop step
    rcases BranchExit.lime_label_br_iff.mp (Step.pure (host := CallFrame.limeNoHost)
        (mem.store bytes) (callee.fn.declaration.frame args) pop) with
      ⟨_, _, _, _, zero, _⟩ | ⟨_, eq⟩
    · omega
    · cases eq
      simp [configAt, renderUnder, frameCode, List.append_assoc]
  · rintro rfl
    have pop := PureStep.labelBranchOuter (types := callee.fn.declaration.module.types)
      resultCount [] stack (code rest) depth (Nat.ne_of_gt positive)
    simpa [configAt, renderUnder, frameCode, List.append_assoc] using
      Step.context (Step.frame (Step.pure (host := CallFrame.limeNoHost) (mem.store bytes)
        (callee.fn.declaration.frame args) pop) resultCount caller) saved tail

private theorem if_select_iff {args stack : List Value} {type : Option NumType} {guard : BitVec 32}
    {left right rest : List Graph.Memory32.Op} :
    Step CallFrame.limeNoHost (cfg bytes (.body args (stack ++ [Value.int .i32 guard]) (.if_ type left right :: rest))) dst ↔
      dst = cfg bytes (.ifBlock args stack type (selectArm guard left right) rest) := by
  have codeIf : code (.if_ type left right :: rest) =
      .source (.if_ (blockType type) (expr left) (expr right)) :: code rest := by
    simp only [code_cons, Graph.Memory32.Op.v1, Wasm.V1.Instr.toLime, blockType, expr,
      Wasm.V1.Expr.toLime_eq_map, v1Code_map, List.map_map, Function.comp_def]
  rw [show cfg bytes (.body args (stack ++ [Value.int .i32 guard]) (.if_ type left right :: rest)) =
      ⟨mem.store bytes, caller, MemoryWrite.limeActivationCode resultCount (callee.fn.declaration.frame args)
        saved tail (values (stack ++ [Value.int .i32 guard]) ++
          .source (.if_ (blockType type) (expr left) (expr right)) :: code rest)⟩ from by
    simp only [configAt, renderUnder, frameCode, codeIf, MemoryWrite.limeActivationCode, List.append_assoc,
      List.singleton_append]]
  rw [body_iff (fun _ => lime_label_stays rfl (by simp) (by simp) (by simp))]
  have chosen : (if guard = 0 then expr right else expr left) = expr (selectArm guard left right) := by
    exact (apply_ite expr (guard = (0 : BitVec 32)) right left).symm
  have step {mid : Config H} :=
    lime_if_iff (s := mem.store bytes) (f := callee.fn.declaration.frame args) (saved := stack)
      (condition := guard) (bt := blockType type) (thenBody := expr left) (elseBody := expr right)
      (rest := code rest) (dst := mid)
  rw [chosen] at step
  constructor
  · rintro ⟨mid, move, rfl⟩
    obtain rfl := step.mp move
    simp [configAt, renderUnder, frameCode, MemoryWrite.limeActivationCode, List.append_assoc]
  · rintro rfl
    exact ⟨_, step.mpr rfl, by
      simp [configAt, renderUnder, frameCode, MemoryWrite.limeActivationCode, List.append_assoc]⟩

private theorem if_enter_iff {args stack : List Value} {type : Option NumType} {arm rest : List Graph.Memory32.Op} :
    Step CallFrame.limeNoHost (cfg bytes (.ifBlock args stack type arm rest)) dst ↔
      dst = cfg bytes (.arm args stack type (.body args [] arm) rest) := by
  rw [show cfg bytes (.ifBlock args stack type arm rest) =
      ⟨mem.store bytes, caller, MemoryWrite.limeActivationCode resultCount (callee.fn.declaration.frame args)
        saved tail (values stack ++ .source (.block (blockType type) (expr arm)) :: code rest)⟩ from by
    simp [configAt, renderUnder, frameCode, MemoryWrite.limeActivationCode, List.append_assoc]]
  rw [body_iff (fun _ => lime_label_stays rfl (by simp) (by simp) (by simp))]
  have signature : blockType? callee.fn.declaration.module.types (blockType type) =
      some ⟨[], type.toList⟩ := by cases type <;> rfl
  constructor
  · rintro ⟨mid, step, rfl⟩
    obtain ⟨kept, used, ft, split, found, arity, rfl⟩ := lime_block_step_iff.mp step
    change blockType? callee.fn.declaration.module.types (blockType type) = some ft at found
    rw [signature] at found
    cases found
    have nil : used = [] := List.length_eq_zero_iff.mp arity
    subst used
    simp at split
    subst kept
    simp [configAt, renderUnder, frameCode, MemoryWrite.limeActivationCode, code, expr, List.append_assoc]
  · rintro rfl
    refine ⟨_, lime_block_step_iff.mpr ⟨stack, [], ⟨[], type.toList⟩, by simp, signature, rfl, rfl⟩, ?_⟩
    simp [configAt, renderUnder, frameCode, MemoryWrite.limeActivationCode, code, expr, List.append_assoc]

private theorem step_in_body {args : List Value} {body : List Admin}
    (stays : ∀ out, ¬ PureStep callee.fn.declaration.module.types [.label resultCount [] body] out) :
    Step host ⟨mem.store bytes, caller, MemoryWrite.limeActivationCode resultCount
      (callee.fn.declaration.frame args) saved tail body⟩ dst ↔
    ∃ mid, Step host ⟨mem.store bytes, callee.fn.declaration.frame args, body⟩ mid ∧
      dst = ⟨mid.store, caller, MemoryWrite.limeActivationCode resultCount mid.frame saved tail mid.code⟩ := by
  constructor
  · intro step
    rcases step.internal_or_callout with internal | ⟨_, located, answer⟩
    · obtain ⟨mid, move, eq⟩ := (body_iff stays).mp internal
      exact ⟨mid, Step.of_internal move, eq⟩
    · let context : EvalCtx Wasm.Lime1.Instr :=
        .seq saved (.frame resultCount (callee.fn.declaration.frame args) (.seq [] (.label resultCount [] .hole) [])) tail
      obtain ⟨_, mid, here, outcome, eq⟩ := answer_through
        (context := context) (inner := ⟨mem.store bytes, callee.fn.declaration.frame args, body⟩)
        (wrapped := ⟨mem.store bytes, caller, MemoryWrite.limeActivationCode resultCount
          (callee.fn.declaration.frame args) saved tail body⟩)
        (by simp [context, EvalCtx.plug, values, MemoryWrite.limeActivationCode]) rfl
        (by simp [decompose?, MemoryWrite.limeActivationCode]) located answer
      have frameEq : mid.frame = callee.fn.declaration.frame args := by cases outcome <;> rfl
      exact ⟨mid, outcome.step here, by
        rw [eq, frameEq]
        simp [context, EvalCtx.plug, values, MemoryWrite.limeActivationCode]⟩
  · rintro ⟨mid, step, rfl⟩
    simpa only [MemoryWrite.limeActivationCode, List.append_assoc, List.singleton_append] using
      Step.context (Step.frame (Step.label step resultCount []) resultCount caller) saved tail

private theorem step_frame_label {s : Store H} {active : Frame} {k : Nat} {body : List Admin} :
    Step host ⟨s, caller, [.frame k active [.label k [] body]]⟩ dst ↔
      ∃ mid, Step host ⟨s, active, [.label k [] body]⟩ mid ∧
        dst = ⟨mid.store, caller, [.frame k mid.frame mid.code]⟩ := by
  constructor
  · intro step
    rcases step.internal_or_callout with internal | ⟨_, located, answer⟩
    · rcases lime_body_step_cases internal with ⟨mid, move, rfl⟩ | ⟨out, pop, rfl⟩
      · exact ⟨_, .label (Step.of_internal move) k [], rfl⟩
      · exact ⟨_, .pure s active pop, rfl⟩
    · obtain ⟨_, mid, here, outcome, eq⟩ := answer_through
        (context := .frame k active .hole) (inner := ⟨s, active, [.label k [] body]⟩)
        (wrapped := ⟨s, caller, [.frame k active [.label k [] body]]⟩) rfl rfl
        (by simp [decompose?]) located answer
      have frameEq : mid.frame = active := by cases outcome <;> rfl
      exact ⟨mid, outcome.step here, by rw [eq, frameEq]; rfl⟩
  · rintro ⟨mid, move, rfl⟩
    exact .frame move k caller

private theorem step_label_with_tail {s : Store H} {active : Frame} {k : Nat}
    {stack : List Value} {body rest : List Admin} :
    Step host ⟨s, active, values stack ++ .label k [] body :: rest⟩ dst ↔
      ∃ mid, Step host ⟨s, active, [.label k [] body]⟩ mid ∧
        dst = ⟨mid.store, mid.frame, values stack ++ mid.code ++ rest⟩ := by
  constructor
  · intro step
    rcases step.internal_or_callout with internal | ⟨_, located, answer⟩
    · rcases Blocks.Context.lime_label_iff.mp internal with ⟨mid, move, rfl⟩ | ⟨out, pop, rfl⟩
      · exact ⟨_, .label (Step.of_internal move) k [], by simp⟩
      · exact ⟨_, .pure s active pop, rfl⟩
    · obtain ⟨_, mid, here, outcome, eq⟩ := answer_through
        (context := .seq stack .hole rest) (inner := ⟨s, active, [.label k [] body]⟩)
        (wrapped := ⟨s, active, values stack ++ .label k [] body :: rest⟩)
        (by simp [EvalCtx.plug, values]) rfl (by simp [decompose?]) located answer
      have frameEq : mid.frame = active := by cases outcome <;> rfl
      exact ⟨mid, outcome.step here, by rw [eq, frameEq]; rfl⟩
  · rintro ⟨mid, move, rfl⟩
    simpa only [List.append_assoc, List.singleton_append] using Step.context move stack rest

private theorem rendered_label {args : List Value} {phase : Phase H} (entered : InLabel args phase) (k : Nat) :
    ∃ body, renderUnder callee k false phase = [.label k [] body] ∧
      renderAt callee k phase = [.frame k (callee.fn.declaration.frame args) [.label k [] body]] := by
  cases phase <;> simp only [InLabel] at entered <;> subst args <;> exact ⟨_, rfl, rfl⟩

private theorem render_step_at_label {args : List Value} {phase : Phase H} (k : Nat)
    (entered : LabelSuccessor args phase) :
    renderAt callee k phase =
      [.frame k (callee.fn.declaration.frame args) (renderUnder callee k false phase)] := by
  cases entered with
  | active inside =>
    obtain ⟨_, bare, boxed⟩ := rendered_label (callee := callee) inside k
    rw [bare, boxed]
  | exit | lowered => rfl

private theorem after_arm_render (callee : MemoryTarget) (k : Nat) (args stack : List Value)
    (type : Option NumType) (rest : List Graph.Memory32.Op) (phase : Phase H) :
    renderAt callee k (afterArm args stack type rest phase) =
      [.frame k (callee.fn.declaration.frame args)
        [.label k [] (values stack ++ renderUnder callee type.toList.length false phase ++ code rest)]] := by
  cases phase <;> try rfl
  case exit outArgs out => cases out <;>
    simp [afterArm, renderUnder, frameCode, result, values_append, List.append_assoc]
  case lowered => simp [afterArm, renderUnder, frameCode, values_append, List.append_assoc]

/-- Apply the local activation theorem at the arm's arity. The frame in the
inner premise serves only to reuse that theorem. The outer native code has the
arm label inside the existing frame. -/
private theorem arm_context {args stack : List Value} {type : Option NumType}
    {phase : Phase H} {rest : List Graph.Memory32.Op} (entered : InLabel args phase) :
    Step host (cfg bytes (.arm args stack type phase rest)) dst ↔
      ∃ (mid : Config H), Step host (configAt mem (callee.fn.declaration.frame args) [] [] callee type.toList.length bytes phase)
        ⟨mid.store, callee.fn.declaration.frame args, [.frame type.toList.length mid.frame mid.code]⟩ ∧
        dst = ⟨mid.store, caller, MemoryWrite.limeActivationCode resultCount mid.frame saved tail
          (values stack ++ mid.code ++ code rest)⟩ := by
  obtain ⟨body, bare, boxed⟩ := rendered_label (callee := callee) entered type.toList.length
  rw [show cfg bytes (.arm args stack type phase rest) =
      ⟨mem.store bytes, caller, MemoryWrite.limeActivationCode resultCount (callee.fn.declaration.frame args)
        saved tail (values stack ++ .label type.toList.length [] body :: code rest)⟩ from by
    simp [configAt, renderUnder, frameCode, bare, MemoryWrite.limeActivationCode, List.append_assoc]]
  rw [step_in_body (fun _ => lime_label_stays rfl (by simp) (by simp) (by simp))]
  constructor
  · rintro ⟨mid, inside, rfl⟩
    obtain ⟨after, move, rfl⟩ := step_label_with_tail.mp inside
    exact ⟨after, by
      simpa only [configAt, boxed, values, List.map_nil, List.nil_append, List.append_nil] using (Step.frame move _ _), rfl⟩
  · rintro ⟨mid, step, rfl⟩
    have installed : Step host ⟨mem.store bytes, callee.fn.declaration.frame args,
        [.frame type.toList.length (callee.fn.declaration.frame args) [.label type.toList.length [] body]]⟩
        ⟨mid.store, callee.fn.declaration.frame args, [.frame type.toList.length mid.frame mid.code]⟩ := by
      simpa only [configAt, boxed, values, List.map_nil, List.nil_append, List.append_nil] using step
    obtain ⟨after, move, eq⟩ := step_frame_label.mp installed
    obtain ⟨storeEq, frameEq, codeEq⟩ := (show mid.store = after.store ∧ mid.frame = after.frame ∧ mid.code = after.code from by
      simpa only [Execution.Runtime.Config.mk.injEq, true_and, and_true, List.cons.injEq, Execution.Runtime.AdminInstr.frame.injEq] using eq)
    exact ⟨_, step_label_with_tail.mpr ⟨_, move, rfl⟩, by rw [storeEq, frameEq, codeEq]⟩

private theorem code_absent (s : Store H) (ops : List Graph.Memory32.Op) (stack : List Value) :
    Execution.Runtime.decomposeFrom? coding s stack (code ops) = none := by
  induction ops generalizing stack with
  | nil => rfl
  | cons op rest ih =>
    change Execution.Runtime.decomposeFrom? coding s stack (.source op.v1.toLime :: code rest) = none
    rw [decomposeFrom?_source_cons]
    cases asValue? (.source op.v1.toLime) <;> simp [ih]

private theorem internal_of_absent {src : Config H} (absent : decompose? src = none)
    (move : Step host src dst) : Step CallFrame.limeNoHost src dst := by
  rcases move.internal_or_callout with internal | ⟨call, located, _⟩
  · exact internal
  · have known := exists_callout_iff.mp ⟨call, located⟩
    simp [absent] at known

private theorem child_context {args stack : List Value} {child : MemoryTarget} {phase : Phase H}
    {rest : List Graph.Memory32.Op} (notDone : ∀ out, phase ≠ .done out) :
    Step host (cfg bytes (.child args stack child phase rest)) dst ↔
      ∃ mid,
        Step host (config mem (callee.fn.declaration.frame args) stack (code rest) child bytes phase) mid ∧
        dst = ⟨mid.store, caller, MemoryWrite.limeActivationCode resultCount mid.frame saved tail mid.code⟩ := by
  have keep := step_in_body (host := host) (mem := mem) (callee := callee) (caller := caller) (saved := saved)
    (tail := tail) (bytes := bytes) (args := args) (dst := dst) (arity := arity)
    (fun _ => stays (callee := child) (saved := stack) (tail := code rest) notDone)
  simpa only [configAt, renderUnder, frameCode, MemoryWrite.limeActivationCode, List.append_assoc, List.singleton_append] using keep

private theorem entry_not_lowered {phase : Phase H} (ready : Ready mem host site callee phase)
    (args stack : List Value) (depth : LabelIdx) (result : List NumType) :
    phase ≠ .lowered args stack depth result := by
  rintro rfl
  cases ready.2.1

private theorem read {phase : Phase H} (linked : site.MemoryLinked mem host .recursive)
    (registered : site.memoryLookup callee.address = some callee.fn) (allocated : callee.Allocated base)
    (label : (labels ++ callee.fn.entryLabels)[0]? = some types)
    (ready : ReadyAt mem host site callee types labels phase) (live : mem.Live bytes) (notDone : ∀ out, phase ≠ .done out)
    (notLowered : ∀ args stack depth result, phase ≠ .lowered args stack depth result)
    (move : Step host (regionCfg bytes phase) dst) :
    ∃ nextBytes next, Edge mem host site callee bytes phase nextBytes next ∧ dst = regionCfg nextBytes next := by
  induction phase generalizing callee caller saved tail bytes dst types labels with
  | invoke args =>
    obtain ⟨typed, rfl, rfl⟩ := ready
    have liveAllocation : callee.Allocated (mem.store bytes) := allocated
    unfold MemoryTarget.Allocated at liveAllocation
    have inside := internal_of_absent (by
      simp [decompose?, configAt, renderUnder, List.append_assoc, decomposeFrom?_invoke_cons,
        Execution.Runtime.decomposeHead?, liveAllocation]) move
    exact ⟨_, _, .enter, (enter_iff allocated typed).mp inside⟩
  | body args stack ops =>
    have move := internal_of_absent (by simp [decompose?, configAt, renderUnder, frameCode,
      List.append_assoc, code_absent]) move
    have checked := linked.checked callee registered
    cases ops with
    | nil =>
      have step := leave_label_iff (args := args) (out := .values stack)
        (mem := mem) (callee := callee) (bytes := bytes) (caller := caller) (saved := saved) (tail := tail) (dst := dst) (arity := types.length)
      exact ⟨_, _, .labelDone, step.mp (by simpa [configAt, renderUnder, frameCode, MemoryWrite.limeActivationCode, result,
        List.append_assoc] using move)⟩
    | cons op ops =>
      have supported := List.all_eq_true.mp ready.2.1 op (List.mem_cons_self ..)
      cases op with
      | load offset =>
        obtain ⟨stack, ptr, rfl, _⟩ := Graph.Memory32.Function.region_load_typed ready.2.2.1
        rcases (load_iff checked).mp move with ⟨bits, edge, eq⟩ | ⟨edge, eq⟩
        · exact ⟨_, _, .load edge, eq⟩
        · exact ⟨_, _, .loadTrap edge, eq⟩
      | store offset =>
        obtain ⟨stack, ptr, word, rfl, _⟩ := Graph.Memory32.Function.region_store_typed ready.2.2.1
        rcases (store_iff checked live).mp move with ⟨written, edge, _, eq⟩ | ⟨edge, eq⟩
        · exact ⟨_, _, .store edge, eq⟩
        · exact ⟨_, _, .storeTrap edge, eq⟩
      | size => exact ⟨_, _, .size, (size_iff checked).mp move⟩
      | grow =>
        obtain ⟨stack, delta, rfl, _⟩ := Graph.Memory32.Function.region_grow_typed ready.2.2.1
        rcases (grow_iff checked).mp move with ⟨grown, edge, eq⟩ | eq
        · exact ⟨_, _, .grow supported edge, eq⟩
        · exact ⟨_, _, .growFail, eq⟩
      | ranked op =>
        cases op with
        | numeric op =>
          cases op with
          | get index =>
            obtain ⟨v, found, _⟩ := get_typed ready.1 ready.2.2.1
            exact ⟨_, _, .get found, (get_iff found).mp move⟩
          | bin => contradiction
        | call target =>
          obtain ⟨stack, operands, rfl, typed, used, _⟩ := call_typed ready.2.2.1
          rcases linked.direct callee registered target used with ⟨child, link, _⟩ | ⟨hostCode, link⟩
          · obtain rfl := (call_iff link.resolves).mp move
            exact ⟨_, _, .call link typed, by
              simp [configAt, renderUnder, frameCode, MemoryWrite.limeActivationCode, link.address, values_append, List.append_assoc]⟩
          · obtain rfl := (call_iff link.resolves).mp move
            exact ⟨_, _, .callHost link typed, by
              simp [configAt, renderUnder, frameCode, MemoryWrite.limeActivationCode, Site.directTarget, List.append_assoc]⟩
        | brIf depth payload =>
          obtain ⟨stack, guard, rfl, _, _, _⟩ := Graph.Memory32.Function.br_if_typed ready.2.2.1
          exact ⟨_, _, .brIf, br_if_iff.mp move⟩
        | _ => contradiction
      | callIndirect index signature =>
        obtain ⟨stack, operands, selector, rfl, typed, _⟩ := indirect_typed ready.2.2.1
        have link := linked.indirect callee registered index signature (ready.2.2.2 (source_head _ _))
        obtain ⟨target, lookup, rfl⟩ := (indirect_iff link).mp move
        cases target with
        | none =>
          refine ⟨_, _, .indirectTrap lookup, ?_⟩
          simp [configAt, renderUnder, frameCode, MemoryWrite.limeActivationCode, IndirectSite.lookupHead, List.append_assoc]
        | some target =>
          cases target with
          | host target =>
            exact ⟨_, _, .callIndirectHost lookup typed, by
              simp [configAt, renderUnder, frameCode, MemoryWrite.limeActivationCode, IndirectSite.lookupHead, List.append_assoc]⟩
          | wasm =>
            cases lookup with
            | wasm _ found _ _ => simp [IndirectSite.memorySite, Graph.Program.lookup] at found
          | memory child =>
            exact ⟨_, _, .callIndirect lookup typed, by
              simp [configAt, renderUnder, frameCode, MemoryWrite.limeActivationCode, IndirectSite.lookupHead, values_append, List.append_assoc]⟩
      | if_ type left right =>
        obtain ⟨stack, guard, rfl, _, _, _⟩ := Graph.Memory32.Function.if_typed ready.2.2.1
        exact ⟨_, _, .ifSelect, if_select_iff.mp move⟩
      | _ => contradiction
  | ifBlock args stack type arm rest =>
    have inside := internal_of_absent (by
      simp [decompose?, configAt, renderUnder, frameCode, asValue?]) move
    exact ⟨_, _, .ifEnter, if_enter_iff.mp inside⟩
  | arm args stack type phase rest ih =>
    obtain ⟨_, entered, active, _, _, _⟩ := ready
    obtain ⟨mid, inside, rfl⟩ := (arm_context entered).mp move
    obtain ⟨written, next, move, eq⟩ := ih registered allocated rfl active live (by
      intro out done
      subst phase
      simp [InLabel] at entered) (by
      rintro args stack depth result rfl
      simp [InLabel] at entered) inside
    have rendered := render_step_at_label (callee := callee) type.toList.length (inLabel_next entered move)
    have matched : mid.store = mem.store written ∧ mid.frame = callee.fn.declaration.frame args ∧
        mid.code = renderUnder callee type.toList.length false next := by
      simpa [configAt, rendered, values] using eq
    obtain ⟨storeEq, frameEq, codeEq⟩ := matched
    refine ⟨_, _, .armStep entered move, ?_⟩
    simp [configAt, after_arm_render, storeEq, frameEq, codeEq, MemoryWrite.limeActivationCode, List.append_assoc]
  | child args stack child phase rest ih =>
    obtain ⟨_, found, childAllocated, childActive, childReady, _, _, _⟩ := ready
    obtain ⟨mid, inside, rfl⟩ := (child_context childActive).mp move
    obtain ⟨written, next, step, rfl⟩ := ih found childAllocated rfl childReady live childActive (entry_not_lowered childReady) inside
    refine ⟨_, _, .child step, ?_⟩
    simp only [configAt, after_child_render, MemoryWrite.limeActivationCode, List.append_assoc, List.singleton_append]
  | hostInvoke args stack target operands rest =>
    obtain ⟨_, allocated, typed, contract, _, _, _⟩ := ready
    rcases (host_iff allocated typed contract live).mp move with
      ⟨written, vs, nextLive, valid, behavior, eq⟩ | ⟨written, nextLive, behavior, eq⟩ | ⟨behavior, eq⟩
    · exact ⟨_, _, .hostReturned nextLive valid behavior, eq⟩
    · exact ⟨_, _, .hostTrapped nextLive behavior, eq⟩
    · exact ⟨_, _, .hostDiverged behavior, eq⟩
  | branch args stack depth signature rest =>
    have inside := internal_of_absent (by
      simp [decompose?, configAt, renderUnder, frameCode, asValue?]) move
    by_cases zero : depth.toNat = 0
    · have same : depth = ⟨0⟩ := Idx.toNat_injective zero
      subst depth
      obtain ⟨scratch, payload, rfl, typed⟩ := Graph.SuffixTyped.split ready.2.2
      have count : payload.length = types.length := by
        simpa using congrArg List.length (typed.trans (branch_result label ready.2))
      exact ⟨_, _, .branchDone typed, (branch_iff count).mp inside⟩
    · have positive : 0 < depth.toNat := Nat.pos_of_ne_zero zero
      exact ⟨_, _, .branchLower positive, (branch_lower_iff positive).mp inside⟩
  | lowered args stack depth result => exact (notLowered args stack depth result rfl).elim
  | trapped args stack rest =>
    have move := internal_of_absent (by simp [decompose?, configAt, renderUnder, frameCode]) move
    by_cases active : stack ≠ [] ∨ rest ≠ []
    · obtain ⟨kept, removed, cut, after, split, suffix, nonempty, eq⟩ := (erase_iff active).mp move
      exact ⟨_, _, .erase split suffix nonempty, eq⟩
    · obtain ⟨stackNil, restNil⟩ := not_or.mp active
      have : stack = [] := not_not.mp stackNil
      have : rest = [] := not_not.mp restNil
      subst stack rest
      have step := leave_label_iff (args := args) (out := .trap)
        (mem := mem) (callee := callee) (bytes := bytes) (caller := caller) (saved := saved) (tail := tail) (dst := dst) (arity := types.length)
      exact ⟨_, _, .labelTrap, step.mp (by simpa [configAt, renderUnder, frameCode, MemoryWrite.limeActivationCode, result,
        values, List.append_assoc] using move)⟩
  | exit args out =>
    have move := internal_of_absent (by cases out <;>
      simp [decompose?, configAt, renderUnder, frameCode, result]) move
    exact ⟨_, _, .frameDone, (leave_frame_iff rfl ready.2).mp move⟩
  | done out => exact (notDone out rfl).elim

private theorem sound {phase next : Phase H} {written : ByteArray} (linked : site.MemoryLinked mem host .recursive)
    (registered : site.memoryLookup callee.address = some callee.fn)
    (allocated : callee.Allocated base) (label : (labels ++ callee.fn.entryLabels)[0]? = some types)
    (ready : ReadyAt mem host site callee types labels phase) (live : mem.Live bytes)
    (move : Edge mem host site callee bytes phase written next) : Step host (regionCfg bytes phase) (regionCfg written next) := by
  induction move generalizing caller saved tail types labels with
  | enter =>
    obtain ⟨typed, rfl, rfl⟩ := ready
    exact Step.of_internal ((enter_iff allocated typed).mpr rfl)
  | get found => exact Step.of_internal ((get_iff found).mpr rfl)
  | load edge => exact Step.of_internal ((load_iff (linked.checked _ registered)).mpr (.inl ⟨_, edge, rfl⟩))
  | loadTrap edge => exact Step.of_internal ((load_iff (linked.checked _ registered)).mpr (.inr ⟨edge, rfl⟩))
  | store edge =>
    exact Step.of_internal ((store_iff (linked.checked _ registered) live).mpr
      (.inl ⟨_, edge, mem.live_same_size live (MemoryWrite.closed_at edge), rfl⟩))
  | storeTrap edge => exact Step.of_internal ((store_iff (linked.checked _ registered) live).mpr (.inr ⟨edge, rfl⟩))
  | size => exact Step.of_internal ((size_iff (linked.checked _ registered)).mpr rfl)
  | grow _ edge => exact Step.of_internal ((grow_iff (linked.checked _ registered)).mpr (.inl ⟨_, edge, rfl⟩))
  | growFail => exact Step.of_internal ((grow_iff (linked.checked _ registered)).mpr (.inr rfl))
  | call link _ =>
    apply Step.of_internal
    exact (call_iff link.resolves).mpr (by
      simp [configAt, renderUnder, frameCode, MemoryWrite.limeActivationCode, link.address, values_append, List.append_assoc])
  | callHost link _ =>
    apply Step.of_internal
    exact (call_iff link.resolves).mpr (by
      simp [configAt, renderUnder, frameCode, MemoryWrite.limeActivationCode, Site.directTarget, List.append_assoc])
  | @callIndirect callee child bytes args operandsSaved operands index signature selector rest lookup _ =>
    have link := linked.indirect callee registered index signature (ready.2.2.2 (source_head _ _))
    apply Step.of_internal
    refine (indirect_iff link).mpr ⟨_, lookup, ?_⟩
    simp [configAt, renderUnder, frameCode, MemoryWrite.limeActivationCode, IndirectSite.lookupHead, values_append, List.append_assoc]
  | @indirectTrap callee bytes args stack index signature selector rest lookup =>
    have link := linked.indirect callee registered index signature (ready.2.2.2 (source_head _ _))
    apply Step.of_internal
    refine (indirect_iff link).mpr ⟨none, lookup, ?_⟩
    simp [configAt, renderUnder, frameCode, MemoryWrite.limeActivationCode, IndirectSite.lookupHead, List.append_assoc]
  | @callIndirectHost callee target bytes args operandsSaved operands index signature selector rest lookup _ =>
    have link := linked.indirect callee registered index signature (ready.2.2.2 (source_head _ _))
    apply Step.of_internal
    refine (indirect_iff link).mpr ⟨_, lookup, ?_⟩
    simp [configAt, renderUnder, frameCode, MemoryWrite.limeActivationCode, IndirectSite.lookupHead, List.append_assoc]
  | hostReturned nextLive valid answer =>
    exact (host_iff ready.2.1 ready.2.2.1 ready.2.2.2.1 live).mpr (.inl ⟨_, _, nextLive, valid, answer, rfl⟩)
  | hostTrapped nextLive answer =>
    exact (host_iff ready.2.1 ready.2.2.1 ready.2.2.2.1 live).mpr (.inr (.inl ⟨_, nextLive, answer, rfl⟩))
  | hostDiverged answer =>
    exact (host_iff ready.2.1 ready.2.2.1 ready.2.2.2.1 live).mpr (.inr (.inr ⟨answer, rfl⟩))
  | brIf => exact Step.of_internal (br_if_iff.mpr rfl)
  | branchDone typed =>
    have count := congrArg List.length (typed.trans (branch_result label ready.2))
    exact Step.of_internal ((branch_iff (by simpa using count)).mpr rfl)
  | branchLower positive => exact Step.of_internal ((branch_lower_iff positive).mpr rfl)
  | ifSelect => exact Step.of_internal (if_select_iff.mpr rfl)
  | ifEnter => exact Step.of_internal (if_enter_iff.mpr rfl)
  | @armStep callee bytes written args stack type phase next rest entered move ih =>
    have rendered := render_step_at_label (callee := callee) type.toList.length (inLabel_next entered move)
    have inside := ih (caller := callee.fn.declaration.frame args) (saved := []) (tail := code [])
      registered allocated rfl ready.2.2.1 live
    refine (arm_context entered).mpr
      ⟨⟨mem.store written, callee.fn.declaration.frame args, renderUnder callee type.toList.length false next⟩, ?_, ?_⟩
    · simpa only [configAt, rendered, code_nil, values, List.map_nil, List.nil_append, List.append_nil] using inside
    · simp [configAt, after_arm_render, MemoryWrite.limeActivationCode, List.append_assoc]
  | @child parent child bytes written args stack phase next rest move ih =>
    obtain ⟨_, found, childAllocated, childActive, childReady, _, _, _⟩ := ready
    have inside := ih (caller := parent.fn.declaration.frame args) (saved := stack) (tail := code rest)
      found childAllocated rfl childReady live
    simpa only [configAt, renderUnder, frameCode, after_child_render, List.append_assoc, List.singleton_append] using
      Step.context (.frame (.label inside types.length [])
        types.length caller) saved tail
  | @erase callee bytes args stack kept removed before cut rest split suffix active =>
    have nonempty : stack ≠ [] ∨ before ≠ [] := by
      rcases active with removed | cut
      · exact .inl (fun h => removed ((List.append_eq_nil_iff.mp (split.symm.trans h)).2))
      · exact .inr (fun h => cut ((List.append_eq_nil_iff.mp (suffix.symm.trans h)).1))
    exact Step.of_internal ((erase_iff nonempty).mpr ⟨kept, _, _, rest, split, suffix, active, rfl⟩)
  | @labelDone callee bytes args vs =>
    apply Step.of_internal
    change Step CallFrame.limeNoHost _ _
    simpa [configAt, renderUnder, frameCode, result, MemoryWrite.limeActivationCode, List.append_assoc] using
      (leave_label_iff (args := args) (out := .values vs) (bytes := bytes) (mem := mem) (caller := caller)
        (callee := callee) (saved := saved) (tail := tail) (arity := types.length)).mpr rfl
  | @labelTrap callee bytes args =>
    apply Step.of_internal
    change Step CallFrame.limeNoHost _ _
    simpa [configAt, renderUnder, frameCode, result, MemoryWrite.limeActivationCode, values, List.append_assoc] using
      (leave_label_iff (args := args) (out := .trap) (bytes := bytes) (mem := mem) (caller := caller)
        (callee := callee) (saved := saved) (tail := tail) (arity := types.length)).mpr rfl
  | frameDone => exact Step.of_internal ((leave_frame_iff rfl ready.2).mpr rfl)

theorem step_iff {phase : Phase H} (linked : site.MemoryLinked mem host .recursive)
    (registered : site.memoryLookup callee.address = some callee.fn) (allocated : callee.Allocated base)
    (ready : Ready mem host site callee phase) (live : mem.Live bytes) (notDone : ∀ out, phase ≠ .done out) :
    Step host (config mem caller saved tail callee bytes phase) dst ↔
      ∃ written next, Edge mem host site callee bytes phase written next ∧
        dst = config mem caller saved tail callee written next := by
  constructor
  · exact read linked registered allocated rfl ready live notDone (entry_not_lowered ready)
  · rintro ⟨_, _, edge, eq⟩
    subst dst
    exact sound linked registered allocated rfl ready live edge

theorem frame_result_iff {args payload : List Value} (typed : payload.map Value.type = callee.fn.declaration.results) :
    Step host (config mem caller saved tail callee bytes (.exit args (.values payload))) dst ↔
      dst = ⟨mem.store bytes, caller, values (saved ++ payload) ++ tail⟩ := by
  have exits := leave_frame_iff (mem := mem) (bytes := bytes) (caller := caller) (callee := callee)
    (saved := saved) (tail := tail) (dst := dst) (args := args) (out := .values payload)
    (types := callee.fn.declaration.results) rfl typed
  constructor
  · intro step
    have internal := internal_of_absent (by simp [decompose?, configAt, renderUnder, frameCode, result]) step
    simpa [configAt, renderUnder, result, values_append, List.append_assoc] using exits.mp internal
  · intro same
    exact Step.of_internal (exits.mpr (by
      simpa [configAt, renderUnder, result, values_append, List.append_assoc] using same))

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1.MemoryCallee.Proofs

module

public import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Memory.Callee.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.HostCall.Lime1.Memory.Callee.Preservation
import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Memory.Thms
import Silmaril.Wasm.Institution.Operational.MemoryWrite.Native.Lime1Context.Thms
import Silmaril.Wasm.Institution.Operational.MemoryQuery.Thms
import Silmaril.Wasm.Institution.Operational.MemoryWrite.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Native.Thms
import Silmaril.Wasm.Lime1.Execution.Callout.Properties

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.HostCall.Lime1.MemoryCallee.Proofs

open Execution.Runtime (Frame Result Value)
open Wasm.Lime1.Execution
open CallContinuation
open CallContinuation.OuterCall (Declaration)
open CallContinuation.OuterCall.Ranked
open CallContinuation.OuterCall.Computed

set_option backward.isDefEq.respectTransparency false

variable {H : Type} {base : Store H} {mem : Memory32 base} {callee : MemoryTarget}
  {caller : Frame} {saved : List Value} {tail : List Admin} {bytes : ByteArray} {dst : Config H}

local notation "resultCount" => callee.fn.declaration.results.length
local notation "cfg" => config mem caller saved tail callee

@[simp] private theorem code_nil : code [] = [] := rfl

@[simp] private theorem code_cons (op : Graph.Memory32.Op) (ops : List Graph.Memory32.Op) :
    code (op :: ops) = .source op.v1.toLime :: code ops := rfl

private theorem enter_iff {args : List Value} (allocated : callee.Allocated base)
    (typed : args.map Value.type = callee.fn.declaration.params) :
    Step CallFrame.limeNoHost (cfg bytes (.invoke args)) dst ↔ dst = cfg bytes (.body args callee.fn.initial callee.fn.code) := by
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
      (by simpa only [config, render, values_append, List.append_assoc, List.singleton_append] using move)
    obtain rfl := exactInvoke.mp invoked
    simp [config, render, Declaration.frame, Declaration.type, MemoryTarget.code, Graph.Memory32.Function.v1Func, Wasm.V1.Func.toLime, ← body]
  · rintro rfl
    have step := exactInvoke.mpr rfl
    have locals : callee.code.locals = callee.fn.declaration.locals := rfl
    rw [body, locals] at step
    simpa [config, render, values, List.append_assoc, Declaration.frame, Declaration.type] using
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
      simpa only [config, render, result, MemoryWrite.limeActivationCode, List.append_assoc, List.singleton_append] using
        Step.context (Step.frame (Step.pure (host := CallFrame.limeNoHost) (mem.store bytes)
          (callee.fn.declaration.frame args) (.labelDone resultCount [] vs)) resultCount caller) saved tail
    | trap =>
      simpa only [config, render, result, MemoryWrite.limeActivationCode, List.append_assoc, List.singleton_append] using
        Step.context (Step.frame (Step.pure (host := CallFrame.limeNoHost) (mem.store bytes)
          (callee.fn.declaration.frame args) (.labelTrap resultCount [])) resultCount caller) saved tail

private theorem leave_frame_iff {args : List Value} {out : Result} (typed : resultTyped callee out) :
    Step CallFrame.limeNoHost (cfg bytes (.exit args out)) dst ↔ dst = cfg bytes (.done out) := by
  constructor
  · intro move
    obtain ⟨mid, step, rfl⟩ := CallContinuation.lime_frame_context_inv
      (by simpa only [config, render, List.append_assoc, List.singleton_append] using move)
    cases out with
    | values vs => obtain rfl := Nested.lime_frame_result (r := .values vs) step; rfl
    | trap => obtain rfl := Nested.lime_frame_result (r := .trap) step; rfl
  · rintro rfl
    cases out with
    | values vs =>
      have count : vs.length = resultCount := by simpa using congrArg List.length typed
      exact Step.context (.pure _ _ (.frameDone resultCount (callee.fn.declaration.frame args) vs count)) saved tail
    | trap => exact Step.context (.pure _ _ (.frameTrap resultCount (callee.fn.declaration.frame args))) saved tail

private theorem get_iff {args stack : List Value} {index : LocalIdx} {ops : List Graph.Memory32.Op}
    {v : Value} (found : (callee.fn.declaration.frame args).locals[index.toNat]? = some v) :
    Step CallFrame.limeNoHost (cfg bytes (.body args stack (.ranked (.numeric (.get index)) :: ops))) dst ↔
      dst = cfg bytes (.body args (stack ++ [v]) ops) := by
  rw [show cfg bytes (.body args stack (.ranked (.numeric (.get index)) :: ops)) =
      ⟨mem.store bytes, caller, MemoryWrite.limeActivationCode resultCount (callee.fn.declaration.frame args)
        saved tail (values stack ++ .source (.localGet index) :: code ops)⟩ from by
    simp only [config, render, code_cons, MemoryWrite.limeActivationCode, List.append_assoc, List.singleton_append]
    rfl]
  rw [body_iff (fun _ => lime_label_stays rfl (by simp) (by simp) (by simp))]
  constructor
  · rintro ⟨mid, step, rfl⟩
    obtain rfl := (lime_local_get_iff found).mp step
    simp [config, render, MemoryWrite.limeActivationCode, values, List.append_assoc]
  · rintro rfl
    exact ⟨_, (lime_local_get_iff found).mpr rfl, by
      simp [config, render, MemoryWrite.limeActivationCode, values, List.append_assoc]⟩

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
    simp only [config, render, code_cons, MemoryWrite.limeActivationCode, MemoryQuery.limeCodeAt,
      values_append, List.append_assoc, List.singleton_append]
    rfl]
  rw [access]
  constructor
  · rintro ⟨out, edge, rfl⟩
    cases out with
    | value bits =>
      exact .inl ⟨bits, edge, by
        simp [config, render, values, MemoryWrite.limeActivationCode, MemoryQuery.limeCodeAt,
          value, Value.int, List.append_assoc]⟩
    | trap =>
      exact .inr ⟨edge, by simp [config, render, MemoryWrite.limeActivationCode, MemoryQuery.limeCodeAt,
        List.append_assoc]⟩
    | size | load => cases MemoryQuery.invert_at edge
  · rintro (⟨bits, edge, rfl⟩ | ⟨edge, rfl⟩)
    · exact ⟨.value bits, edge, by simp [config, render, MemoryWrite.limeActivationCode,
        MemoryQuery.limeCodeAt, values, value, Value.int, List.append_assoc]⟩
    · exact ⟨.trap, edge, by simp [config, render, MemoryWrite.limeActivationCode, MemoryQuery.limeCodeAt,
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
  simpa [config, render, Graph.Memory32.Op.v1, Wasm.V1.Instr.toLime, MemoryWrite.limeActivationCode,
    MemoryWrite.limeConfigAt, value, Value.int, values, List.append_assoc, arg, Graph.Memory32.immediate] using access

private theorem erase_iff {args stack : List Value} {rest : List Admin} (active : stack ≠ [] ∨ rest ≠ []) :
    Step CallFrame.limeNoHost (cfg bytes (.trapped args stack rest)) dst ↔
      ∃ kept removed cut after, stack = kept ++ removed ∧ rest = cut ++ after ∧
        (removed ≠ [] ∨ cut ≠ []) ∧ dst = cfg bytes (.trapped args kept after) := by
  rw [show cfg bytes (.trapped args stack rest) =
      ⟨mem.store bytes, caller, MemoryWrite.limeActivationCode resultCount (callee.fn.declaration.frame args)
        saved tail (values stack ++ .trap :: rest)⟩ from by
    simp [config, render, MemoryWrite.limeActivationCode, List.append_assoc]]
  rw [body_iff (fun _ => lime_label_stays rfl (by simp) (by simp) (fun _ => active))]
  constructor
  · rintro ⟨mid, step, rfl⟩
    obtain ⟨kept, removed, cut, after, split, suffix, nonempty, rfl⟩ := lime_trap_front_iff.mp step
    exact ⟨kept, removed, cut, after, split, suffix, nonempty,
      by simp [config, render, MemoryWrite.limeActivationCode, List.append_assoc]⟩
  · rintro ⟨kept, removed, cut, after, split, suffix, nonempty, rfl⟩
    exact ⟨_, lime_trap_front_iff.mpr ⟨kept, removed, cut, after, split, suffix, nonempty, rfl⟩,
      by simp [config, render, MemoryWrite.limeActivationCode, List.append_assoc]⟩

private theorem read {phase : Phase} (checked : callee.Checked mem) (allocated : callee.Allocated base)
    (ready : Ready callee phase) (live : mem.Live bytes) (notDone : ∀ out, phase ≠ .done out)
    (move : Step CallFrame.limeNoHost (cfg bytes phase) dst) :
    ∃ nextBytes next, Edge callee bytes phase nextBytes next ∧ dst = cfg nextBytes next := by
  cases phase with
  | invoke args => exact ⟨_, _, .enter, (enter_iff allocated ready).mp move⟩
  | body args stack ops =>
    cases ops with
    | nil =>
      have step := leave_label_iff (args := args) (out := .values stack)
        (mem := mem) (callee := callee) (bytes := bytes) (caller := caller) (saved := saved) (tail := tail) (dst := dst)
      exact ⟨_, _, .labelDone, step.mp (by simpa [config, render, MemoryWrite.limeActivationCode, result,
        List.append_assoc] using move)⟩
    | cons op ops =>
      have supported := List.all_eq_true.mp ready.2.1 op (List.mem_cons_self ..)
      cases op with
      | load offset =>
        obtain ⟨stack, ptr, rfl, _⟩ := Graph.Memory32.Function.load_typed ready.2.2
        rcases (load_iff checked).mp move with ⟨bits, edge, eq⟩ | ⟨edge, eq⟩
        · exact ⟨_, _, .load edge, eq⟩
        · exact ⟨_, _, .loadTrap edge, eq⟩
      | store offset =>
        obtain ⟨stack, ptr, word, rfl, _⟩ := Graph.Memory32.Function.store_typed ready.2.2
        rcases (store_iff checked live).mp move with ⟨written, edge, _, eq⟩ | ⟨edge, eq⟩
        · exact ⟨_, _, .store edge, eq⟩
        · exact ⟨_, _, .storeTrap edge, eq⟩
      | ranked op =>
        cases op with
        | numeric op =>
          cases op with
          | get index =>
            obtain ⟨v, found, _⟩ := get_typed ready.1 ready.2.2
            exact ⟨_, _, .get found, (get_iff found).mp move⟩
          | bin => contradiction
        | _ => contradiction
      | _ => contradiction
  | trapped args stack rest =>
    by_cases active : stack ≠ [] ∨ rest ≠ []
    · obtain ⟨kept, removed, cut, after, split, suffix, nonempty, eq⟩ := (erase_iff active).mp move
      exact ⟨_, _, .erase split suffix nonempty, eq⟩
    · obtain ⟨stackNil, restNil⟩ := not_or.mp active
      have : stack = [] := not_not.mp stackNil
      have : rest = [] := not_not.mp restNil
      subst stack rest
      have step := leave_label_iff (args := args) (out := .trap)
        (mem := mem) (callee := callee) (bytes := bytes) (caller := caller) (saved := saved) (tail := tail) (dst := dst)
      exact ⟨_, _, .labelTrap, step.mp (by simpa [config, render, MemoryWrite.limeActivationCode, result,
        values, List.append_assoc] using move)⟩
  | exit args out => exact ⟨_, _, .frameDone, (leave_frame_iff ready.2).mp move⟩
  | done out => exact (notDone out rfl).elim

private theorem sound {phase next : Phase} {written : ByteArray} (checked : callee.Checked mem)
    (allocated : callee.Allocated base) (ready : Ready callee phase) (live : mem.Live bytes)
    (move : Edge callee bytes phase written next) : Step CallFrame.limeNoHost (cfg bytes phase) (cfg written next) := by
  cases move with
  | enter => exact (enter_iff allocated ready).mpr rfl
  | get found => exact (get_iff found).mpr rfl
  | load edge => exact (load_iff checked).mpr (.inl ⟨_, edge, rfl⟩)
  | loadTrap edge => exact (load_iff checked).mpr (.inr ⟨edge, rfl⟩)
  | store edge =>
    have size : written.size = bytes.size := MemoryWrite.closed_at edge
    exact (store_iff checked live).mpr (.inl ⟨_, edge, size.trans live, rfl⟩)
  | storeTrap edge => exact (store_iff checked live).mpr (.inr ⟨edge, rfl⟩)
  | @erase args stack kept removed before cut rest split suffix active =>
    have nonempty : stack ≠ [] ∨ before ≠ [] := by
      rcases active with removed | cut
      · exact .inl (fun h => removed ((List.append_eq_nil_iff.mp (split.symm.trans h)).2))
      · exact .inr (fun h => cut ((List.append_eq_nil_iff.mp (suffix.symm.trans h)).1))
    exact (erase_iff nonempty).mpr ⟨kept, _, _, rest, split, suffix, active, rfl⟩
  | @labelDone args vs =>
    simpa [config, render, result, MemoryWrite.limeActivationCode, List.append_assoc] using
      (leave_label_iff (args := args) (out := .values vs) (bytes := bytes) (mem := mem) (caller := caller)
        (callee := callee) (saved := saved) (tail := tail)).mpr rfl
  | @labelTrap args =>
    simpa [config, render, result, MemoryWrite.limeActivationCode, values, List.append_assoc] using
      (leave_label_iff (args := args) (out := .trap) (bytes := bytes) (mem := mem) (caller := caller)
        (callee := callee) (saved := saved) (tail := tail)).mpr rfl
  | frameDone => exact (leave_frame_iff ready.2).mpr rfl

theorem step_iff {phase : Phase} (checked : callee.Checked mem) (allocated : callee.Allocated base)
    (ready : Ready callee phase) (live : mem.Live bytes) (notDone : ∀ out, phase ≠ .done out) :
    Step CallFrame.limeNoHost (cfg bytes phase) dst ↔
      ∃ written next, Edge callee bytes phase written next ∧ dst = cfg written next :=
  ⟨read checked allocated ready live notDone, fun ⟨_, _, edge, eq⟩ => eq.symm ▸ sound checked allocated ready live edge⟩

private theorem code_absent (s : Store H) (ops : List Graph.Memory32.Op) (stack : List Value) :
    Execution.Runtime.decomposeFrom? coding s stack (code ops) = none := by
  induction ops generalizing stack with
  | nil => rfl
  | cons op rest ih =>
    change Execution.Runtime.decomposeFrom? coding s stack (.source op.v1.toLime :: code rest) = none
    rw [decomposeFrom?_source_cons]
    cases asValue? (.source op.v1.toLime) <;> simp [ih]

theorem absent {phase : Phase} (s : Store H) (allocated : callee.Allocated s)
    (notDone : ∀ out, phase ≠ .done out) :
    Execution.Runtime.decomposeFrom? coding s [] (values saved ++ render callee phase ++ tail) = none := by
  cases phase with
  | invoke =>
    unfold MemoryTarget.Allocated at allocated
    simp [render, List.append_assoc, decomposeFrom?_invoke_cons, Execution.Runtime.decomposeHead?, allocated]
  | body _ _ ops => simp [render, List.append_assoc, code_absent]
  | trapped => simp [render]
  | exit _ out => cases out <;> simp [render, result]
  | done out => exact (notDone out rfl).elim

theorem stays {phase : Phase} (notDone : ∀ out, phase ≠ .done out)
    {types : List Wasm.Lime1.FuncType} {n : Nat} {cont : Wasm.Lime1.Expr} {out : List Admin} :
    ¬ PureStep types [.label n cont (values saved ++ render callee phase ++ tail)] out := by
  have frameStays {k : Nat} {fr : Frame} {body : List Admin} :
      ¬ PureStep types [.label n cont (values saved ++ .frame k fr body :: tail)] out :=
    lime_label_stays rfl (by simp) (by simp) (by simp)
  cases phase with
  | invoke args =>
    simpa only [render, values_append, List.append_assoc, List.singleton_append] using
      (lime_label_stays (types := types) (n := n) (cont := cont) (out := out)
        (stack := saved ++ args) (head := .invoke callee.address) (rest := tail) rfl
        (by simp) (by simp) (by simp))
  | body | trapped | exit => simpa only [render, List.append_assoc, List.singleton_append] using frameStays
  | done out => exact (notDone out rfl).elim

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1.MemoryCallee.Proofs

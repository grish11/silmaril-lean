module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Defs
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Guard
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.Native.Thms
import Silmaril.Wasm.Versions.Lime1.Execution.Thms
import Silmaril.Wasm.Institution.Operational.MemoryQuery.Native.Thms
import Silmaril.Wasm.Institution.Operational.MemoryWrite.Native.Thms
import Silmaril.Wasm.Institution.Operational.MemoryGrow.Native.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.RunProofs

open Execution.Runtime (Frame FuncAddr MemAddr MemInst ModuleInst Value)
open Wasm.V1.Execution

private theorem selected {H : Type} {p : Program} {base : Store H} {m : MemAddr} {initial : MemInst}
    (layout : Layout p base m initial) {f : Frame} (slot : f.module.memories[0]? = some m) (bytes : ByteArray) :
    frameMemory (storeWithBytes base m initial bytes) f = some (m, { initial with data := bytes }) := by
  have before : frameMemory base f = some (m, initial) := by
    simp [frameMemory, slot, layout.memory]
  exact MemoryWrite.v1_frameMemory_setBytes before bytes

private theorem update_bytes {H : Type} (base : Store H) (m : MemAddr) (initial : MemInst)
    (before after : ByteArray) :
    setMemory (storeWithBytes base m initial before) m { initial with data := after } =
      storeWithBytes base m initial after := by
  simp [storeWithBytes, setMemory, List.set_set]

theorem enter_rendered {H : Type} {p : Program} {m : MemAddr} {base : Store H} {initial : MemInst}
    (layout : Layout p base m initial) {address : FuncAddr} {fn : Function}
    (found : p.lookup address = some fn) (arity : fn.declaration.results.length ≤ 1)
    {suspended : Frame} {bytes : ByteArray} {args : List Value}
    (count : args.length = fn.declaration.params.length) :
    Step CallFrame.v1NoHost (render base m initial ⟨bytes, suspended, values args ++ [.invoke address]⟩)
      (render base m initial ⟨bytes, suspended, [.frame fn.declaration.results.length (fn.declaration.frame args)
        [.label fn.declaration.results.length [] (expression fn.v1Func.body)]]⟩) :=
  .invokeWasm _ _ address fn.declaration.type fn.declaration.module fn.v1Func args
    (layout.functions address fn found) count arity

theorem sound {H : Type} {mode : MemoryMode} {calls : CallMode} {p : Program} {m : MemAddr} {base : Store H} {initial : MemInst}
    (checked : p.checkV1 m mode calls = true) (layout : Layout p base m initial)
    (matched : mode.matches initial) {src dst : State}
    (move : EdgeAt mode p m src dst) :
    Step CallFrame.v1NoHost (render base m initial src) (render base m initial dst) := by
  induction move with
  | pure move => exact .pure _ _ move
  | context move saved tail ih => exact .context ih saved tail
  | label move n ih => exact .label ih n []
  | underLoop result body move ih => exact .label ih 0 [.loop result body]
  | frame move n outer ih => exact .frame ih n outer
  | get found => exact .localGet _ _ _ _ found
  | set found => exact .localSet _ _ _ _ _ found
  | resolve found => exact .call _ _ _ _ found
  | enter found count => exact enter_rendered layout found (p.function_checked checked found).1 count
  | load slot rule =>
    exact (MemoryWrite.v1_context_load_step_iff_at (saved := []) (tail := []) (selected layout slot _)).mpr
      ⟨_, rule, by simp [render, values]⟩
  | store slot rule =>
    have native := (MemoryWrite.v1_context_store_step_iff_at (host := CallFrame.v1NoHost) (saved := []) (tail := [])
      (selected layout slot _)).mpr ⟨_, rule, rfl⟩
    simpa [render, MemoryWrite.v1ConfigAt, values, update_bytes, value, Value.int] using native
  | storeTrap slot rule =>
    exact (MemoryWrite.v1_context_store_step_iff_at (saved := []) (tail := [])
      (selected layout slot _)).mpr ⟨_, rule, rfl⟩

  | size _ slot => exact .memorySize _ _ _ _ (selected layout slot _)
  | @grow bytes f maximum delta grown enabled slot rule =>
    have limit : initial.max = maximum := by simpa only [enabled, MemoryMode.matches] using matched
    have compatible : MemoryGrow.Edge { initial with data := bytes } (.request delta) (.grown grown) := by
      cases initial
      cases limit
      exact rule
    have native := MemoryGrow.v1_sound (host := CallFrame.v1NoHost) (selected layout slot bytes) compatible
    simpa only [MemoryGrow.v1Config, render, update_bytes] using! native
  | @growFail bytes _ _ delta _ slot =>
    exact MemoryGrow.v1_sound (selected layout slot bytes) (MemoryGrow.fact (.fail delta))

private theorem reflect_load {H : Type} {mode : MemoryMode} {p : Program} {m : MemAddr} {base : Store H}
    {initial : MemInst} (layout : Layout p base m initial)
    {bytes : ByteArray} {f : Frame} {arg : Wasm.V1.MemArg} {ptr : BitVec 32} {dst : Config H}
    (slot : f.module.memories[0]? = some m)
    (move : Step CallFrame.v1NoHost
      (render base m initial ⟨bytes, f, MemoryQuery.v1CodeAt arg (.load ptr)⟩) dst) :
    ∃ out, EdgeAt mode p m ⟨bytes, f, MemoryQuery.v1CodeAt arg (.load ptr)⟩ out ∧
      dst = render base m initial out := by
  obtain ⟨out, edge, eq⟩ := (MemoryWrite.v1_context_load_step_iff_at (saved := []) (tail := [])
    (selected layout slot _)).mp move
  exact ⟨_, .load slot edge, by simpa [render, values] using eq⟩

private theorem reflect_store {H : Type} {mode : MemoryMode} {p : Program} {m : MemAddr} {base : Store H}
    {initial : MemInst} (layout : Layout p base m initial)
    {bytes : ByteArray} {f : Frame} {arg : Wasm.V1.MemArg} {ptr word : BitVec 32} {dst : Config H}
    (slot : f.module.memories[0]? = some m)
    (move : Step CallFrame.v1NoHost (render base m initial ⟨bytes, f,
      [value (.int .i32 ptr), value (.int .i32 word), .source (.intStore .i32 none arg)]⟩) dst) :
    ∃ out, EdgeAt mode p m ⟨bytes, f,
      [value (.int .i32 ptr), value (.int .i32 word), .source (.intStore .i32 none arg)]⟩ out ∧
      dst = render base m initial out := by
  obtain ⟨out, edge, eq⟩ := (MemoryWrite.v1_context_store_step_iff_at (saved := []) (tail := [])
    (immediate := arg) (address := ptr) (word := word) (selected layout slot _)).mp move
  cases MemoryWrite.invert_at edge with
  | write => exact ⟨_, .store slot edge, by simpa [render, MemoryWrite.v1ConfigAt, values, update_bytes] using eq⟩
  | trap => exact ⟨_, .storeTrap slot edge, eq⟩

private theorem source_last {mode : MemoryMode} {calls : CallMode} {p : Program} {m : MemAddr} {rank : Nat} {mod : ModuleInst}
    {code : List Admin} {op : Wasm.V1.Instr}
    (guard : CodeAllowedFor mode p m calls rank mod code) (last : code.getLast? = some (.source op)) :
    SourceAllowedFor mode p m calls rank mod op :=
  source_allowed (guard _ (List.mem_of_getLast? last))

theorem readback {H : Type} {mode : MemoryMode} {calls : CallMode} {p : Program} {m : MemAddr} {base : Store H} {initial : MemInst}
    (layout : Layout p base m initial) (matched : mode.matches initial) {src dst : Config H} (move : Step CallFrame.v1NoHost src dst)
    (bytes : ByteArray) (same : src.store = storeWithBytes base m initial bytes)
    {rank : Nat} (ready : CodeAllowedFor mode p m calls rank src.frame.module src.code) :
    ∃ out, EdgeAt mode p m ⟨bytes, src.frame, src.code⟩ out ∧ dst = render base m initial out := by
  induction move generalizing bytes rank with
  | pure s f move => exact ⟨_, .pure move, by simp [render, ← same]⟩
  | @context s t f g before after move saved tail ih =>
    have leading := ((append_allowed (l := values saved ++ before) (r := tail)).mp ready).1
    have inside := ((append_allowed (l := values saved) (r := before)).mp leading).2
    obtain ⟨next, rule, eq⟩ := ih bytes same inside
    exact ⟨_, .context rule saved tail, congrArg
      (fun c : Config H => (⟨c.store, c.frame, values saved ++ c.code ++ tail⟩ : Config H)) eq⟩
  | label move n cont ih =>
    have guard := single_allowed.mp ready
    cases guard with
    | label _ inside =>
      obtain ⟨next, rule, eq⟩ := ih bytes same inside
      exact ⟨_, .label rule n, congrArg
        (fun c : Config H => (⟨c.store, c.frame, [.label n [] c.code]⟩ : Config H)) eq⟩
    | @loopLabel _ _ result body _ restart inside =>
      obtain ⟨next, rule, eq⟩ := ih bytes same inside
      exact ⟨_, .underLoop result body rule, congrArg
        (fun c : Config H => (⟨c.store, c.frame, [.label 0 [.loop result body] c.code]⟩ : Config H)) eq⟩
  | frame move n outer ih =>
    have guard := single_allowed.mp ready
    cases guard with | frame found permitted scope arity inside =>
      obtain ⟨next, rule, eq⟩ := ih bytes same inside
      exact ⟨_, .frame rule n outer, congrArg
        (fun c : Config H => (⟨c.store, outer, [.frame n c.frame c.code]⟩ : Config H)) eq⟩
  | localGet s f i v found => exact ⟨_, .get found, by simp [render, ← same]⟩
  | localSet s f i v old found => exact ⟨_, .set found, by simp [render, ← same]⟩
  | call s f i address found => exact ⟨_, .resolve found, by simp [render, ← same]⟩
  | invokeWasm s f address ty mod fn args found count arity =>
    have guard := single_allowed.mp (append_allowed.mp ready).2
    cases guard with
    | invoke declared permitted =>
      change s = storeWithBytes base m initial bytes at same
      rw [same] at found
      change base.funcs[address.value]? = some (.wasm ty mod fn) at found
      rw [layout.functions address _ declared] at found
      obtain ⟨rfl, rfl, rfl⟩ := Execution.Runtime.FuncInst.wasm.inj (Option.some.inj found)
      exact ⟨_, .enter declared count, by simp [render, ← same, Declaration.frame, Function.v1Func, Declaration.type]⟩
  | invokeHost s t f address ty fn args r found count behavior => cases behavior
  | invokeHostDiverges s f address ty fn args found count behavior => cases behavior
  | intLoad s f t packed arg ptr a mem v found loaded =>
    have guard := source_last ready (op := .intLoad t packed arg) rfl
    cases guard with | load offset slot =>
      change s = storeWithBytes base m initial bytes at same
      change f.module.memories[0]? = some m at slot
      have foundNow := selected layout slot bytes
      rw [same, foundNow] at found
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj found)
      subst s
      exact reflect_load layout slot (.intLoad _ _ _ _ _ _ _ _ _ foundNow loaded)
  | intLoadTrap s f t packed arg ptr a mem found loaded =>
    have guard := source_last ready (op := .intLoad t packed arg) rfl
    cases guard with | load offset slot =>
      change s = storeWithBytes base m initial bytes at same
      change f.module.memories[0]? = some m at slot
      have foundNow := selected layout slot bytes
      rw [same, foundNow] at found
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj found)
      subst s
      exact reflect_load layout slot (.intLoadTrap _ _ _ _ _ _ _ _ foundNow loaded)
  | intStore s f t packed arg ptr word a mem written found stored =>
    have guard := source_last ready (op := .intStore t packed arg) rfl
    cases guard with | store offset slot =>
      change s = storeWithBytes base m initial bytes at same
      change f.module.memories[0]? = some m at slot
      have foundNow := selected layout slot bytes
      rw [same, foundNow] at found
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj found)
      subst s
      exact reflect_store layout slot (.intStore _ _ _ _ _ _ _ _ _ _ foundNow stored)
  | intStoreTrap s f t packed arg ptr word a mem found stored =>
    have guard := source_last ready (op := .intStore t packed arg) rfl
    cases guard with | store offset slot =>
      change s = storeWithBytes base m initial bytes at same
      change f.module.memories[0]? = some m at slot
      have foundNow := selected layout slot bytes
      rw [same, foundNow] at found
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj found)
      subst s
      exact reflect_store layout slot (.intStoreTrap _ _ _ _ _ _ _ _ _ foundNow stored)
  | memorySize s f a mem found =>
    have guard := source_allowed (single_allowed.mp ready)
    cases guard with | memorySize enabled slot =>
      change s = storeWithBytes base m initial bytes at same
      have foundNow := selected layout slot bytes
      rw [same, foundNow] at found
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj found)
      exact ⟨_, .size enabled slot, by simp only [render, ← same]; rfl⟩
  | memoryGrow s f a mem delta r out found grown =>
    have guard := source_last ready (op := .memoryGrow) rfl
    cases guard with | @memoryGrow maximum enabled slot =>
      change s = storeWithBytes base m initial bytes at same
      have foundNow := selected layout slot bytes
      rw [same, foundNow] at found
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj found)
      have limit : initial.max = maximum := by simpa only [enabled, MemoryMode.matches] using matched
      cases grown with
      | success _ ok =>
        have grew : Execution.Memory.grow? bytes maximum delta.toNat = some out := by
          simpa only [limit] using ok
        exact ⟨_, .grow enabled slot (MemoryGrow.fact (.grow delta _ grew)),
          by simp only [render, same, update_bytes]; rfl⟩
      | failure =>
        exact ⟨_, .growFail enabled slot, by simp only [render, same, update_bytes]; rfl⟩
  | _ =>
    have guard := source_last ready rfl
    cases guard

theorem initial_store {H : Type} {p : Program} {m : MemAddr} {base : Store H} {initial : MemInst}
    (layout : Layout p base m initial) :
    storeWithBytes base m initial initial.data = base := by
  obtain ⟨_, allocated⟩ := List.getElem?_eq_some_iff.mp layout.memory
  change setMemory base m initial = base
  unfold setMemory
  rw [← allocated, List.set_getElem_self]

theorem step_iff {H : Type} {mode : MemoryMode} {calls : CallMode} {p : Program} {m : MemAddr} {base : Store H} {initial : MemInst}
    (checked : p.checkV1 m mode calls = true) (layout : Layout p base m initial) (matched : mode.matches initial) {src : State} {rank : Nat}
    (ready : ReadyFor mode p m calls rank initial.data.size src) {dst : Config H} :
    Step CallFrame.v1NoHost (render base m initial src) dst ↔
      ∃ out, EdgeAt mode p m src out ∧ ReadyFor mode p m calls rank initial.data.size out ∧ dst = render base m initial out := by
  constructor
  · intro step
    obtain ⟨out, edge, eq⟩ := readback layout matched step src.bytes rfl ready.2
    exact ⟨out, edge, ⟨extent_preserved edge ready.1, preserve checked edge ready.2⟩, eq⟩
  · rintro ⟨out, edge, _, rfl⟩
    exact sound checked layout matched edge

theorem run_iff {H : Type} {mode : MemoryMode} {calls : CallMode} {p : Program} {m : MemAddr} {base : Store H} {initial : MemInst}
    (checked : p.checkV1 m mode calls = true) (layout : Layout p base m initial) (matched : mode.matches initial) {src : State} {rank : Nat}
    (ready : ReadyFor mode p m calls rank initial.data.size src) {dst : Config H} :
    Steps CallFrame.v1NoHost (render base m initial src) dst ↔
      ∃ out, RunsAt mode p m src out ∧ ReadyFor mode p m calls rank initial.data.size out ∧ dst = render base m initial out := by
  constructor
  · intro run
    induction run with
    | refl => exact ⟨src, .refl, ready, rfl⟩
    | tail _ step ih =>
      obtain ⟨middle, trace, guarded, rfl⟩ := ih
      obtain ⟨next, edge, nextGuarded, eq⟩ := (step_iff checked layout matched guarded).mp step
      exact ⟨next, trace.tail edge, nextGuarded, eq⟩
  · rintro ⟨out, trace, _, rfl⟩
    exact Relation.ReflTransGen.lift (render base m initial) (fun _ _ h => sound checked layout matched h) _ _ trace

theorem loop_restart {H : Type} {s : Store H} {f : Frame} {result : Option NumType}
    {body : Wasm.V1.Expr} {saved scratch : List Value} {branchTail tail : List Admin} :
    let loop := Wasm.V1.Instr.loop result body
    let pending := (⟨s, f, values saved ++ [.source loop] ++ tail⟩ : Config H)
    Step CallFrame.v1NoHost
      ⟨s, f, values saved ++ [.label 0 [loop] (values scratch ++ [.source (.br ⟨0⟩)] ++ branchTail)] ++ tail⟩ pending ∧
    Step CallFrame.v1NoHost pending ⟨s, f, values saved ++ [.label 0 [loop] (expression body)] ++ tail⟩ := by
  constructor
  · simpa only [values, expression, List.map_nil, List.map_cons, List.append_nil, List.nil_append] using
      Step.context (Step.pure (host := CallFrame.v1NoHost) s f
        (.labelBranch 0 [.loop result body] scratch [] branchTail rfl)) saved tail
  · exact .context (.pure _ _ (.loop result body)) saved tail

theorem function_branch_exit {H : Type} {s : Store H} {caller callee : Frame}
    {saved extra payload : List Value} {bodyTail callerTail : List Admin} {results : List NumType}
    (typed : payload.map Value.type = results) :
    let arity := results.length
    let done := ⟨s, caller, values saved ++ [.frame arity callee (values payload)] ++ callerTail⟩
    Step CallFrame.v1NoHost
      ⟨s, caller, values saved ++ [.frame arity callee [.label arity []
        (values extra ++ values payload ++ [.source (.br ⟨0⟩)] ++ bodyTail)]] ++ callerTail⟩ done ∧
    Step CallFrame.v1NoHost done ⟨s, caller, values saved ++ values payload ++ callerTail⟩ := by
  have arity : payload.length = results.length := by simpa using congrArg List.length typed
  constructor
  · simpa only [expression, List.map_nil, List.append_nil] using
      Step.context (Step.frame (Step.pure (host := CallFrame.v1NoHost) s callee
        (.labelBranch results.length [] extra payload bodyTail arity)) results.length caller) saved callerTail
  · exact .context (.pure _ _ (.frameDone _ callee payload arity)) saved callerTail

theorem function_fallthrough {H : Type} {s : Store H} {caller callee : Frame}
    {saved payload : List Value} {tail : List Admin} {arity : Nat} (count : payload.length = arity) :
    let done := (⟨s, caller, values saved ++ [.frame arity callee (values payload)] ++ tail⟩ : Config H)
    Step CallFrame.v1NoHost
      ⟨s, caller, values saved ++ [.frame arity callee [.label arity [] (values payload)]] ++ tail⟩ done ∧
    Step CallFrame.v1NoHost done ⟨s, caller, values saved ++ values payload ++ tail⟩ :=
  ⟨.context (.frame (.pure _ _ (.labelDone arity [] payload)) arity caller) saved tail,
    .context (.pure _ _ (.frameDone arity callee payload count)) saved tail⟩

theorem br_table_select_iff {H : Type} {s : Store H} {f : Frame} {saved : List Value}
    {selector : BitVec 32} {depths : List LabelIdx} {fallback : LabelIdx} {tail : List Admin} {dst : Config H} :
    Step CallFrame.v1NoHost
      ⟨s, f, values (saved ++ [Value.int .i32 selector]) ++ .source (.brTable depths fallback) :: tail⟩ dst ↔
    dst = ⟨s, f, values saved ++ .source (.br (depths[selector.toNat]?.getD fallback)) :: tail⟩ := by
  constructor
  · intro move
    have projected := move.toLime (target := CallFrame.limeNoHost) (fun _ _ _ _ h => h)
    have mapped := (Computed.lime_br_table_iff (depths := depths) (fallback := fallback)
      (selector := selector) (saved := saved) (rest := codeToLime tail)).mp
      (by simpa only [Config.toLime, codeToLime_append, map_values, codeToLime_cons,
        Execution.Runtime.AdminInstr.map, Wasm.V1.Instr.toLime] using projected)
    apply CallContinuation.config_toLime_injective H
    simpa only [Config.toLime, codeToLime_append, map_values, codeToLime_cons,
      Execution.Runtime.AdminInstr.map, Wasm.V1.Instr.toLime] using mapped
  · rintro rfl
    rw [values_append, List.append_assoc]
    simpa only [values, List.map_cons, List.map_nil, List.append_assoc, List.cons_append, List.nil_append] using
      Step.context (Step.pure (host := CallFrame.v1NoHost) s f (.brTable depths fallback selector)) saved tail

theorem if_select_iff {H : Type} {s : Store H} {f : Frame} {saved : List Value}
    {condition : BitVec 32} {result : Option NumType} {left right : Wasm.V1.Expr}
    {tail : List Admin} {dst : Config H} :
    Step CallFrame.v1NoHost
      ⟨s, f, values (saved ++ [Value.int .i32 condition]) ++ .source (.if_ result left right) :: tail⟩ dst ↔
    dst = ⟨s, f, values saved ++ .source (.block result (if condition = 0 then right else left)) :: tail⟩ := by
  constructor
  · intro move
    have projected := move.toLime (target := CallFrame.limeNoHost) (fun _ _ _ _ h => h)
    have mapped := (Computed.lime_if_iff (bt := Wasm.V1.BlockType.toLime result) (thenBody := left.toLime) (elseBody := right.toLime)
      (condition := condition) (saved := saved) (rest := codeToLime tail)).mp
      (by simpa only [Config.toLime, codeToLime_append, map_values, codeToLime_cons,
        Execution.Runtime.AdminInstr.map, Wasm.V1.Instr.toLime] using projected)
    apply CallContinuation.config_toLime_injective H
    by_cases zero : condition = 0 <;>
      simpa only [zero, ite_true, ite_false, Config.toLime, codeToLime_append, map_values,
        codeToLime_cons, Execution.Runtime.AdminInstr.map, Wasm.V1.Instr.toLime] using mapped
  · rintro rfl
    rw [values_append, List.append_assoc]
    by_cases zero : condition = 0
    · rw [ite_eq_left zero, zero]
      simpa only [values, List.map_cons, List.map_nil, List.append_assoc, List.cons_append,
        List.nil_append] using!
        Step.context (Step.pure (host := CallFrame.v1NoHost) s f (.ifZero result left right)) saved tail
    · rw [ite_eq_right zero]
      simpa only [values, List.map_cons, List.map_nil, List.append_assoc, List.cons_append,
        List.nil_append] using
        Step.context (Step.pure (host := CallFrame.v1NoHost) s f
          (.ifNonzero result left right condition zero)) saved tail

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.RunProofs

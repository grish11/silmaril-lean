module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Guard
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Native

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32

open Execution.Runtime (Frame FuncAddr MemAddr MemInst Value)
open Wasm.V1.Execution

theorem Layout.initial_store {H : Type} {p : Program} {m : MemAddr} {base : Store H} {initial : MemInst}
    (layout : Layout p base m initial) : storeWithBytes base m initial initial.data = base :=
  RunProofs.initial_store layout

/-- Entry depends on allocation and V1 arity. The caller frame and the live
store survive unchanged, including when the caller invokes its own address. -/
theorem Layout.enter_rendered {H : Type} {p : Program} {m : MemAddr} {base : Store H} {initial : MemInst}
    (layout : Layout p base m initial) {address : FuncAddr} {fn : Function}
    (found : p.lookup address = some fn) (arity : fn.declaration.results.length ≤ 1)
    {suspended : Frame} {bytes : ByteArray} {args : List Value}
    (count : args.length = fn.declaration.params.length) :
    Step CallFrame.v1NoHost (render base m initial ⟨bytes, suspended, values args ++ [.invoke address]⟩)
      (render base m initial ⟨bytes, suspended, [.frame fn.declaration.results.length (fn.declaration.frame args)
        [.label fn.declaration.results.length [] (expression fn.v1Func.body)]]⟩) :=
  RunProofs.enter_rendered layout found arity count

/-- Fallthrough first closes the function label, then delivers the results
above the saved operands and resumes the caller on the current live store. -/
theorem v1_function_fallthrough {H : Type} {s : Store H} {caller callee : Frame}
    {saved payload : List Value} {tail : List Admin} {arity : Nat} (count : payload.length = arity) :
    let done := (⟨s, caller, values saved ++ [.frame arity callee (values payload)] ++ tail⟩ : Config H)
    Step CallFrame.v1NoHost
      ⟨s, caller, values saved ++ [.frame arity callee [.label arity [] (values payload)]] ++ tail⟩ done ∧
    Step CallFrame.v1NoHost done ⟨s, caller, values saved ++ values payload ++ tail⟩ :=
  RunProofs.function_fallthrough count

theorem call_ready {p : Program} {m : MemAddr} {addr : FuncAddr} {fn : Function}
    {caller : Frame} {index : FuncIdx} (found : p.lookup addr = some fn)
    (resolved : caller.module.funcs[index.toNat]? = some addr) (args : List Value) (bytes : ByteArray) :
    Ready p m (fn.rank + 1) bytes.size ⟨bytes, caller, values args ++ [.source (.call index)]⟩ :=
  RunProofs.initial_call found resolved args bytes rfl

/-- A resolved external invocation enters the same checked graph as a
source direct call. Allocation and argument count are checked at native entry. -/
theorem invoke_ready {mode : MemoryMode} {calls : CallMode} {p : Program} {m : MemAddr} {addr : FuncAddr}
    {fn : Function} {caller : Frame} (found : p.lookup addr = some fn) (args : List Value)
    {bytes : ByteArray} {minimum : Nat} (extent : mode.extent minimum bytes) :
    ReadyFor mode p m calls (fn.rank + 1) minimum ⟨bytes, caller, values args ++ [.invoke addr]⟩ :=
  RunProofs.initial_invoke found args extent

theorem Edge.module_eq {p : Program} {m : MemAddr} {src dst : State} (edge : Edge p m src dst) :
    dst.frame.module = src.frame.module :=
  RunProofs.edge_module edge

theorem Edge.extent_eq {p : Program} {m : MemAddr} {src dst : State} (edge : Edge p m src dst) :
    dst.bytes.size = src.bytes.size :=
  RunProofs.extent_preserved edge rfl

theorem Edge.ready {p : Program} {m : MemAddr} {src dst : State} {rank extent : Nat}
    (edge : Edge p m src dst) (checked : p.checkV1 m = true) (ready : Ready p m rank extent src) :
    Ready p m rank extent dst :=
  ⟨edge.extent_eq.trans ready.1, RunProofs.preserve checked edge ready.2⟩

theorem render_shared {H : Type} {p : Program} {m : MemAddr} {base : Store H}
    {initial : MemInst} {src : State} {rank : Nat} (ready : Ready p m rank initial.data.size src) :
    SharedStore base m initial (render base m initial src).store :=
  ⟨src.bytes, ready.1, rfl⟩

/-- Exact native successors, including each separate administrative trap step. -/
theorem v1_step_iff {H : Type} {p : Program} {m : MemAddr} {base : Store H} {initial : MemInst}
    (checked : p.checkV1 m = true) (layout : Layout p base m initial) {src : State} {rank : Nat}
    (ready : Ready p m rank initial.data.size src) {dst : Config H} :
    Step CallFrame.v1NoHost (render base m initial src) dst ↔
      ∃ out, Edge p m src out ∧ Ready p m rank initial.data.size out ∧ dst = render base m initial out :=
  RunProofs.step_iff checked layout trivial ready

/-- Each finite native prefix reflects to a run whose exact store, locals and
administrative code render the endpoint. The endpoint need not have returned. -/
theorem v1_run_iff {H : Type} {p : Program} {m : MemAddr} {base : Store H} {initial : MemInst}
    (checked : p.checkV1 m = true) (layout : Layout p base m initial) {src : State} {rank : Nat}
    (ready : Ready p m rank initial.data.size src) {dst : Config H} :
    Steps CallFrame.v1NoHost (render base m initial src) dst ↔
      ∃ out, Runs p m src out ∧ Ready p m rank initial.data.size out ∧ dst = render base m initial out :=
  RunProofs.run_iff checked layout trivial ready

/-- Ordinary entry from an external caller resolving a checked root. -/
theorem v1_call_run_iff {H : Type} {p : Program} {m : MemAddr} {base : Store H} {initial : MemInst}
    (checked : p.checkV1 m = true) (layout : Layout p base m initial)
    {root : FuncAddr} {fn : Function} {caller : Frame} {index : FuncIdx} {args : List Value}
    (found : p.lookup root = some fn) (resolved : caller.module.funcs[index.toNat]? = some root)
    {dst : Config H} :
    Steps CallFrame.v1NoHost ⟨base, caller, values args ++ [.source (.call index)]⟩ dst ↔
      ∃ out, Runs p m ⟨initial.data, caller, values args ++ [.source (.call index)]⟩ out ∧
        Ready p m (fn.rank + 1) initial.data.size out ∧ dst = render base m initial out := by
  have exactRun := v1_run_iff (dst := dst) checked layout (call_ready found resolved args initial.data)
  simpa only [render, layout.initial_store] using exactRun

/-- The extent never decreases, including across a growing child frame. -/
theorem EdgeAt.extent_mono {mode : MemoryMode} {p : Program} {m : MemAddr} {src dst : State}
    (edge : EdgeAt mode p m src dst) : src.bytes.size ≤ dst.bytes.size :=
  RunProofs.extent_mono edge

theorem RunsAt.extent_mono {mode : MemoryMode} {p : Program} {m : MemAddr} {src dst : State}
    (run : RunsAt mode p m src dst) : src.bytes.size ≤ dst.bytes.size := by
  induction run with
  | refl => exact Nat.le_refl _
  | tail _ edge ih => exact ih.trans edge.extent_mono

theorem EdgeAt.ready {mode : MemoryMode} {calls : CallMode} {p : Program} {m : MemAddr} {src dst : State}
    {rank minimum : Nat} (edge : EdgeAt mode p m src dst) (checked : p.checkV1 m mode calls = true)
    (ready : ReadyFor mode p m calls rank minimum src) : ReadyFor mode p m calls rank minimum dst :=
  ⟨RunProofs.extent_preserved edge ready.1, RunProofs.preserve checked edge ready.2⟩

theorem render_growing {H : Type} {p : Program} {m : MemAddr} {base : Store H} {initial : MemInst}
    {calls : CallMode} {src : State} {rank : Nat}
    (ready : ReadyFor (.growing initial.max) p m calls rank initial.data.size src) :
    GrowingStore base m initial (render base m initial src).store :=
  ⟨src.bytes, ready.1, rfl⟩

/-- Exact successors in either call or memory profile. Growth has separate
success and failure edges. -/
theorem v1_step_iff_at {H : Type} {mode : MemoryMode} {calls : CallMode} {p : Program} {m : MemAddr}
    {base : Store H} {initial : MemInst} (checked : p.checkV1 m mode calls = true) (layout : Layout p base m initial)
    (matched : mode.matches initial) {src : State} {rank : Nat}
    (ready : ReadyFor mode p m calls rank initial.data.size src) {dst : Config H} :
    Step CallFrame.v1NoHost (render base m initial src) dst ↔
      ∃ out, EdgeAt mode p m src out ∧ ReadyFor mode p m calls rank initial.data.size out ∧
        dst = render base m initial out :=
  RunProofs.step_iff checked layout matched ready

/-- Relational finite-prefix correspondence, including native allocation failure. -/
theorem v1_run_iff_at {H : Type} {mode : MemoryMode} {calls : CallMode} {p : Program} {m : MemAddr}
    {base : Store H} {initial : MemInst} (checked : p.checkV1 m mode calls = true) (layout : Layout p base m initial)
    (matched : mode.matches initial) {src : State} {rank : Nat}
    (ready : ReadyFor mode p m calls rank initial.data.size src) {dst : Config H} :
    Steps CallFrame.v1NoHost (render base m initial src) dst ↔
      ∃ out, RunsAt mode p m src out ∧ ReadyFor mode p m calls rank initial.data.size out ∧
        dst = render base m initial out :=
  RunProofs.run_iff checked layout matched ready

/-- Read back every finite prefix from ordinary entry. The recursive policy
checks direct links independently of rank, and the growing memory profile
reflects both native choices of an in-limit grow. -/
theorem v1_call_run_iff_at {H : Type} {mode : MemoryMode} {calls : CallMode} {p : Program} {m : MemAddr}
    {base : Store H} {initial : MemInst} (checked : p.checkV1 m mode calls = true)
    (layout : Layout p base m initial) (matched : mode.matches initial)
    (extent : mode.extent initial.data.size initial.data)
    {root : FuncAddr} {fn : Function} {caller : Frame} {index : FuncIdx} {args : List Value}
    (found : p.lookup root = some fn) (resolved : caller.module.funcs[index.toNat]? = some root)
    {dst : Config H} :
    Steps CallFrame.v1NoHost ⟨base, caller, values args ++ [.source (.call index)]⟩ dst ↔
      ∃ out, RunsAt mode p m ⟨initial.data, caller, values args ++ [.source (.call index)]⟩ out ∧
        ReadyFor mode p m calls (fn.rank + 1) initial.data.size out ∧ dst = render base m initial out := by
  have ready := RunProofs.initial_call (calls := calls) (m := m) found resolved args initial.data extent
  simpa only [render, layout.initial_store] using v1_run_iff_at (dst := dst) checked layout matched ready

/-- A growing graph starts with a page-aligned, in-limit allocation. -/
theorem v1_growing_call_run_iff {H : Type} {p : Program} {m : MemAddr} {base : Store H} {initial : MemInst}
    (checked : p.checkV1 m (.growing initial.max) = true) (layout : Layout p base m initial)
    (extent : MemoryGrow.SizeAllows initial 0)
    {root : FuncAddr} {fn : Function} {caller : Frame} {index : FuncIdx} {args : List Value}
    (found : p.lookup root = some fn) (resolved : caller.module.funcs[index.toNat]? = some root)
    {dst : Config H} :
    Steps CallFrame.v1NoHost ⟨base, caller, values args ++ [.source (.call index)]⟩ dst ↔
      ∃ out, RunsAt (.growing initial.max) p m ⟨initial.data, caller, values args ++ [.source (.call index)]⟩ out ∧
        ReadyAt (.growing initial.max) p m (fn.rank + 1) initial.data.size out ∧ dst = render base m initial out :=
  v1_call_run_iff_at checked layout rfl (show GrowthExtent initial initial.data from ⟨Nat.le_refl _, extent⟩)
    found resolved

/-- A depth-zero backedge restores the loop source. Re-entry then opens a
new zero-input label with the same current frame and store. -/
theorem v1_loop_restart {H : Type} {s : Store H} {f : Frame} {result : Option NumType}
    {body : Wasm.V1.Expr} {saved scratch : List Value} {branchTail tail : List Admin} :
    let loop := Wasm.V1.Instr.loop result body
    let pending := (⟨s, f, values saved ++ [.source loop] ++ tail⟩ : Config H)
    Step CallFrame.v1NoHost
      ⟨s, f, values saved ++ [.label 0 [loop] (values scratch ++ [.source (.br ⟨0⟩)] ++ branchTail)] ++ tail⟩ pending ∧
    Step CallFrame.v1NoHost pending ⟨s, f, values saved ++ [.label 0 [loop] (expression body)] ++ tail⟩ :=
  RunProofs.loop_restart

/-- A branch at the function label delivers the typed suffix inside the
activation. A separate frame-completion step resumes the caller. -/
theorem v1_function_branch_exit {H : Type} {s : Store H} {caller callee : Frame}
    {saved extra payload : List Value} {bodyTail callerTail : List Admin} {results : List NumType}
    (typed : payload.map Value.type = results) :
    let arity := results.length
    let done := ⟨s, caller, values saved ++ [.frame arity callee (values payload)] ++ callerTail⟩
    Step CallFrame.v1NoHost
      ⟨s, caller, values saved ++ [.frame arity callee [.label arity []
        (values extra ++ values payload ++ [.source (.br ⟨0⟩)] ++ bodyTail)]] ++ callerTail⟩ done ∧
    Step CallFrame.v1NoHost done ⟨s, caller, values saved ++ values payload ++ callerTail⟩ :=
  RunProofs.function_branch_exit typed

/-- The unsigned i32 selector chooses a listed depth or the default. This
step leaves an ordinary branch with its saved operands and continuation. -/
theorem v1_br_table_select_iff {H : Type} {s : Store H} {f : Frame} {saved : List Value}
    {selector : BitVec 32} {depths : List LabelIdx} {fallback : LabelIdx} {tail : List Admin} {dst : Config H} :
    Step CallFrame.v1NoHost
      ⟨s, f, values (saved ++ [Value.int .i32 selector]) ++ .source (.brTable depths fallback) :: tail⟩ dst ↔
    dst = ⟨s, f, values saved ++ .source (.br (depths[selector.toNat]?.getD fallback)) :: tail⟩ :=
  RunProofs.br_table_select_iff

/-- Selection consumes the i32 condition and retains only the selected block. -/
theorem v1_if_select_iff {H : Type} {s : Store H} {f : Frame} {saved : List Value}
    {condition : BitVec 32} {result : Option NumType} {left right : Wasm.V1.Expr}
    {tail : List Admin} {dst : Config H} :
    Step CallFrame.v1NoHost
      ⟨s, f, values (saved ++ [Value.int .i32 condition]) ++ .source (.if_ result left right) :: tail⟩ dst ↔
    dst = ⟨s, f, values saved ++ .source (.block result (if condition = 0 then right else left)) :: tail⟩ :=
  RunProofs.if_select_iff

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32

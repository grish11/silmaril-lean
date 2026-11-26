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

theorem call_ready {p : Program} {m : MemAddr} {addr : FuncAddr} {fn : Function}
    {caller : Frame} {index : FuncIdx} (found : p.lookup addr = some fn)
    (resolved : caller.module.funcs[index.toNat]? = some addr) (args : List Value) (bytes : ByteArray) :
    Ready p m (fn.rank + 1) bytes.size ⟨bytes, caller, values args ++ [.source (.call index)]⟩ :=
  RunProofs.initial_call found resolved args bytes

theorem Edge.module_eq {p : Program} {m : MemAddr} {src dst : State} (edge : Edge p m src dst) :
    dst.frame.module = src.frame.module :=
  RunProofs.edge_module edge

theorem Edge.extent_eq {p : Program} {m : MemAddr} {src dst : State} (edge : Edge p m src dst) :
    dst.bytes.size = src.bytes.size :=
  RunProofs.edge_extent edge

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
  RunProofs.step_iff checked layout ready

/-- Each finite native prefix reflects to a run whose exact store, locals and
administrative code render the endpoint. The endpoint need not have returned. -/
theorem v1_run_iff {H : Type} {p : Program} {m : MemAddr} {base : Store H} {initial : MemInst}
    (checked : p.checkV1 m = true) (layout : Layout p base m initial) {src : State} {rank : Nat}
    (ready : Ready p m rank initial.data.size src) {dst : Config H} :
    Steps CallFrame.v1NoHost (render base m initial src) dst ↔
      ∃ out, Runs p m src out ∧ Ready p m rank initial.data.size out ∧ dst = render base m initial out :=
  RunProofs.run_iff checked layout ready

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

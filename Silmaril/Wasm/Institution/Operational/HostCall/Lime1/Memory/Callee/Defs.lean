module

public import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Defs
public import Silmaril.Wasm.Institution.Operational.MemoryWrite.Native.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.HostCall.Lime1.MemoryCallee

open Execution.Runtime (Frame Result Value)
open Wasm.Lime1.Execution
open CallContinuation.OuterCall.Ranked

/-- After entry the arguments determine the same frame until it is popped.
The relation carries live bytes separately from the frame and its operands. -/
inductive Phase where
  | invoke (args : List Value)
  | body (args stack : List Value) (ops : List Graph.Memory32.Op)
  | trapped (args stack : List Value) (rest : List Admin)
  | exit (args : List Value) (out : Result)
  | done (out : Result)

def code (ops : List Graph.Memory32.Op) : List Admin :=
  expression (ops.map fun op => op.v1.toLime)

def resultTyped (callee : MemoryTarget) : Result → Prop
  | .values vs => vs.map Value.type = callee.fn.declaration.results
  | .trap => True

def Ready (callee : MemoryTarget) : Phase → Prop
  | .invoke args | .trapped args _ _ => args.map Value.type = callee.fn.declaration.params
  | .body args stack ops => args.map Value.type = callee.fn.declaration.params ∧
      ops.all MemoryTarget.supportedOp = true ∧ callee.fn.WellTyped stack ops
  | .exit args out => args.map Value.type = callee.fn.declaration.params ∧ resultTyped callee out
  | .done out => resultTyped callee out

def render (callee : MemoryTarget) : Phase → List Admin
  | .invoke args => values args ++ [.invoke callee.address]
  | .body args stack ops => [.frame callee.fn.declaration.results.length (callee.fn.declaration.frame args)
      [.label callee.fn.declaration.results.length [] (values stack ++ code ops)]]
  | .trapped args stack rest => [.frame callee.fn.declaration.results.length (callee.fn.declaration.frame args)
      [.label callee.fn.declaration.results.length [] (values stack ++ .trap :: rest)]]
  | .exit args out => [.frame callee.fn.declaration.results.length (callee.fn.declaration.frame args) (result out)]
  | .done out => result out

def config {H : Type} {base : Store H} (mem : Memory32 base) (caller : Frame)
    (saved : List Value) (tail : List Admin) (callee : MemoryTarget) (bytes : ByteArray)
    (phase : Phase) : Config H :=
  ⟨mem.store bytes, caller, values saved ++ render callee phase ++ tail⟩

inductive Edge (callee : MemoryTarget) : ByteArray → Phase → ByteArray → Phase → Prop where
  | enter {bytes args} : Edge callee bytes (.invoke args) bytes (.body args callee.fn.initial callee.fn.code)
  | get {bytes args stack index ops v}
      (found : (callee.fn.declaration.frame args).locals[index.toNat]? = some v) :
      Edge callee bytes (.body args stack (.ranked (.numeric (.get index)) :: ops))
        bytes (.body args (stack ++ [v]) ops)
  | load {bytes args saved offset ptr ops bits}
      (read : MemoryQuery.EdgeAt bytes offset.val (.load ptr) (.value bits)) :
      Edge callee bytes (.body args (saved ++ [Value.int .i32 ptr]) (.load offset :: ops))
        bytes (.body args (saved ++ [Value.int .i32 bits]) ops)
  | loadTrap {bytes args saved offset ptr ops}
      (read : MemoryQuery.EdgeAt bytes offset.val (.load ptr) .trap) :
      Edge callee bytes (.body args (saved ++ [Value.int .i32 ptr]) (.load offset :: ops))
        bytes (.trapped args saved (code ops))
  | store {bytes written args saved offset ptr word ops}
      (write : MemoryWrite.EdgeAt bytes offset.val (.store ptr word) (.written written)) :
      Edge callee bytes (.body args (saved ++ [Value.int .i32 ptr, Value.int .i32 word]) (.store offset :: ops))
        written (.body args saved ops)
  | storeTrap {bytes args saved offset ptr word ops}
      (write : MemoryWrite.EdgeAt bytes offset.val (.store ptr word) .trap) :
      Edge callee bytes (.body args (saved ++ [Value.int .i32 ptr, Value.int .i32 word]) (.store offset :: ops))
        bytes (.trapped args saved (code ops))
  | erase {bytes args stack kept removed before cut rest}
      (split : stack = kept ++ removed) (suffix : before = cut ++ rest) (active : removed ≠ [] ∨ cut ≠ []) :
      Edge callee bytes (.trapped args stack before) bytes (.trapped args kept rest)
  | labelDone {bytes args vs} : Edge callee bytes (.body args vs []) bytes (.exit args (.values vs))
  | labelTrap {bytes args} : Edge callee bytes (.trapped args [] []) bytes (.exit args .trap)
  | frameDone {bytes args out} : Edge callee bytes (.exit args out) bytes (.done out)

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1.MemoryCallee

module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Host.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Native.Defs

/-!
# A computed direct host site in a checked V1 activation

The prefix uses graph numeric instructions. The site checks the declared
parameter suffix and the same region continuation that receives the results.
The caller's module and local types remain those of the current declaration.
-/

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32

open Execution.Runtime (Frame Value)
open Computed
open Wasm.V1.Execution

/-- Check a numeric prefix and feed the host's declared results above the
saved operand prefix to a continuation checker. -/
def checkHostPrefixWith (locals stack : List NumType) (ops : List Prefix.Op)
    (signature : Wasm.V1.FuncType) (resume : List NumType → Bool) : Bool :=
  ((Prefix.check locals stack ops).map fun operands =>
    decide (operands.take signature.params.length = signature.params.reverse) &&
      resume (signature.results.reverse ++ operands.drop signature.params.length)).getD false

def Function.checkHostPrefix (fn : Function) (stack : List NumType) (ops : List Prefix.Op)
    (signature : Wasm.V1.FuncType) (tail : List Op) (fallthrough : List NumType)
    (labels : List (List NumType)) : Bool :=
  checkHostPrefixWith (fn.declaration.params ++ fn.declaration.locals) stack ops signature
    (fun next => fn.checkRegion next fallthrough tail labels)

/-- The running prefix and its checked continuation share the current activation.
The actual argument values need only be recovered when the prefix is exhausted. -/
structure HostPrefixTyped (fn : Function) (caller : Frame) (stack : List Value)
    (ops : List Prefix.Op) (signature : Wasm.V1.FuncType) (tail : List Op)
    (fallthrough : List NumType) (labels : List (List NumType)) : Prop where
  scope : caller.module = fn.declaration.module
  locals : caller.locals.map Value.type = fn.declaration.params ++ fn.declaration.locals
  code : fn.checkHostPrefix (Prefix.stackTypes stack) ops signature tail fallthrough labels = true

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32

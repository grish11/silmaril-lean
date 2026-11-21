module

public import Silmaril.Wasm.Execution.Core.Intrinsic.Defs

@[expose] public section

namespace Silmaril.Wasm.Execution.Core.Intrinsic

open Validation

variable {H : Type} {context : Context} {caller : World H context}
  {parameters results locals suffix : List IntType}

def Values.append : {left : List IntType} → Values left → Values suffix → Values (left ++ suffix)
  | _, .nil, right => right
  | _, .cons bits tail, right => .cons bits (tail.append right)

def Values.zeros : (types : List IntType) → Values types
  | [] => .nil
  | _ :: tail => .cons 0 (zeros tail)

def rawIntTypes (types : List IntType) : List ValType := types.map fun kind => .num (.int kind)

/-- A direct Core Wasm call resolved in the caller's store. Parameter indices
are in declaration order; result indices are top-first like the machine.
The callee may be in another instance of the same store. -/
structure DirectCall (caller : World H context) (parameters results : List IntType) where
  index : FuncIdx
  address : Nat
  instance_ : FuncInst H
  declaredLocals : List IntType
  rawType : TypeIdx
  body : Code (parameters ++ declaredLocals) [] results
  calleeContext : Context
  calleeOk : ModuleInstOk caller.store instance_.module calleeContext
  resolveIndex : caller.moduleInst.funcs[index.toNat]? = some address
  resolveAddress : caller.store.funcs[address]? = some instance_
  signature : Expand instance_.type (.func
    (Ty.ofList (parameters.map fun kind => .num (.int kind))) (Ty.ofList (stackTypes results)))
  codeEq : instance_.code = .wasm ⟨rawType, rawIntTypes declaredLocals, body.erase⟩

def DirectCall.world (call : DirectCall caller parameters results) : World H call.calleeContext :=
  ⟨caller.store, call.instance_.module, caller.storeOk, call.calleeOk⟩

def DirectCall.start (call : DirectCall caller parameters results) (args : Values parameters) :
    State call.world (parameters ++ call.declaredLocals) results :=
  ⟨⟨args.append (Values.zeros call.declaredLocals)⟩, .run .nil call.body⟩

/-- Fuel only bounds the callee machine, not resolution or Core frame cleanup. -/
def DirectCall.runFor (call : DirectCall caller parameters results) (args : Values parameters) (fuel : Nat) :
    Option (Option (Values results)) :=
  ((call.start args).runFor fuel).control.result?

def DirectCall.source (call : DirectCall caller parameters results) (frame : LocalFrame caller locals)
    (args : Values parameters) : Config H :=
  ⟨caller.store, frame.erase, vals args.erase ++ [.plain (.call call.index)]⟩

def DirectCall.wrap (_call : DirectCall caller parameters results) (outer : Frame)
    (configuration : Config H) : Config H :=
  ⟨configuration.store, outer,
    [.frame results.length configuration.frame [.label results.length [] configuration.code]]⟩

def DirectCall.suspend (call : DirectCall caller parameters results) (frame : LocalFrame caller locals)
    (configuration : Config H) : Config H := call.wrap frame.erase configuration

end Silmaril.Wasm.Execution.Core.Intrinsic

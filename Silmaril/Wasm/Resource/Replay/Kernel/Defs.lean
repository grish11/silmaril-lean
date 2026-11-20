module

public import Silmaril.Wasm.Resource.Replay.Defs
public import Silmaril.Wasm.Verify.Kernel.Defs

@[expose] public section

namespace Silmaril.Wasm.Resource.Replay.Kernel

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Verify
  Silmaril.Wasm.Game
open Silmaril.Wasm.Verify.Kernel (splitK runIK kDepth)

noncomputable def decomposeK (store : Store Nat) : Nat → List Admin →
    Option (Ctx × Nat × Nat × List Val)
  | 0, code => decompose? store code
  | depth + 1, code =>
    match _split : splitK code with
    | (values, .label arity cont body :: rest) =>
      (decomposeK store depth body).map fun (ctx, addr, host, args) =>
        (.label values arity cont ctx rest, addr, host, args)
    | (values, .handler arity catches body :: rest) =>
      (decomposeK store depth body).map fun (ctx, addr, host, args) =>
        (.handler values arity catches ctx rest, addr, host, args)
    | (values, .frame arity frame body :: rest) =>
      (decomposeK store depth body).map fun (ctx, addr, host, args) =>
        (.frame values arity frame ctx rest, addr, host, args)
    | (values, head :: rest) =>
      if head.isCallRef then
        match values.getLast? with
        | some (.ref (.func addr)) =>
          match hostArity? store addr with
          | some (host, count) =>
            let operands := values.dropLast
            if count ≤ operands.length then
              some (.top (operands.take (operands.length - count)) rest, addr, host,
                operands.drop (operands.length - count))
            else none
          | none => none
        | _ => none
      else none
    | (_, []) => none

noncomputable def runToK (fuel : Nat) (config : Config Nat) :
    Option (Config Nat × Ctx × Nat × Nat × List Val) :=
  let stopped := (runIK refOracle fuel config).1
  (decomposeK stopped.store kDepth stopped.code).map fun entry => (stopped, entry)

/-- Evaluate the same replay with a structural driver even when the Core operands are symbolic. -/
noncomputable def replayFromK (inst : ScalarInstance) (script : Script) (fuel : Nat) :
    Nat → Nat → Config Nat → List RMove
  | 0, _, _ => []
  | count + 1, index, config =>
    match runToK fuel config with
    | none => []
    | some (stopped, ctx, addr, host, args) =>
      if argsOk inst host args then
        let reply := script index host args
        if ansOk inst stopped.store addr host reply then
          .ask host args :: .ans host (.returns reply) ::
            replayFromK inst script fuel count (index + 1)
              ⟨stopped.store, stopped.frame, ctx.fill (vals reply)⟩
        else [.ask host args]
      else []

end Silmaril.Wasm.Resource.Replay.Kernel

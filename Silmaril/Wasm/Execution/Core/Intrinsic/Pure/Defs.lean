module

public import Silmaril.Wasm.Execution.Core.Intrinsic.Invoke.Defs
public import Silmaril.Wasm.SingleThreaded.Determinism.Head
public import Silmaril.Wasm.SingleThreaded.Profile

@[expose] public section

namespace Silmaril.Wasm.Execution.Core.Intrinsic.Pure

open Numerics SingleThreaded

variable {locals input middle output parameters declared results : List IntType}

/-- A store-free, terminating denotation of typed integer code. Traps are
absorbing: a later operation does not execute if its prefix traps. This
fragment has no calls in the body, mutation, allocation, or references. -/
def eval (frame : Values locals) : {input : List IntType} →
    Code locals input output → Values input → Option (Values output)
  | _, .done, stack => some stack
  | _, .seq op tail, stack =>
    match op.eval frame stack with
    | .next values => eval frame tail values
    | .trap _ => none

/-- Zero-initialize declared locals in declaration order, as in Core. -/
def denotes (body : Code (parameters ++ declared) [] results) (args : Values parameters) :
    Option (Values results) :=
  eval (args.append (Values.zeros declared)) body .nil

def budget : {input : List IntType} → Code locals input output → Nat
  | _, .done => 1
  | _, .seq _ tail => budget tail + 1

/-- A linked realization in stock Core, with exact code and local layout. The
store lookup, signature and code equality are inherited from `DirectCall`. -/
structure Linked {parameters declared results : List IntType}
    (body : Code (parameters ++ declared) [] results) where
  context : Validation.Context
  world : World Nat context
  call : DirectCall world parameters results
  locals : call.declaredLocals = declared
  code : locals ▸ call.body = body

/-- Actual observer contexts: append the same typed numeric suffix, link both
filled functions to real Core entries, and invoke with any valid argument
vector. The empty suffix is allowed. No arbitrary linking or Core context is
quantified over; only the stores of these fully linked invocations vary. -/
def PostEquivalent (first second : Code (parameters ++ declared) [] results) : Prop :=
  ∀ {observed : List IntType} (tail : Code (parameters ++ declared) results observed)
    (left : Linked (first.append tail)) (right : Linked (second.append tail))
    (oracle : GrowOracle) (args : List Val), InvokeOk left.world.store left.call.address args →
      behaviours (profile oracle) Det.noHost left.world.store left.call.address args =
        behaviours (profile oracle) Det.noHost right.world.store right.call.address args

end Silmaril.Wasm.Execution.Core.Intrinsic.Pure

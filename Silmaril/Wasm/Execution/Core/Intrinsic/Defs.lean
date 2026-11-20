module

public import Silmaril.Wasm.Execution.Core.Typing.Config

@[expose] public section

/-! # A typed Core machine for integer straight-line code

Operand indices are top-first. Locals use the same heterogeneous list in
declaration order. An instance is fixed by the index of a machine state, so the
machine never equates stores or frames belonging to different instances.
-/

namespace Silmaril.Wasm.Execution.Core.Intrinsic

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type} {context : Context} {kind : IntType}
  {kinds locals input middle output results : List IntType}

def stackTypes (types : List IntType) : List CValType :=
  (types.map fun kind => .num (.int kind)).reverse

def localTypes (types : List IntType) : List LocalType :=
  types.map fun kind => ⟨.set, .num (.int kind)⟩

/-- Heterogeneous integer values; no run-time type test is required to pop one. -/
inductive Values : List IntType → Type where
  | nil : Values []
  | cons {kind : IntType} {kinds : List IntType}
      (bits : BitVec kind.width) (tail : Values kinds) : Values (kind :: kinds)

def Values.erase : {kinds : List IntType} → Values kinds → List Val
  | _, .nil => []
  | _, .cons (kind := kind) bits tail => .num ⟨.int kind, bits⟩ :: tail.erase

def Values.isEmpty : Values kinds → Bool
  | .nil => true
  | .cons .. => false

/-- Typed de Bruijn references into the declared locals. -/
inductive Slot : List IntType → IntType → Type where
  | here {kind : IntType} {kinds : List IntType} : Slot (kind :: kinds) kind
  | there {kind other : IntType} {kinds : List IntType} :
      Slot kinds kind → Slot (other :: kinds) kind

def Slot.toNat : {locals : List IntType} → Slot locals kind → Nat
  | _, .here => 0
  | _, .there ref => ref.toNat + 1

def Slot.index (ref : Slot locals kind) (bound : ref.toNat < 2 ^ 32) : LocalIdx :=
  ⟨⟨ref.toNat, bound⟩⟩

def Slot.get : {locals : List IntType} → Slot locals kind → Values locals → BitVec kind.width
  | _, .here, .cons bits _ => bits
  | _, .there ref, .cons _ tail => ref.get tail

/-- Individual instructions indexed by their precise stack effect. The
`unreachable` constructor is polymorphic in both stack indices. -/
inductive Op (locals : List IntType) : List IntType → List IntType → Type where
  | nop {stack : List IntType} : Op locals stack stack
  | drop {kind : IntType} {stack : List IntType} : Op locals (kind :: stack) stack
  | localGet {kind : IntType} {stack : List IntType}
      (ref : Slot locals kind) (bound : ref.toNat < 2 ^ 32) :
      Op locals stack (kind :: stack)
  | intBin {kind : IntType} {stack : List IntType} (op : IntBinOp) :
      Op locals (kind :: kind :: stack) (kind :: stack)
  | unreachable {input output : List IntType} : Op locals input output

def Op.erase : Op locals input output → Instr
  | .nop => .nop
  | .drop => .drop
  | .localGet ref bound => .localGet (ref.index bound)
  | .intBin (kind := kind) op => .intBinOp kind op
  | .unreachable => .unreachable

/-- A composable, transport-free sequence, not a recursive call or an inliner. -/
inductive Code (locals : List IntType) : List IntType → List IntType → Type where
  | done {stack : List IntType} : Code locals stack stack
  | seq {input middle output : List IntType} :
      Op locals input middle → Code locals middle output → Code locals input output

def Code.erase : {input output : List IntType} → Code locals input output → List Instr
  | _, _, .done => []
  | _, _, .seq op tail => op.erase :: tail.erase

def Code.append : {input middle output : List IntType} → Code locals input middle →
    Code locals middle output → Code locals input output
  | _, _, _, .done, right => right
  | _, _, _, .seq op tail, right => .seq op (tail.append right)

def Code.isEmpty : Code locals input output → Bool
  | .done => true
  | .seq .. => false

/-- The untouched store and module instantiation, checked by the existing
Core judgments, not by an independent typing relation. -/
structure World (H : Type) (context : Context) where
  store : Store H
  moduleInst : ModuleInst
  storeOk : StoreOk store
  moduleOk : ModuleInstOk store moduleInst context

structure LocalFrame (world : World H context) (locals : List IntType) where
  values : Values locals

def LocalFrame.erase {world : World H context} (frame : LocalFrame world locals) : Frame :=
  ⟨frame.values.erase.map some, world.moduleInst⟩

/-- Trap formation and propagation are separate Core steps. A pending trap
retains exactly the operands and instructions Core has not discarded yet. -/
inductive Control (locals results : List IntType) where
  | run {stack : List IntType} : Values stack → Code locals stack results → Control locals results
  | trapping {saved ignored : List IntType} :
      Values saved → Code locals ignored results → Control locals results

structure State (world : World H context) (locals results : List IntType) where
  frame : LocalFrame world locals
  control : Control locals results

def Control.erase : Control locals results → List Admin
  | .run stack code => vals stack.erase.reverse ++ expression code.erase
  | .trapping stack code => vals stack.erase.reverse ++ [.trap] ++ expression code.erase

def State.erase {world : World H context} (state : State world locals results) : Config H :=
  ⟨world.store, state.frame.erase, state.control.erase⟩

inductive Effect (output : List IntType) where
  | next : Values output → Effect output
  | trap {saved : List IntType} : Values saved → Effect output

def Op.eval (op : Op locals input output) (frame : Values locals) (stack : Values input) :
    Effect output :=
  match op, stack with
  | .nop, stack => .next stack
  | .drop, .cons _ tail => .next tail
  | .localGet ref _, stack => .next (.cons (ref.get frame) stack)
  | .intBin (kind := kind) op, .cons rhs (.cons lhs tail) =>
    match intBinOp kind op lhs rhs with
    | .ok bits => .next (.cons bits tail)
    | .error _ => .trap tail
  | .unreachable, stack => .trap stack

def Effect.resume (effect : Effect middle) (tail : Code locals middle results) :
    Control locals results :=
  match effect with
  | .next stack => .run stack tail
  | .trap stack => .trapping stack tail

def Control.step? (control : Control locals results) (frame : Values locals) :
    Option (Control locals results) :=
  match control with
  | .run _ .done => none
  | .run stack (.seq op tail) => some ((op.eval frame stack).resume tail)
  | .trapping stack tail =>
    if stack.isEmpty && tail.isEmpty then none else some (.trapping .nil .done)

def State.step? {world : World H context} (state : State world locals results) :
    Option (State world locals results) :=
  (state.control.step? state.frame.values).map fun control => ⟨state.frame, control⟩

def State.runFor {world : World H context} : Nat → State world locals results → State world locals results
  | 0, state => state
  | fuel + 1, state => match state.step? with
    | none => state
    | some next => next.runFor fuel

/-- `none` means still running (including a trap that has not yet bubbled). -/
def Control.result? : Control locals results → Option (Option (Values results))
  | .run stack .done => some (some stack)
  | .run _ (.seq ..) => none
  | .trapping stack tail => if stack.isEmpty && tail.isEmpty then some none else none

def State.result? {world : World H context} (state : State world locals results) :
    Option Result :=
  state.control.result?.map fun result =>
    match result with
    | some stack => .values stack.erase.reverse
    | none => .trap

end Silmaril.Wasm.Execution.Core.Intrinsic

module

public import Silmaril.Languages.Python.Core.Closure.Dispatch.Defs

/-! # Stepping fixed positional Python closure bodies -/

@[expose] public section

namespace Silmaril.Languages.Python.Core.Closure.Executor

inductive Operand (layout : Layout) where
  | literal (value : Value)
  | read (slot : Slot layout)
  | closure (code : CodeRef) (select : Fin code.layout.captures → CaptureSlot layout)

/-- Every body ends in an explicit return. A call assigns its result before
resuming the remaining body. -/
inductive Body (layout : Layout) where
  | ret (value : Operand layout)
  | store (destination : Slot layout) (value : Operand layout) (next : Body layout)
  | call (destination : Slot layout) (callee : Operand layout)
      (arguments : List (Operand layout)) (next : Body layout)

structure Continuation (layout : Layout) where
  destination : Slot layout
  body : Body layout

abbrev Stack := List (Call.Saved Continuation)
abbrev CodeTable := Dispatch.CodeTable Body

inductive Fault where
  | danglingCell (identity : CellId)
  | missingCode (key : Nat)
  | layoutMismatch (expected actual : Layout)
  deriving DecidableEq, Repr

inductive State where
  | running (heap : Heap) {layout : Layout} (frame : Frame layout) (body : Body layout) (stack : Stack)
  | delivering (heap : Heap) (stack : Stack) (result : Result)
  | receiving (heap : Heap) (caller : Call.Saved Continuation) (stack : Stack) (result : Result)
  | finished (heap : Heap) (result : Result)
  | faulted (heap : Heap) (stack : Stack) (fault : Fault)

inductive Event where
  | enter (callee : Value)
  | resume (result : Result)
  | complete (result : Result)
  | fault (error : Fault)

abbrev Transition := Option Event × State

variable {layout : Layout}

def Operand.eval (heap : Heap) (frame : Frame layout) : Operand layout → Except Failure Value
  | .literal value => .ok value
  | .read slot => frame.read heap slot
  | .closure code select => .ok (.function (frame.closure code select))

def evalArguments (heap : Heap) (frame : Frame layout) :
    List (Operand layout) → Except Failure (List Value)
  | [] => .ok []
  | head :: tail =>
    (head.eval heap frame).bind fun value => (evalArguments heap frame tail).map (value :: ·)

def evalCall (heap : Heap) (frame : Frame layout) (callee : Operand layout)
    (arguments : List (Operand layout)) : Except Failure (Value × List Value) :=
  (callee.eval heap frame).bind fun value => (evalArguments heap frame arguments).map (value, ·)

def fault (heap : Heap) (stack : Stack) (error : Fault) : Transition :=
  (some (.fault error), .faulted heap stack error)

def fail (heap : Heap) (stack : Stack) : Failure → Transition
  | .defined error => (none, .delivering heap stack (.error error))
  | .danglingCell identity => fault heap stack (.danglingCell identity)

def failDispatch (heap : Heap) (stack : Stack) : Dispatch.Failure → Transition
  | .call error => fail heap stack error
  | .missingCode key => fault heap stack (.missingCode key)
  | .layoutMismatch expected actual => fault heap stack (.layoutMismatch expected actual)

def resumeStore (heap : Heap) (frame : Frame layout) (destination : Slot layout)
    (value : Value) (body : Body layout) (stack : Stack) : Transition :=
  match frame.write heap destination value with
  | .ok (updated, frame') => (none, .running updated frame' body stack)
  | .error error => fail heap stack error

def enter (active : Dispatch.Active Body Continuation) : State :=
  .running active.entered.environment.1 active.entered.environment.2 active.definition.body active.entered.stack

/-- Execute one transition, preserving the heap in terminal states. -/
def advance (table : CodeTable) : State → Option Transition
  | .running heap frame (.ret operand) stack =>
    some <| match operand.eval heap frame with
    | .ok value => (none, .delivering heap stack (.ok value))
    | .error error => fail heap stack error
  | .running heap frame (.store destination operand next) stack =>
    some <| match operand.eval heap frame with
    | .ok value => resumeStore heap frame destination value next stack
    | .error error => fail heap stack error
  | .running heap frame (.call destination callee arguments next) stack =>
    some <| match evalCall heap frame callee arguments with
    | .error error => fail heap stack error
    | .ok (value, values) =>
      match Dispatch.dispatch table value values heap ⟨_, frame, ⟨destination, next⟩⟩ stack with
      | .ok active => (some (.enter value), enter active)
      | .error error => failDispatch heap stack error
  | .delivering heap stack result =>
    let exit := Call.finish heap stack result
    some <| match exit.delivery with
    | .terminal observed => (some (.complete observed), .finished exit.heap observed)
    | .resume caller observed => (some (.resume observed), .receiving exit.heap caller exit.stack observed)
  | .receiving heap caller stack (.ok value) =>
    some (resumeStore heap caller.frame caller.continuation.destination value caller.continuation.body stack)
  | .receiving heap _ stack (.error error) => some (none, .delivering heap stack (.error error))
  | .finished .. | .faulted .. => none

/-- Execute at most the requested number of transitions and keep the residual
state. A prefix that ends in a live state makes no termination claim. -/
def runPrefix (table : CodeTable) : Nat → State → List Event × State
  | 0, source => ([], source)
  | fuel + 1, source =>
    match advance table source with
    | none => ([], source)
    | some (label, target) =>
      let (log, residual) := runPrefix table fuel target
      (label.toList ++ log, residual)

/-- Slot reads are the primitive operations shared with the frame interface. -/
inductive Evaluates (heap : Heap) (frame : Frame layout) :
    Operand layout → Except Failure Value → Prop where
  | literal (value : Value) : Evaluates heap frame (.literal value) (.ok value)
  | read (slot : Slot layout) : Evaluates heap frame (.read slot) (frame.read heap slot)
  | closure (code : CodeRef) (select : Fin code.layout.captures → CaptureSlot layout) :
      Evaluates heap frame (.closure code select) (.ok (.function (frame.closure code select)))

inductive Arguments (heap : Heap) (frame : Frame layout) :
    List (Operand layout) → Except Failure (List Value) → Prop where
  | nil : Arguments heap frame [] (.ok [])
  | headError {head tail error} : Evaluates heap frame head (.error error) →
      Arguments heap frame (head :: tail) (.error error)
  | tailError {head tail value error} : Evaluates heap frame head (.ok value) →
      Arguments heap frame tail (.error error) → Arguments heap frame (head :: tail) (.error error)
  | cons {head tail value values} : Evaluates heap frame head (.ok value) →
      Arguments heap frame tail (.ok values) → Arguments heap frame (head :: tail) (.ok (value :: values))

inductive Inputs (heap : Heap) (frame : Frame layout) :
    Operand layout → List (Operand layout) → Except Failure (Value × List Value) → Prop where
  | calleeError {callee arguments error} : Evaluates heap frame callee (.error error) →
      Inputs heap frame callee arguments (.error error)
  | argumentError {callee arguments value error} : Evaluates heap frame callee (.ok value) →
      Arguments heap frame arguments (.error error) → Inputs heap frame callee arguments (.error error)
  | ok {callee arguments value values} : Evaluates heap frame callee (.ok value) →
      Arguments heap frame arguments (.ok values) → Inputs heap frame callee arguments (.ok (value, values))

/-- Failure premises inspect the code table, captures and arity. -/
inductive Rejects (table : CodeTable) (arguments : List Value) (heap : Heap) :
    Value → Dispatch.Failure → Prop where
  | nonCallable (value : Int) : Rejects table arguments heap (.int value) (.call (.defined .notCallable))
  | missing (fn : Function) (absent : table fn.code.key = none) :
      Rejects table arguments heap (.function fn) (.missingCode fn.code.key)
  | mismatch (fn : Function) (entry : Dispatch.Entry Body)
      (found : table fn.code.key = some entry) (different : entry.layout ≠ fn.code.layout) :
      Rejects table arguments heap (.function fn) (.layoutMismatch fn.code.layout entry.layout)
  | dangling {fn : Function} {definition : Dispatch.Definition Body fn.code.layout} {identity : CellId}
      (found : Dispatch.Resolves table fn.code definition) (first : Call.firstDangling fn heap = some identity) :
      Rejects table arguments heap (.function fn) (.call (.danglingCell identity))
  | arity {fn : Function} {definition : Dispatch.Definition Body fn.code.layout}
      (found : Dispatch.Resolves table fn.code definition) (live : Call.firstDangling fn heap = none)
      (wrong : arguments.length ≠ definition.parameters.slots.length) :
      Rejects table arguments heap (.function fn)
        (.call (.defined (.positionalArity definition.parameters.slots.length arguments.length)))

/-- Assignment and successful return delivery use the same frame-write relation. -/
inductive Stores (heap : Heap) (frame : Frame layout) (destination : Slot layout) (value : Value)
    (body : Body layout) (stack : Stack) : Transition → Prop where
  | ok {updated frame'} : frame.write heap destination value = .ok (updated, frame') →
      Stores heap frame destination value body stack (none, .running updated frame' body stack)
  | error {failure} : frame.write heap destination value = .error failure →
      Stores heap frame destination value body stack (fail heap stack failure)

/-- The body and delivery rules do not refer to the machine's selector. -/
inductive Step (table : CodeTable) : State → Option Event → State → Prop where
  | ret {heap stack layout} {frame : Frame layout} {operand value} :
      Evaluates heap frame operand (.ok value) →
      Step table (.running heap frame (.ret operand) stack) none (.delivering heap stack (.ok value))
  | retError {heap stack layout} {frame : Frame layout} {operand error} :
      Evaluates heap frame operand (.error error) →
      Step table (.running heap frame (.ret operand) stack) (fail heap stack error).1 (fail heap stack error).2
  | store {heap stack layout} {frame : Frame layout} {destination operand next value transition} :
      Evaluates heap frame operand (.ok value) → Stores heap frame destination value next stack transition →
      Step table (.running heap frame (.store destination operand next) stack) transition.1 transition.2
  | storeError {heap stack layout} {frame : Frame layout} {destination operand next error} :
      Evaluates heap frame operand (.error error) →
      Step table (.running heap frame (.store destination operand next) stack)
        (fail heap stack error).1 (fail heap stack error).2
  | call {heap stack layout} {frame : Frame layout} {destination callee arguments next value values active} :
      Inputs heap frame callee arguments (.ok (value, values)) →
      Dispatch.Dispatches table values heap ⟨layout, frame, ⟨destination, next⟩⟩ stack value active →
      Step table (.running heap frame (.call destination callee arguments next) stack)
        (some (.enter value)) (enter active)
  | callError {heap stack layout} {frame : Frame layout} {destination callee arguments next error} :
      Inputs heap frame callee arguments (.error error) →
      Step table (.running heap frame (.call destination callee arguments next) stack)
        (fail heap stack error).1 (fail heap stack error).2
  | rejected {heap stack layout} {frame : Frame layout} {destination callee arguments next value values error} :
      Inputs heap frame callee arguments (.ok (value, values)) → Rejects table values heap value error →
      Step table (.running heap frame (.call destination callee arguments next) stack)
        (failDispatch heap stack error).1 (failDispatch heap stack error).2
  | complete (heap : Heap) (result : Result) :
      Step table (.delivering heap [] result) (some (.complete result)) (.finished heap result)
  | resume (heap : Heap) (caller : Call.Saved Continuation) (stack : Stack) (result : Result) :
      Step table (.delivering heap (caller :: stack) result) (some (.resume result))
        (.receiving heap caller stack result)
  | receive {heap caller stack value transition} :
      Stores heap caller.frame caller.continuation.destination value caller.continuation.body stack transition →
      Step table (.receiving heap caller stack (.ok value)) transition.1 transition.2
  | receiveError (heap : Heap) (caller : Call.Saved Continuation) (stack : Stack) (error : RuntimeError) :
      Step table (.receiving heap caller stack (.error error)) none (.delivering heap stack (.error error))

def observes : State → Result → Prop
  | .finished _ result, observed => result = observed
  | _, _ => False

def labelled (table : CodeTable) : Semantics.Operational.Labelled State Event Result where
  step := Step table
  observe source outcome := ∃ result, observes source result ∧ outcome = .returned result

end Silmaril.Languages.Python.Core.Closure.Executor

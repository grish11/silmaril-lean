module

public import Silmaril.Languages.Python.Core.Closure.Defs

/-! # Fixed positional call entry and saved-caller delivery -/

@[expose] public section

namespace Silmaril.Languages.Python.Core.Closure.Call

variable {layout : Layout}

abbrev Environment (layout : Layout) := Heap × Frame layout

/-- Write one argument for each ordered destination. -/
def writeArguments : List (ParameterSlot layout × Value) → Environment layout →
    Except Failure (Environment layout)
  | [], before => .ok before
  | (slot, value) :: rest, before =>
    (before.2.write before.1 slot.slot value).bind (writeArguments rest)

inductive Writes : List (ParameterSlot layout × Value) → Environment layout → Environment layout → Prop where
  | nil (before : Environment layout) : Writes [] before before
  | cons {slot : ParameterSlot layout} {value : Value} {rest : List (ParameterSlot layout × Value)}
      {before middle after : Environment layout} :
      before.2.write before.1 slot.slot value = .ok middle →
      Writes rest middle after → Writes ((slot, value) :: rest) before after

/-- A wrong argument count leaves the input environment as the only committed state. -/
def bindPositional (parameters : Parameters layout) (arguments : List Value)
    (before : Environment layout) : Except Failure (Environment layout) :=
  if arguments.length = parameters.slots.length then
    writeArguments (parameters.slots.zip arguments) before
  else
    .error (.defined (.positionalArity parameters.slots.length arguments.length))

/-- Each saved frame retains its own layout and typed continuation. -/
structure Saved (Continuation : Layout → Type) where
  layout : Layout
  frame : Frame layout
  continuation : Continuation layout

structure Entered (Continuation : Layout → Type) (layout : Layout) where
  environment : Environment layout
  stack : List (Saved Continuation)

variable {Continuation : Layout → Type}

/-- Check captured identities against the caller heap before allocating any callee cells. -/
def firstDangling (fn : Function) (heap : Heap) : Option CellId :=
  fn.captures.toList.find? fun identity => decide (heap.next ≤ identity.address)

/-- Expose an initialized callee and the saved caller only after binding succeeds.
Code lookup and continuation execution are supplied by the surrounding machine. -/
def enter (fn : Function) (parameters : Parameters fn.code.layout) (arguments : List Value)
    (heap : Heap) (caller : Saved Continuation) (stack : List (Saved Continuation)) :
    Except Failure (Entered Continuation fn.code.layout) :=
  match firstDangling fn heap with
  | some identity => .error (.danglingCell identity)
  | none =>
    (bindPositional parameters arguments (fn.freshFrame heap)).map fun initialized =>
      ⟨initialized, caller :: stack⟩

inductive Delivery (Continuation : Layout → Type) where
  | terminal (result : Result)
  | resume (caller : Saved Continuation) (result : Result)

structure Exit (Continuation : Layout → Type) where
  heap : Heap
  stack : List (Saved Continuation)
  delivery : Delivery Continuation

/-- Deliver either a result or a defined error with the current shared heap.
A saved frame carries the continuation's local bindings and cell identities. -/
def finish (heap : Heap) (stack : List (Saved Continuation)) (result : Result) : Exit Continuation :=
  match stack with
  | [] => ⟨heap, [], .terminal result⟩
  | caller :: rest => ⟨heap, rest, .resume caller result⟩

end Silmaril.Languages.Python.Core.Closure.Call

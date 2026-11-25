module

import Silmaril.Languages.Python.Core.Closure.Dispatch.Thms

open Silmaril.Languages.Python.Core.Closure
open Silmaril.Languages.Python.Core.Closure.Dispatch

private def calleeRef : CodeRef := ⟨1, ⟨1, 0, 0⟩⟩
private def fn : Function := Function.ofCaptureList calleeRef [] rfl
private def index : Fin calleeRef.layout.locals := ⟨0, by decide⟩

-- This fixture uses a body that returns the value read from a single slot.
private def definition : Definition Slot calleeRef.layout :=
  ⟨⟨[.local index], by decide⟩, .local index⟩

private def table : CodeTable Slot :=
  fun key => if key = calleeRef.key then some ⟨calleeRef.layout, definition⟩ else none

private def saved : Call.Saved (fun _ => Unit) :=
  ⟨⟨0, 0, 0⟩, (Frame.fresh Heap.empty Fin.elim0).2, ()⟩

example : resolve table calleeRef = .ok definition := resolve_iff.mpr rfl

example : (do
    let active ← dispatch table (.function fn) [.int (-7)] Heap.empty saved []
    pure (active.entered.environment.2.read active.entered.environment.1 active.definition.body)) =
      .ok (.ok (.int (-7))) := rfl

example : dispatch table (.function fn) [] Heap.empty saved [] =
    .error (.call (.defined (.positionalArity 1 0))) := rfl

example : dispatch table (.int 1) [] Heap.empty saved [] =
    .error (.call (.defined .notCallable)) := rfl

private def missingRef : CodeRef := ⟨2, calleeRef.layout⟩
private def wrongRef : CodeRef := ⟨calleeRef.key, ⟨0, 0, 0⟩⟩

example : dispatch table (.function (Function.ofCaptureList missingRef [] rfl)) [] Heap.empty saved [] =
    .error (.missingCode missingRef.key) := rfl

example : dispatch table (.function (Function.ofCaptureList wrongRef [] rfl)) [] Heap.empty saved [] =
    .error (.layoutMismatch wrongRef.layout calleeRef.layout) := rfl

#print axioms resolve_iff
#print axioms dispatch_iff

module

import Silmaril.Languages.Python.Core.Closure.Finite.Dispatch.Thms
meta import Silmaril.Languages.Python.Core.Closure.Finite.Dispatch.Defs
meta import Silmaril.Languages.Python.Core.Closure.Finite.Defs
meta import Silmaril.Languages.Python.Core.Closure.Dispatch.Defs
meta import Silmaril.Languages.Python.Core.Closure.Call.Defs
meta import Silmaril.Languages.Python.Core.Closure.Defs
meta import Mathlib.Data.List.AList

open Silmaril.Languages.Python.Core.Closure
open Silmaril.Languages.Python.Core.Closure.Finite
open Silmaril.Languages.Python.Core.Closure.Finite.Dispatch

private abbrev calleeLayout : Layout := ⟨0, 1, 1⟩
private abbrev callerLayout : Layout := ⟨0, 0, 1⟩
private def definition : Silmaril.Languages.Python.Core.Closure.Dispatch.Definition Slot calleeLayout :=
  ⟨⟨[.owned 0], by decide⟩, .capture 0⟩
private def rows : CodeRows Slot := (∅ : CodeRows Slot).insert 1 ⟨calleeLayout, definition⟩
private def fn : Function := Function.ofCaptureList ⟨1, calleeLayout⟩ [⟨0⟩] rfl
private def caller : Call.Saved (fun _ => Nat) :=
  ⟨callerLayout, ⟨Fin.elim0, Fin.elim0, fun _ => ⟨0⟩⟩, 42⟩
private def heap : HeapTable := HeapTable.empty.reserve 1

example : Silmaril.Languages.Python.Core.Closure.Dispatch.resolve rows.project fn.code = .ok definition := rfl

example : dispatch rows (.function fn) [] heap caller [] =
    .error (.call (.defined (.positionalArity 1 0))) := rfl

example : dispatch rows (.function (Function.ofCaptureList ⟨2, calleeLayout⟩ [⟨0⟩] rfl)) [] heap caller [] =
    .error (.missingCode 2) := rfl

example : dispatch rows (.function (Function.ofCaptureList ⟨1, callerLayout⟩ [⟨0⟩] rfl)) [] heap caller [] =
    .error (.layoutMismatch callerLayout calleeLayout) := rfl

#guard
  match dispatch rows (.function fn) [.int 17] heap caller [caller] with
  | .ok active =>
    match active.environment.heap.rows.lookup 1, active.environment.heap.write ⟨0⟩ (.int 23) with
    | some (.int 17), some residual =>
      let exit := finish residual active.stack (.error .notCallable)
      match exit.delivery, exit.stack, exit.heap.rows.lookup 0, exit.heap.rows.lookup 1 with
      | .resume saved (.error .notCallable), [older], some (.int 23), some (.int 17) =>
        saved.continuation == 42 && older.continuation == 42 && exit.heap.next == 2
      | _, _, _, _ => false
    | _, _ => false
  | .error _ => false

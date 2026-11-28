module

import Silmaril.Languages.Python.Core.Closure.Executor.TupleReturn.Thms
import Silmaril.Languages.Python.Core.Closure.Finite.Executor.Thms
meta import Silmaril.Languages.Python.Core.Closure.Finite.Executor.Defs
meta import Silmaril.Languages.Python.Core.Closure.Finite.Dispatch.Defs
meta import Silmaril.Languages.Python.Core.Closure.Finite.Defs
meta import Silmaril.Languages.Python.Core.Closure.Executor.Defs
meta import Silmaril.Languages.Python.Core.Closure.Defs
meta import Silmaril.Languages.Python.Core.Module.Defs
meta import Mathlib.Data.List.AList

namespace Silmaril.Languages.Python.Core.Closure.Finite.Executor

private abbrev calleeLayout : Layout := ⟨1, 0, 1⟩
private abbrev callerLayout : Layout := ⟨1, 0, 0⟩

private def heap : HeapTable := (HeapTable.empty.reserve 1).bind ⟨0⟩ (.int 12) (by decide)
private def callee : Frame calleeLayout := ⟨fun _ => some (.bool true), Fin.elim0, fun _ => ⟨0⟩⟩
private def caller : Call.Saved Closure.Executor.Continuation :=
  ⟨callerLayout, ⟨fun _ => none, Fin.elim0, Fin.elim0⟩, some (.store (.local 0), .ret (.read (.local 0)))⟩

private def result (items : List (TupleItem calleeLayout)) : List Closure.Executor.Event × State :=
  runPrefixIn (∅ : CodeRows) (fun name => if name = "live" then some (.int 23) else none)
    8 (.running ⟨heap, callee⟩ (.ret (.tuple items)) [caller])

#guard
  match result [.read (.capture 0), .literal .none, .read (.local 0), .global "live"] with
  | ([.resume (.ok (.tuple observed)), .complete (.ok (.tuple completed))], .finished residual (.ok (.tuple final))) =>
    observed == [.int 12, .none, .bool true, .int 23] && completed == observed && final == observed &&
      residual.next == 1 && (match residual.rows.lookup 0 with | some (.int 12) => true | _ => false)
  | _ => false

#guard
  match result [.read (.capture 0), .global "first_missing", .global "second_missing"] with
  | ([.resume (.error (.nameError a)), .complete (.error (.nameError b))],
      .finished residual (.error (.nameError c))) =>
    a == "first_missing" && b == a && c == a && residual.next == 1 &&
      (match residual.rows.lookup 0 with | some (.int 12) => true | _ => false)
  | _ => false

end Silmaril.Languages.Python.Core.Closure.Finite.Executor

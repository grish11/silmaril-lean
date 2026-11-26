module

import Silmaril.Languages.Python.Core.Closure.Call.Variadic.Thms
import Silmaril.Languages.Python.Core.Closure.Call.Variadic.Finite.Thms
meta import Silmaril.Languages.Python.Core.Closure.Call.Variadic.Defs
meta import Silmaril.Languages.Python.Core.Closure.Call.Variadic.Finite.Defs
meta import Silmaril.Languages.Python.Core.Closure.Call.Defs
meta import Silmaril.Languages.Python.Core.Closure.Defs
meta import Silmaril.Languages.Python.Core.Closure.Finite.Defs
meta import Silmaril.Languages.Python.Core.Module.Defs

namespace Silmaril.Languages.Python.Core.Closure.Call.Variadic

private abbrev layout : Layout := ⟨1, 1, 1⟩
private def rest : ParameterSlot layout := .owned 0
private def signature : VariadicParameters layout := ⟨⟨[.local 0], by decide⟩, rest, by decide⟩
private abbrev original : Function := .ofCaptureList ⟨7, layout⟩ [⟨0⟩] rfl
private abbrev replacement : Function := .ofCaptureList ⟨8, layout⟩ [⟨0⟩] rfl

private def finiteHeap : Finite.HeapTable :=
  (Finite.HeapTable.empty.reserve 1).bind ⟨0⟩ (.int 37) (by decide)

private structure CallerState where
  heap : Heap
  live : Function
  reads : List String

private def beginCall : CallerState := ⟨finiteHeap.project, original, []⟩

private def read : ReadOperand String CallerState := fun operand before =>
  let reached := { before with reads := before.reads ++ [operand] }
  let write (value : Int) := (reached.heap.write ⟨0⟩ (.int value)).getD reached.heap
  match operand with
  | "callee" => (.ok (.function reached.live), reached)
  | "first" => (.ok (.bool false), { reached with heap := write 41, live := replacement })
  | "spread" => (.ok (.tuple [.int 3, .none]), { reached with heap := write 42 })
  | "after" => (.ok (.int 8), reached)
  | "empty" => (.ok (.tuple []), reached)
  | "bad" => (.ok (.int 11), { reached with heap := write 43 })
  | missing => (.error (.defined (.nameError missing)), { reached with heap := write 44 })

private def caller : Saved (fun _ => Unit) :=
  ⟨⟨0, 0, 0⟩, ⟨fun _ => none, Fin.elim0, Fin.elim0⟩, ()⟩

#guard
  let (selected, reached) := preparePositionalCall read "callee"
    [.single "first", .starred "spread", .single "after"] beginCall
  match selected with
  | .ok (.function fn, supplied) =>
    match signature.enter original supplied reached.heap caller [] with
    | .ok entered =>
      let (heap, frame) := entered.environment
      fn == original && reached.live == replacement && reached.reads == ["callee", "first", "spread", "after"] &&
        heap.next == 2 &&
        (match frame.read heap (.local ⟨0, by decide⟩), frame.read heap (.owned ⟨0, by decide⟩), heap.lookup ⟨0⟩ with
        | .ok (.bool false), .ok (.tuple values), some (some (.int 42)) => values == [.int 3, .none, .int 8]
        | _, _, _ => false)
    | .error _ => false
  | _ => false

#guard
  let (result, reached) := preparePositionalCall read "callee" [.starred "bad", .single "missing"] beginCall
  reached.reads == ["callee", "bad"] &&
    (match result, reached.heap.lookup ⟨0⟩ with
    | .error .notIterable, some (some (.int 43)) => true
    | _, _ => false)

#guard
  let (result, reached) := preparePositionalCall read "callee" [.starred "empty", .single "missing"] beginCall
  reached.reads == ["callee", "empty", "missing"] &&
    (match result, reached.heap.lookup ⟨0⟩ with
    | .error (.operand (.defined (.nameError "missing"))), some (some (.int 44)) => true
    | _, _ => false)

#guard
  let (result, reached) := preparePositionalCall read "missing_callee" [.starred "bad"] beginCall
  reached.reads == ["missing_callee"] &&
    (match result with
    | .error (.operand (.defined (.nameError "missing_callee"))) => true
    | _ => false)

example : signature.enter original [] finiteHeap.project caller [] =
    .error (.defined (.positionalArity 1 0)) := rfl

example : signature.enter original [.int 2, .tuple []] finiteHeap.project caller [] =
    .error .unsupportedTupleElement := rfl

#guard
  match Finite.Variadic.enter original signature [.tuple [.int 2]] finiteHeap with
  | .ok state =>
    state.heap.next == 2 &&
      (match state.frame.read state.heap.project (.local ⟨0, by decide⟩), state.heap.rows.lookup 1, state.heap.rows.lookup 0 with
      | .ok (.tuple fixed), some (.tuple []), some (.int 37) => fixed == [.int 2]
      | _, _, _ => false)
  | .error _ => false

end Silmaril.Languages.Python.Core.Closure.Call.Variadic

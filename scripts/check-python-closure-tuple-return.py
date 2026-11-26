# SPDX-License-Identifier: MIT
"""Compare checked scalar tuple returns and settlement with CPython 3.13.5."""

from contextlib import redirect_stderr, redirect_stdout
from io import StringIO
from pathlib import Path
import runpy
import sys
import tempfile


DIRECT = """live = 6
def pack(a, b, c):
    def keep():
        return a
    return (a, b, c, None, True, live)
alias = pack
first = alias(11, 22, 33)
live = 9
second = alias(44, 55, 66)
empty = lambda: ()
blank = empty()
assert not blank
"""

FORWARDED = """live = 6
def pack(a):
    def middle():
        def leaf():
            return (a, live)
        return leaf()
    return middle()
live = 9
answer = pack(11)
"""

ERROR = """answer = 77
def pack(a):
    def keep():
        return a
    return (a, pack, first_missing, second_missing)
answer = pack(11)
"""

OUTSIDE = ERROR.replace(", first_missing, second_missing", "")

COMMON = """
open Silmaril.Languages.Python
open Compile.ModuleEntry.Functions.Run
open Core.Module.SeededCall (Namespace Value Result)

private def initialHeap : Core.Closure.Heap :=
  ⟨1, fun index => if index = 0 then some (.int 37) else none⟩

private def contents (heap : Core.Closure.Heap) : List (Option Value) :=
  (List.range heap.next).map fun index => (heap.contents index).map Seeded.seededValue

private def ordinary (source : Source.Module) (completion : Completion)
    (bindings : List (String × Value)) (cells : List Value) : Bool := Id.run do
  let .ok compiled := compile source | return false
  let initial := State.ready (seed .empty initialHeap) compiled.instructions
  let .finished plain status := (runPrefix compiled.table 256 initial).2 | return false
  return status == completion && contents plain.heap == cells.map some &&
    bindings.all (fun (name, value) => (plain.globals name).map Seeded.seededValue == some value)

private def seeded (source : Source.Module) (completion : Except Seeded.ModuleFailure Unit)
    (bindings : List (String × Value)) (cells : List Value) (receipts : List (String × Result))
    (published : Core.Module.SeededCall.Namespace → Bool := fun _ => true) : Bool := Id.run do
  let .ok compiled := compile source | return false
  let spaces : List Namespace := [.empty, Seeded.legacySeed .builtin, Seeded.legacySeed .preamble]
  return spaces.all fun space =>
    let result := Seeded.run space compiled initialHeap
    result.completion == completion && result.residual.builtins == space.builtins &&
      result.lists.objects.isEmpty &&
      contents result.heap == cells.map some && published result.residual &&
      bindings.all (fun (name, value) => result.residual.lookupGlobal name == some value) &&
      result.calls.map (fun call => (call.callee, call.observation.result)) == receipts &&
      result.calls.all (fun call => call.observation.caught.isNone)
"""

DIRECT_CHECK = """
private def first : Value := .returnedTuple [.int 11, .int 22, .int 33, .none, .bool true, .int 6]
private def second : Value := .returnedTuple [.int 44, .int 55, .int 66, .none, .bool true, .int 9]

#guard ordinary pythonSource .normal [("first", first), ("second", second), ("live", .int 9), ("blank", .returnedTuple [])]
  [.int 37, .int 11, .int 44]
#guard seeded pythonSource (.ok ()) [("first", first), ("second", second), ("live", .int 9), ("blank", .returnedTuple [])]
  [.int 37, .int 11, .int 44] [("alias", .ok first), ("alias", .ok second), ("empty", .ok (.returnedTuple []))]
  (fun residual => residual.lookupGlobal "alias" == residual.lookupGlobal "pack")

private def interrupted (source : Source.Module) : Bool := Id.run do
  let .ok compiled := compile source | return false
  let noFuel := Seeded.run .empty compiled initialHeap 0
  let some (.function closure) := noFuel.residual.lookupGlobal "alias" | return false
  let imported := (Namespace.empty.bindGlobal "foreign" (.function closure))
  let calls := [(.call (.bindGlobal "result") "foreign" [.literal (.int 1), .literal (.int 2), .literal (.int 3)] :
    Instruction compiled.checked.tree.scope)]
  let declined := Seeded.runInstructions imported calls compiled.table initialHeap
  let masked := imported.bindGlobal "foreign" (.int 0)
  let rejected := Seeded.runInstructions masked calls compiled.table initialHeap
  return noFuel.completion == .error .directCallFuelExhausted &&
    noFuel.calls.isEmpty && noFuel.residual.lookupGlobal "first" == none &&
    contents noFuel.heap == [some (.int 37)] &&
    declined.completion == .error .unsupported && declined.residual.moduleGlobals == imported.moduleGlobals &&
    contents declined.heap == [some (.int 37)] &&
    rejected.completion == .error (.raised (.runtime .notCallable)) &&
    rejected.residual.moduleGlobals == masked.moduleGlobals && contents rejected.heap == [some (.int 37)]

#guard interrupted pythonSource
"""

FORWARDED_CHECK = """
#guard ordinary pythonSource .normal [("answer", .returnedTuple [.int 11, .int 9])] [.int 37, .int 11]
"""

ERROR_CHECK = """
#guard ordinary pythonSource (.raised (.nameError "first_missing")) [("answer", .int 77)] [.int 37, .int 11]
#guard seeded pythonSource (.error (.raised (.runtime (.nameError "first_missing")))) [("answer", .int 77)]
  [.int 37, .int 11] [("pack", .error (.raised (.runtime (.nameError "first_missing"))))]
"""

OUTSIDE_CHECK = """
#guard ordinary pythonSource (.executorFault .unsupportedTupleElement) [("answer", .int 77)] [.int 37, .int 11]
#guard seeded pythonSource (.error (.directCallFault .unsupportedTupleElement)) [("answer", .int 77)]
  [.int 37, .int 11] []
"""


def cpython(source, missing=None):
    namespace = {"__builtins__": {}}
    with redirect_stdout(StringIO()) as stdout, redirect_stderr(StringIO()) as stderr:
        try:
            exec(compile(source, "<checked tuple return>", "exec", dont_inherit=True, optimize=0), namespace)
        except NameError as error:
            assert missing == error.name
        else:
            assert missing is None
    assert stdout.getvalue() == stderr.getvalue() == ""
    assert namespace.pop("__builtins__") == {}
    return namespace


def assert_tuple(actual, expected):
    assert type(actual) is tuple and len(actual) == len(expected)
    assert all(type(left) is type(right) and left == right for left, right in zip(actual, expected))


if __name__ == "__main__":
    assert sys.version_info[:3] == (3, 13, 5)
    normal = cpython(DIRECT)
    assert normal["alias"] is normal["pack"]
    assert normal["pack"].__code__.co_cellvars == ("a",)
    assert_tuple(normal["first"], (11, 22, 33, None, True, 6))
    assert_tuple(normal["second"], (44, 55, 66, None, True, 9))
    assert_tuple(normal["blank"], ())
    assert_tuple(cpython(FORWARDED)["answer"], (11, 9))
    assert cpython(ERROR, "first_missing")["answer"] == 77
    outside = cpython(OUTSIDE)
    assert outside["answer"][0] == 11 and outside["answer"][1] is outside["pack"]

    root = Path(__file__).resolve().parents[1] / "tests/languages/python"
    shared = runpy.run_path(str(root / "source-scope/check_intake.py"))
    imports = runpy.run_path(str(root / "source-module-entry/check_return_local_call.py"))["IMPORTS"]
    with tempfile.TemporaryDirectory() as tmp:
        source, lean = Path(tmp) / "TupleReturn.py", Path(tmp) / "TupleReturn.lean"
        for body, checks in ((DIRECT, DIRECT_CHECK), (FORWARDED, FORWARDED_CHECK),
                             (ERROR, ERROR_CHECK), (OUTSIDE, OUTSIDE_CHECK)):
            shared["emit"](source, lean, body)
            shared["check_lean"](lean, COMMON + checks, extra_imports=imports)
    print("CPython 3.13.5 and Lean checked tuple tags, forwarding, lookup order and settlement.")

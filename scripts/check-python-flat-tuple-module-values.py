# SPDX-License-Identifier: MIT
"""Check flat tuple bindings, live reads and linked operands with CPython 3.13.5."""

from pathlib import Path
import runpy
import sys
import tempfile

SNAPSHOTS = """live = 7
current = (live, True, None, False, -2)
alias = current
live = 9
current = (live,)
snapshot = alias
alias = ()
"""

LINKED = SNAPSHOTS + """def read():
    return snapshot
___assertEqual(read(), (live, False, None))
"""

ORDINARY = SNAPSHOTS + """def echo(value):
    def retain():
        return value
    return value
def deliver(value):
    return value
answer = deliver(echo((live, None, True)))
"""

BEFORE = """saved = (9,)
present = (1,)
"""

ITEM_FAILURE = BEFORE + "saved = (present, missing_item)\nunreached = 4\n"
MASKED_CALL = BEFORE + "target = 0\ntarget((present, missing_item))\nunreached = 4\n"
MISSING_CALLEE = BEFORE + "absent((present, missing_item))\nunreached = 4\n"
OUTSIDE = BEFORE + "saved = (present,)\nunreached = 4\n"

COMMON = r"""
open Silmaril.Languages.Python
open Compile.ModuleEntry.Functions.Run
open Core.Module.SeededCall (Namespace Value Result)

private def initialHeap : Core.Closure.Heap :=
  ⟨1, fun i => if i = 0 then some (.int 37) else none⟩

private def cells (heap : Core.Closure.Heap) : List (Option Value) :=
  (List.range heap.next).map fun index => (heap.contents index).map Seeded.seededValue

private def ordinary (source : Source.Module) (status : Completion) (bindings : List (String × Value))
    (heap : List Value := [.int 37]) : Bool := Id.run do
  let .ok compiled := compile source | return false
  let .finished residual completion :=
    (runPrefix compiled.table 256 (.ready (seed .empty initialHeap) compiled.instructions)).2 | return false
  return completion == status && cells residual.heap == heap.map some && (residual.globals "unreached").isNone &&
    bindings.all (fun (name, expected) => (residual.globals name).map Seeded.seededValue == some expected)

private def seeded (source : Source.Module) (status : Except Seeded.ModuleFailure Unit)
    (bindings : List (String × Value)) (receipts : List (String × Result) := [])
    (spaces : List Namespace := [.empty, Seeded.legacySeed .builtin, Seeded.legacySeed .preamble]) : Bool := Id.run do
  let .ok compiled := compile source | return false
  return spaces.all fun space =>
    let observed := Seeded.run space compiled initialHeap
    observed.completion == status && cells observed.heap == [some (.int 37)] &&
    observed.lists.objects.isEmpty && observed.residual.builtins == space.builtins &&
    (observed.residual.lookupGlobal "unreached").isNone &&
    bindings.all (fun (name, expected) => observed.residual.lookupGlobal name == some expected) &&
    observed.calls.map (fun call => (call.callee, call.observation.result)) == receipts &&
    observed.calls.all (fun call => call.observation.caught.isNone)

private def resolvedTupleOperands (source : Source.Module) : Bool := Id.run do
  let .ok compiled := compile source | return false
  let .nestedCall .discard "___assertEqual" [_, .scalar tuple] :: _ :=
    compiled.instructions.reverse | return false
  let space := (Seeded.legacySeed .builtin).bindGlobal "live" (.int 21)
  let outcome := Seeded.observeArgumentIn space { table := compiled.table, heap := initialHeap, fuel := 15 }
    (.scalar tuple)
  let seededOnly := (Core.Module.SeededCall.Operand.tuple [.global "___assertEqual", .global "missing_item"]).eval space #v[]
  return outcome.1 == .ok (.returnedTuple [.int 21, .bool false, .none]) &&
    outcome.2.1.isEmpty && cells outcome.2.2 == [some (.int 37)] &&
    seededOnly == .error (.raised (.runtime (.nameError "missing_item")))
"""


def execute(source, error_name=None, supply=False):
    def equal(left, right):
        assert type(left) is tuple and type(right) is tuple
        assert [(type(x), x) for x in left] == [(int, 7), (bool, True), (type(None), None), (bool, False), (int, -2)]
        assert [(type(x), x) for x in right] == [(int, 9), (bool, False), (type(None), None)]

    namespace = {"__builtins__": {"___assertEqual": equal} if supply else {}}
    try:
        exec(compile(source, "<module tuple>", "exec", dont_inherit=True, optimize=0), namespace)
    except NameError as error:
        assert error.name == error_name
    else:
        assert error_name is None
    return namespace


def main():
    assert sys.version_info[:3] == (3, 13, 5)
    actual = execute(SNAPSHOTS)
    assert [(type(x), x) for x in actual["snapshot"]] == [
        (int, 7), (bool, True), (type(None), None), (bool, False), (int, -2)]
    assert actual["alias"] == () and actual["current"] == (9,)
    assert [(type(x), x) for x in execute(ORDINARY)["answer"]] == [(int, 9), (type(None), None), (bool, True)]
    execute(LINKED, "___assertEqual")
    execute(LINKED, supply=True)
    original = '[("saved", .returnedTuple [.int 9]), ("present", .returnedTuple [.int 1])]'
    snapshot = '.returnedTuple [.int 7, .bool true, .none, .bool false, .int (-2)]'
    controls = [
        (SNAPSHOTS, f'''
#guard ordinary pythonSource .normal
  [("snapshot", {snapshot}), ("current", .returnedTuple [.int 9]), ("alias", .returnedTuple [])]
#guard seeded pythonSource (.ok ())
  [("snapshot", {snapshot}), ("current", .returnedTuple [.int 9]), ("alias", .returnedTuple [])]
'''),
        (ORDINARY, '''
#guard ordinary pythonSource .normal [("answer", .returnedTuple [.int 9, .none, .bool true])]
  [.int 37, .returnedTuple [.int 9, .none, .bool true]]
'''),
        (LINKED, f'''
#guard ordinary pythonSource (.raised (.nameError "___assertEqual")) [("snapshot", {snapshot})]
#guard seeded pythonSource (.error .unsupported) [("snapshot", {snapshot})]
  [("read", .ok ({snapshot})), ("___assertEqual", .error .unsupported)]
  [Seeded.legacySeed .builtin, Seeded.legacySeed .preamble]
#guard resolvedTupleOperands pythonSource
'''),
        (OUTSIDE, f'''
#guard ordinary pythonSource (.executorFault .unsupportedTupleElement) {original}
#guard seeded pythonSource (.error .unsupported) {original}
'''),
        ("answer = ((1,),)\n", '''
#guard (match compile pythonSource with | .error (.source (.scalar .expressionProfile)) => true | _ => false)
'''),
    ]
    for source, missing in ((ITEM_FAILURE, "missing_item"), (MASKED_CALL, "missing_item"),
                            (MISSING_CALLEE, "absent")):
        residual = execute(source, missing)
        assert residual["saved"] == (9,) and "unreached" not in residual
        controls.append((source, f'''
#guard ordinary pythonSource (.raised (.nameError "{missing}")) {original}
#guard seeded pythonSource (.error (.raised (.runtime (.nameError "{missing}")))) {original}
'''))

    root = Path(__file__).resolve().parents[1] / "tests/languages/python"
    shared = runpy.run_path(str(root / "source-scope/check_intake.py"))
    imports = runpy.run_path(str(root / "source-module-entry/check_return_local_call.py"))["IMPORTS"]
    with tempfile.TemporaryDirectory() as directory:
        source, lean = Path(directory) / "ModuleTuple.py", Path(directory) / "ModuleTuple.lean"
        chunks = []
        for i, (raw, control) in enumerate(controls):
            shared["emit"](source, lean, raw)
            header, declaration = lean.read_text().split("public def pythonSource", 1)
            chunks.append(f"namespace Case{i}\npublic def pythonSource{declaration}\n{control}\nend Case{i}")
        lean.write_text(header + COMMON + "\n".join(chunks))
        shared["check_lean"](lean, "", extra_imports=imports)
    print("CPython 3.13.5 and Lean checked module tuple tags, alias snapshots, linked operands, and failure order.")


if __name__ == "__main__":
    main()

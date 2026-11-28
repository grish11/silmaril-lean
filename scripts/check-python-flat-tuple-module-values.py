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
carried = echo(snapshot)
"""

FRESH = """item = 1
first = (item, True, None)
alias = first
second = (item, True, None)
empty = ()
other_empty = ()
closed = (1,)
"""

EQUALITY = FRESH + """___assertEqual(first, second)
___assertEqual(first, (1, 1, None))
___assertEqual((True, 1, None), second)
"""

STOCK = FRESH + """copy = tuple(alias)
copy_empty = tuple(empty)
saved_builtin = tuple
tuple = 0
tuple = saved_builtin
first = (item, True, None)
restored = tuple(first)
"""

MASKED_TUPLE = FRESH + "tuple = 0\ncopy = tuple(alias)\nunreached = 4\n"
MASKED_TUPLE_READ = FRESH + "tuple = 0\ncopy = tuple(missing_item)\nunreached = 4\n"

BEFORE = """live = 9
saved = (live,)
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
    (spaces : List Namespace := [.empty, Seeded.legacySeed .builtin, Seeded.legacySeed .preamble])
    (heap : List Value := [.int 37]) : Bool := Id.run do
  let .ok compiled := compile source | return false
  return spaces.all fun space =>
    let observed := Seeded.run space compiled initialHeap
    observed.completion == status && cells observed.heap == heap.map some &&
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


def execute(source, error_name=None, supply=False, stock_tuple=False):
    def equal(left, right):
        assert type(left) is tuple and type(right) is tuple
        if source == LINKED:
            assert [(type(x), x) for x in left] == [
                (int, 7), (bool, True), (type(None), None), (bool, False), (int, -2)]
            assert [(type(x), x) for x in right] == [(int, 9), (bool, False), (type(None), None)]
        assert left == right, (left, right)

    builtins = {"___assertEqual": equal} if supply else {}
    if stock_tuple:
        builtins["tuple"] = tuple
    namespace = {"__builtins__": builtins}
    try:
        exec(compile(source, "<module tuple>", "exec", dont_inherit=True, optimize=0), namespace)
    except NameError as error:
        assert error.name == error_name
    except TypeError:
        assert error_name is TypeError
    else:
        assert error_name is None
    return namespace


def main():
    assert sys.version_info[:3] == (3, 13, 5)
    actual = execute(SNAPSHOTS)
    assert [(type(x), x) for x in actual["snapshot"]] == [
        (int, 7), (bool, True), (type(None), None), (bool, False), (int, -2)]
    assert actual["alias"] == () and actual["current"] == (9,)
    ordinary_namespace = execute(ORDINARY)
    assert [(type(x), x) for x in ordinary_namespace["answer"]] == [(int, 9), (type(None), None), (bool, True)]
    assert ordinary_namespace["carried"] is ordinary_namespace["snapshot"]
    execute(LINKED, "___assertEqual")
    try:
        execute(LINKED, supply=True)
    except AssertionError as error:
        assert error.args == (((7, True, None, False, -2), (9, False, None)),)
    else:
        raise AssertionError("tuple mismatch completed")
    fresh = execute(FRESH)
    assert fresh["first"] == fresh["second"] and fresh["first"] is not fresh["second"]
    assert fresh["first"] is fresh["alias"] and fresh["empty"] is fresh["other_empty"]
    execute(EQUALITY, supply=True)
    stock = execute(STOCK, stock_tuple=True)
    assert stock["copy"] is stock["alias"] and stock["copy_empty"] is stock["empty"]
    assert stock["restored"] is stock["first"] and stock["first"] is not stock["alias"]
    assert "copy" not in execute(STOCK, "tuple")
    assert "copy" not in execute(MASKED_TUPLE, TypeError, stock_tuple=True)
    assert "copy" not in execute(MASKED_TUPLE_READ, "missing_item", stock_tuple=True)

    saved = '.tupleObject ⟨some 1, [.int 9]⟩'
    original = f'[("saved", {saved}), ("present", .returnedTuple [.int 1])]'
    prior_heap = '[.int 37, .returnedTuple [.int 9]]'
    contents = '[.int 7, .bool true, .none, .bool false, .int (-2)]'
    snapshot = f'.tupleObject ⟨some 1, {contents}⟩'
    mismatch = f'.raised (.assertionError (.tuplePair {contents} [.int 9, .bool false, .none]))'
    snapshot_heap = f'[.int 37, .returnedTuple {contents}, .returnedTuple [.int 9]]'
    snapshot_bindings = f'[("snapshot", {snapshot}), ("current", .tupleObject ⟨some 2, [.int 9]⟩), ("alias", .returnedTuple [])]'
    first = '.tupleObject ⟨some 1, [.int 1, .bool true, .none]⟩'
    second = '.tupleObject ⟨some 2, [.int 1, .bool true, .none]⟩'
    third = '.tupleObject ⟨some 3, [.int 1, .bool true, .none]⟩'
    fresh_bindings = (f'[("first", {first}), ("second", {second}), ("alias", {first}), '
                      '("empty", .returnedTuple []), ("other_empty", .returnedTuple []), ("closed", .returnedTuple [.int 1])]')
    pair = '.returnedTuple [.int 1, .bool true, .none]'
    fresh_heap = f'[.int 37, {pair}, {pair}]'
    legacy_seeds = '[.empty, Seeded.legacySeed .builtin, Seeded.legacySeed .preamble]'
    tuple_seeds = '[Seeded.legacyTupleSeed .builtin, Seeded.legacyTupleSeed .preamble]'
    controls = [
        (SNAPSHOTS, f'''
#guard ordinary pythonSource .normal {snapshot_bindings} {snapshot_heap}
#guard seeded pythonSource (.ok ()) {snapshot_bindings} [] {legacy_seeds} {snapshot_heap}
'''),
        (ORDINARY, f'''
#guard ordinary pythonSource .normal
  [("answer", .returnedTuple [.int 9, .none, .bool true]), ("carried", {snapshot})]
  [.int 37, .returnedTuple {contents}, .returnedTuple [.int 9], .returnedTuple [.int 9, .none, .bool true], {snapshot}]
'''),
        (LINKED, f'''
#guard ordinary pythonSource (.raised (.nameError "___assertEqual")) [("snapshot", {snapshot})] {snapshot_heap}
#guard seeded pythonSource (.error ({mismatch})) [("snapshot", {snapshot})]
  [("read", .ok ({snapshot})), ("___assertEqual", .error ({mismatch}))]
  [Seeded.legacySeed .builtin, Seeded.legacySeed .preamble] {snapshot_heap}
#guard resolvedTupleOperands pythonSource
'''),
        (FRESH, f'''
#guard ordinary pythonSource .normal {fresh_bindings} {fresh_heap}
#guard seeded pythonSource (.ok ()) {fresh_bindings} [] {tuple_seeds} {fresh_heap}
'''),
        (EQUALITY, f'''
#guard seeded pythonSource (.ok ()) {fresh_bindings}
  (List.replicate 3 ("___assertEqual", .ok .none))
  [Seeded.legacySeed .builtin, Seeded.legacySeed .preamble] {fresh_heap}
'''),
        (STOCK, f'''
#guard ordinary pythonSource (.raised (.nameError "tuple")) {fresh_bindings} {fresh_heap}
#guard seeded pythonSource (.error (.raised (.runtime (.nameError "tuple"))))
  {fresh_bindings} [("tuple", .error (.raised (.runtime (.nameError "tuple"))))]
  {legacy_seeds} {fresh_heap}
#guard seeded pythonSource (.ok ())
  [("first", {third}), ("second", {second}), ("alias", {first}), ("copy", {first}),
    ("copy_empty", .returnedTuple []), ("restored", {third}), ("tuple", .builtin .tuple)]
  [("tuple", .ok ({first})), ("tuple", .ok (.returnedTuple [])), ("tuple", .ok ({third}))]
  {tuple_seeds} [.int 37, {pair}, {pair}, {pair}]
'''),
        (MASKED_TUPLE, f'''
#guard seeded pythonSource (.error (.raised (.runtime .notCallable))) {fresh_bindings}
  [("tuple", .error (.raised (.runtime .notCallable)))] {tuple_seeds} {fresh_heap}
'''),
        (MASKED_TUPLE_READ, f'''
#guard seeded pythonSource (.error (.raised (.runtime (.nameError "missing_item")))) {fresh_bindings}
  [("tuple", .error (.raised (.runtime (.nameError "missing_item"))))] {tuple_seeds} {fresh_heap}
'''),
        (OUTSIDE, f'''
#guard ordinary pythonSource (.executorFault .unsupportedTupleElement) {original} {prior_heap}
#guard seeded pythonSource (.error .unsupported) {original} [] {legacy_seeds} {prior_heap}
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
#guard ordinary pythonSource (.raised (.nameError "{missing}")) {original} {prior_heap}
#guard seeded pythonSource (.error (.raised (.runtime (.nameError "{missing}"))))
  {original} [] {legacy_seeds} {prior_heap}
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
    print("CPython 3.13.5 and Lean checked module tuple identities, exact heaps, alias snapshots, and reached failures.")


if __name__ == "__main__":
    main()

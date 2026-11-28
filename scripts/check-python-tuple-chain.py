# SPDX-License-Identifier: MIT
"""Check exact tuple methods, equality chains, and live identity operands."""

import argparse
import ast
from contextlib import redirect_stderr, redirect_stdout
from io import StringIO
import json
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile
import warnings

DIRECTORY = Path(__file__).resolve().parents[1] / "tests/languages/python"
SUITE = runpy.run_path(str(DIRECTORY / "source-module-entry/check_seeded_run.py"))
INTAKE = runpy.run_path(str(DIRECTORY / "source-scope/check_intake.py"))
PIN = "tests/python/programs/original/k-python/programs/testtuples3.py"
SHA = "6ebe39b5877a6dcf2bf137915fefa9ed1ed2bb71873552fe37af2bef5b1d77b5"
CONSTRUCTORS_PIN = "tests/python/programs/original/lambda-py/python-reference/tuple/tuple-constructors.py"
CONSTRUCTORS_SHA = "f4c4456ed6ffc8dc95d34f46a18636a57196236e1ff7bafc5cc4b851532adf18"
IMMUTABLE_ALIAS_PIN = "tests/python/programs/original/lambda-py/python-reference/scope/immutable-alias.py"
IMMUTABLE_ALIAS_SHA = "e5c11007f121cac93bfb3cbb9aa9ec74b48ac1e617400434a42b4668b7b9f7ef"

TUPLE_TRUTH_PIN = "tests/python/programs/original/lambda-py/python-reference/tuple/tuple-truth.py"
TUPLE_TRUTH_SHA = "b2cadc65b6d30d9998a4b5ae435d2452705ae82bd74dd3d98dbfb5275f0e8e44"

LIVE_COMPARISON_PIN = "tests/python/programs/original/k-python/programs/testtuples11.py"
LIVE_COMPARISON_SHA = "b1e88db0dfe2d8470404900de6cac22eb9067b7042ad2a1af0b941a9e3cd7aab"

LEAN = SUITE["LEAN"] + """
open Compile.ModuleEntry.Functions
open Compile.ModuleEntry.Functions.Run.Seeded (legacyListSeed legacyTupleSeed legacyTupleIdentitySeed)

private def tupleOutcome (source : Source.Module) (space : Namespace) (status : String)
    (bindings : Bindings) (calls : List (String × Core.Module.SeededCall.Result))
    (allocated : List Value := []) (appendedLists : List (List Core.Module.Value) := []) : Bool := Id.run do
  let .ok compiled := Compile.ModuleEntry.Functions.Run.compile source | return false
  let heap : Core.Closure.Heap := ⟨1, fun address => if address == 0 then some (.int 23) else none⟩
  let lists : Core.Module.ListHeap := ⟨#[[.int 31]]⟩
  let result := Compile.ModuleEntry.Functions.Run.Seeded.run space compiled heap (lists := lists)
  let completion := match result.completion with
    | .ok () => "normal"
    | .error (.raised (.runtime .tupleArgumentNotIterable)) => "TypeError"
    | .error (.raised error) => raised error
    | .error .unsupported => "unsupported"
    | .error _ => "unexpected completion"
  return completion == status && result.residual.moduleGlobals == bindings &&
    result.residual.builtins == space.builtins && result.lists.objects == lists.objects ++ appendedLists.toArray &&
    result.heap.next == allocated.length + 1 &&
    (allocated.zipIdx 1).all (fun (value, address) =>
      (result.heap.contents address).map Compile.ModuleEntry.Functions.Run.Seeded.seededValue == some value) &&
    result.calls.map (fun event => (event.callee, event.observation.result)) == calls &&
    result.calls.all (·.observation.caught.isNone) &&
    (result.heap.contents 0).map Compile.ModuleEntry.Functions.Run.Seeded.seededValue == some (.int 23)

private def tupleTrace (source : Source.Module) (space : Namespace) : Option
    (Except Core.Module.TupleDispatch.Failure Bool × List (Except Core.Module.TupleDispatch.Failure
      TupleChain.Compared) × Array (List Core.Module.TupleDispatch.Element)) := do
  let compiled ← (Compile.ModuleEntry.Functions.Run.compile source).toOption
  let test ← compiled.instructions.findSome? fun
    | .assertTupleChain test => some test
    | _ => none
  let trace := TupleChain.evaluate (Compile.ModuleEntry.Functions.Run.Seeded.tupleLookup space) test
  return (trace.result, trace.reached, trace.heap.objects)

private def ordinaryTuple (source : Source.Module) : Option (String × String × String) := do
  let compiled ← (Compile.ModuleEntry.Functions.Run.compile source).toOption
  match (Compile.ModuleEntry.Functions.Run.runPrefix compiled.table 1000 compiled.start).2 with
  | .finished session completion =>
    let status := match completion with
      | .normal => "normal"
      | .assertionError => "AssertionError:empty"
      | .raised error => raised (.runtime error)
      | .scalarProfile => "unsupported"
      | _ => "unexpected completion"
    let binding name := resultBinding ((session.globals name).map Compile.ModuleEntry.Functions.Run.Seeded.seededValue)
    some (status, binding "keep", binding "tail")
  | _ => none

private def ordinaryBindings (source : Source.Module)
    (completion : Compile.ModuleEntry.Functions.Run.Completion)
    (bindings : List (String × Option Value)) : Bool := Id.run do
  let .ok compiled := Compile.ModuleEntry.Functions.Run.compile source | return false
  let heap : Core.Closure.Heap := ⟨1, fun address => if address == 0 then some (.int 23) else none⟩
  let lists : Core.Module.ListHeap := ⟨#[[.int 31]]⟩
  let session := { Compile.ModuleEntry.Functions.Run.seed .empty heap with lists := lists }
  let .finished residual observed := (Compile.ModuleEntry.Functions.Run.runPrefix compiled.table 1000
    (.ready session compiled.instructions)).2 | return false
  return observed == completion &&
    bindings.all (fun (name, value) =>
      (residual.globals name).map Compile.ModuleEntry.Functions.Run.Seeded.seededValue == value) &&
    residual.lists == lists && residual.heap.next == 1 &&
    (residual.heap.contents 0).map Compile.ModuleEntry.Functions.Run.Seeded.seededValue == some (.int 23)

private def tupleTruthArguments (source : Source.Module) (space : Namespace) : Option (List Value) := do
  let compiled ← (Compile.ModuleEntry.Functions.Run.compile source).toOption
  let [.call .discard "___assertTrue" [first], .nestedCall .discard "___assertTrue" [.scalar second]] :=
    compiled.instructions | none
  [first, second].mapM fun operand =>
    ((Compile.ModuleEntry.Functions.Run.Seeded.lowerCallOperand operand).eval space #v[]).toOption

private def ordinaryTupleLists (source : Source.Module) :
    Option (Compile.ModuleEntry.Functions.Run.Completion × Array (List Core.Module.Value) × Option Value) := do
  let compiled ← (Compile.ModuleEntry.Functions.Run.compile source).toOption
  let session := { Compile.ModuleEntry.Functions.Run.seed .empty with lists := ⟨#[[.int 31]]⟩ }
  match (Compile.ModuleEntry.Functions.Run.runPrefix compiled.table 1000 (.ready session compiled.instructions)).2 with
  | .finished residual completion =>
    some (completion, residual.lists.objects,
      (residual.globals "keep").map Compile.ModuleEntry.Functions.Run.Seeded.seededValue)
  | _ => none
"""

STOCK = "(legacyTupleSeed .builtin)"
MASKED = f'({STOCK}.bindGlobal "tuple" .none)'


def assert_equal(left, right):
    assert left == right, (left, right)


def assert_true(value):
    assert value, value


def execute(source, builtins, initial=None, expected=None, *, identity_warning=False):
    namespace = dict(initial or {}, __builtins__=builtins)
    result = "normal"
    with redirect_stdout(StringIO()) as stdout, redirect_stderr(StringIO()) as stderr:
        try:
            with warnings.catch_warnings(record=True) as caught:
                warnings.simplefilter("always", SyntaxWarning)
                code = compile(source, "<tuple fixture>", "exec", dont_inherit=True, optimize=0)
            expected_diagnostics = []
            if identity_warning:
                message = """"is" with 'tuple' literal. Did you mean "=="?"""
                expected_diagnostics.append((SyntaxWarning, message))
            assert [(entry.category, str(entry.message)) for entry in caught] == expected_diagnostics
            exec(code, namespace)
        except AttributeError as error:
            result = "AttributeError:" + error.name
        except (NameError, TypeError, AssertionError) as error:
            result = SUITE["exception_observation"](error)
    assert not stdout.getvalue() and not stderr.getvalue()
    assert namespace.pop("__builtins__") is builtins
    assert namespace == expected, namespace
    return result


def check(source, source_path, lean_path, *guards):
    INTAKE["emit"](source_path, lean_path, source)
    INTAKE["check_lean"](lean_path, LEAN + "\n".join(guards), extra_imports=SUITE["IMPORTS"])


def outcome(space, result, bindings, calls="[]", source="pythonSource", allocated="[]", appended_lists="[]"):
    return f"#guard tupleOutcome {source} {space} {json.dumps(result)} {bindings} {calls} {allocated} {appended_lists}"


def replay_pin(checkout, source_path, lean_path):
    revision = subprocess.check_output(["git", "-C", str(checkout), "rev-parse", "HEAD"], text=True).strip()
    assert revision == SUITE["UPSTREAM_REVISION"], revision
    source = SUITE["pinned_source"](checkout, PIN, SHA)
    statement, = ast.parse(source).body
    test = statement.test
    assert type(statement) is ast.Assert and all(type(op) is ast.Eq for op in test.ops)
    operands = [test.left, *test.comparators]
    values = [eval(compile(ast.Expression(expr), PIN, "eval", optimize=0), {"tuple": tuple}) for expr in operands]
    assert values == [(5, 6)] * 4 and all(type(value) is tuple for value in values)
    assert execute(source, {"tuple": tuple}, expected={}) == "normal"
    assert execute(source, {}, expected={}) == "NameError:tuple"
    guards = ['#guard ordinaryTuple pythonSource == some ("NameError:tuple", "absent", "absent")']
    absent = ["empty", "legacy_builtin", "legacy_preamble", *SUITE["OPT_IN_PROFILES"]]
    for profile in absent:
        assert SUITE["cpython"](source, profile, expected_globals={}) == ["NameError:tuple", "absent", "absent"]
        space = f"(initial {json.dumps(profile)})"
        guards.append(outcome(space, "NameError:tuple", f"{space}.moduleGlobals"))
    for placement in ("builtin", "preamble"):
        space = f"(legacyListSeed .{placement})"
        assert execute(source, {"list": list}, expected={}) == "NameError:tuple"
        guards.append(outcome(space, "NameError:tuple", f"{space}.moduleGlobals"))
    for placement in ("builtin", "preamble"):
        space = f"(legacyTupleSeed .{placement})"
        guards.append(outcome(space, "normal", f"{space}.moduleGlobals"))
    objects = ", ".join(f".ok (.object ⟨some {address}, [.int 5, .int 6]⟩)" for address in (2, 5, 8, 9))
    guards.extend((
        f"#guard tupleTrace pythonSource {STOCK} == some (.ok true, [{objects}], "
        "#[[.int 5], [.int 6], [.int 5, .int 6], [.int 5], [.int 6], [.int 5, .int 6], "
        "[.int 5], [.int 6], [.int 5, .int 6], [.int 5, .int 6]])",
        "#guard tupleTrace pythonSource Namespace.empty == some (.error .missingType, "
        "[.ok (.object ⟨some 2, [.int 5, .int 6]⟩), .error .missingType], #[[.int 5], [.int 6], [.int 5, .int 6]])",
    ))
    check(source, source_path, lean_path, *guards)
    return {"upstream": revision, "sha256": SHA, "operand_values": values,
            "stock_seeded": "normal", "ordinary_and_prior_seeds": "NameError:tuple"}


def method_controls():
    left, right = tuple([True]), tuple([2])
    empty = ()
    for method in (lambda first, second: first.__add__(second), tuple.__add__, lambda first, second: first + second):
        assert method(left, empty) is left and method(empty, right) is right
        assert method(empty, empty) is empty
        joined = method(left, right)
        assert joined == (True, 2) and joined is not left and joined is not right
        assert type(joined[0]) is bool
    assert left.__eq__([True]) is NotImplemented and tuple.__eq__(left, [True]) is NotImplemented
    assert (left == [True]) is False
    scope = {"left": left}
    assert execute("left.__add__([True])", {}, scope, scope) == "TypeError"

    events = []
    def prepare(name, value):
        events.append(name)
        return value

    assert execute("tuple.__add__(prepare('receiver', (1,)), prepare('argument', (2,)))",
                   {}, {"tuple": None, "prepare": prepare}, {"tuple": None, "prepare": prepare}) == "AttributeError:__add__"
    assert events == []
    scope = {"tuple": tuple, "prepare": prepare}
    assert execute("tuple.__add__(prepare('receiver', []), prepare('argument', (2,)))",
                   {}, scope, scope) == "TypeError"
    assert events == ["receiver", "argument"]
    events.clear()
    scope = {"prepare": prepare}
    assert execute("assert prepare('left', (1,)) == prepare('middle', (1,)) == prepare('right', (2,))"
                   " == prepare('skipped', (2,))", {}, scope, scope) == "AssertionError:empty"
    assert events == ["left", "middle", "right"]
    return {"empty_aliases": True, "cross_kind_method": "NotImplemented",
            "cross_kind_operator": False, "chain_order": events}


def chain_controls(source_path, lean_path):
    outcomes = {}
    cases = (
        ("early_false", "assert (1,).__add__(()) == (2,) == tuple.__add__((2,), ())",
         "Namespace.empty", {}, {}, "AssertionError:empty", "AssertionError:empty",
         "#guard tupleTrace pythonSource Namespace.empty == some "
         "(.ok false, [.ok (.object ⟨some 0, [.int 1]⟩), .ok (.object ⟨some 1, [.int 2]⟩)], #[[.int 1], [.int 2]])"),
        ("late_false", "assert (1,).__add__(()) == ().__add__((1,)) == (2,) == tuple.__add__((2,), ())",
         "Namespace.empty", {}, {}, "AssertionError:empty", "AssertionError:empty",
         "#guard tupleTrace pythonSource Namespace.empty == some "
         "(.ok false, [.ok (.object ⟨some 0, [.int 1]⟩), .ok (.object ⟨some 1, [.int 1]⟩), .ok (.object ⟨some 2, [.int 2]⟩)], "
         "#[[.int 1], [.int 1], [.int 2]])"),
        ("bound_without_seed", "assert (True,).__add__(()) == (1,)", "Namespace.empty", {}, {},
         "normal", "normal", ""),
        ("operator_empty", "assert (1,).__add__(()) == () + (1,) == (1,) + ()", "Namespace.empty", {}, {},
         "normal", "normal", "#guard tupleTrace pythonSource Namespace.empty == some "
         "(.ok true, [.ok (.object ⟨some 0, [.int 1]⟩), .ok (.object ⟨some 1, [.int 1]⟩), .ok (.object ⟨some 2, [.int 1]⟩)], "
         "#[[.int 1], [.int 1], [.int 1]])"),
        ("masked_type", "assert (1,) == tuple.__add__((1,), ())", MASKED, {"tuple": tuple}, {"tuple": None},
         "AttributeError:__add__", "unsupported",
         f"#guard tupleTrace pythonSource {MASKED} == some (.error (.missingAttribute .add), "
         "[.ok (.object ⟨some 0, [.int 1]⟩), .error (.missingAttribute .add)], #[[.int 1]])"),
        ("different_descriptor", "assert (1,) == tuple.__add__((1,), ())",
         f'({STOCK}.bindGlobal "tuple" (.int 0))', {"tuple": tuple}, {"tuple": 0}, "TypeError", "unsupported", ""),
    )
    for name, assertion, space, builtins, initial, python_status, lean_status, trace in cases:
        source = "keep = 7\n" + assertion + "\ntail = 9\n"
        bindings = {"keep": 7, **initial}
        lean_bindings = ['("keep", .int 7)']
        if python_status == "normal":
            bindings["tail"] = 9
            lean_bindings.insert(0, '("tail", .int 9)')
        if initial:
            tag = ".none" if initial["tuple"] is None else ".int 0"
            lean_bindings.append(f'("tuple", {tag})')
        assert execute(source, builtins, initial, bindings) == python_status, name
        guards = [outcome(space, lean_status, "[" + ", ".join(lean_bindings) + "]"), trace]
        if space == "Namespace.empty":
            tail = "int:9" if lean_status == "normal" else "absent"
            guards.append(f"#guard ordinaryTuple pythonSource == some ({json.dumps(lean_status)}, \"int:7\", \"{tail}\")")
        check(source, source_path, lean_path, *guards)
        outcomes[name] = {"cpython": python_status, "lean": lean_status}

    restore = "saved = tuple\ntuple = None\ntuple = saved\nassert tuple.__add__((True,), ()) == (1,)\n"
    assert execute(restore, {"tuple": tuple}, expected={"tuple": tuple, "saved": tuple}) == "normal"
    check(restore, source_path, lean_path,
          outcome(STOCK, "normal", '[("tuple", .builtin .tuple), ("saved", .builtin .tuple)]'))
    ordinary_mask = "keep = 7\ntuple = None\nassert tuple.__add__((1,), ()) == (1,)\ntail = 9\n"
    assert execute(ordinary_mask, {}, expected={"keep": 7, "tuple": None}) == "AttributeError:__add__"
    check(ordinary_mask, source_path, lean_path,
          '#guard ordinaryTuple pythonSource == some ("unsupported", "int:7", "absent")')
    for text in (
        "assert (1,).__add__(()) == (2,) == tuple.__add__((unknown,), ())\n",
        "assert (1,).__add__(()) == (2,) == tuple.__add__(x=(2,), y=())\n",
        "assert tuple.__add__([1], ()) == (1,)\n",
        "assert (1,).__eq__([1]) == ()\n",
    ):
        check(text, source_path, lean_path, """#guard (
  match Compile.ModuleEntry.Functions.Run.compile pythonSource with
  | .error (.source (.scalar .expressionProfile)) => true
  | _ => false)""")
    return outcomes


def constructor_controls(source_path, lean_path):
    first = tuple([True, None])
    equal = tuple([1, None])
    assert first == equal and first is not equal
    assert tuple(first) is first and tuple(equal) is equal
    empty = ()
    assert tuple() is empty and tuple(empty) is empty

    assertion = "assert tuple((True, 1, None)) == tuple((1, True, None)) == tuple((1, 1, None))\n"
    source = "keep = 7\n" + assertion + "tail = 9\n"
    assert execute(source, {"tuple": tuple}, expected={"keep": 7, "tail": 9}) == "normal"
    assert execute(source, {}, expected={"keep": 7}) == "NameError:tuple"
    assert execute(source, {"tuple": tuple}, {"tuple": 0}, {"tuple": 0, "keep": 7}) == "TypeError"
    masked = f'({STOCK}.bindGlobal "tuple" (.int 0))'
    check(source, source_path, lean_path,
          outcome(STOCK, "normal", '[("tail", .int 9), ("keep", .int 7)]'),
          outcome("Namespace.empty", "NameError:tuple", '[("keep", .int 7)]'),
          outcome(masked, "TypeError", '[("keep", .int 7), ("tuple", .int 0)]'),
          '#guard ordinaryTuple pythonSource == some ("NameError:tuple", "int:7", "absent")',
          f"#guard tupleTrace pythonSource {STOCK} == some (.ok true, "
          "[.ok (.object ⟨some 0, [.bool true, .int 1, .none]⟩), .ok (.object ⟨some 1, [.int 1, .bool true, .none]⟩), "
          ".ok (.object ⟨some 2, [.int 1, .int 1, .none]⟩)], "
          "#[[.bool true, .int 1, .none], [.int 1, .bool true, .none], [.int 1, .int 1, .none]])",
          "#guard tupleTrace pythonSource Namespace.empty == "
          "some (.error .missingType, [.error .missingType], #[])",
          f"#guard tupleTrace pythonSource {masked} == "
          "some (.error .notCallable, [.error .notCallable], #[[.bool true, .int 1, .none]])")

    empty_assertion = "assert tuple() == () == tuple(())\n"
    restore = "saved = tuple\ntuple = None\ntuple = saved\n" + empty_assertion
    bindings = '[("tuple", .builtin .tuple), ("saved", .builtin .tuple)]'
    assert execute(restore, {"tuple": tuple}, expected={"tuple": tuple, "saved": tuple}) == "normal"
    check(restore, source_path, lean_path, outcome(STOCK, "normal", bindings),
          f"#guard tupleTrace pythonSource {STOCK} == "
          "some (.ok true, [.ok (.object ⟨none, []⟩), .ok (.object ⟨none, []⟩), .ok (.object ⟨none, []⟩)], #[])")
    masked = "keep = 7\ntuple = None\n" + assertion + "tail = 9\n"
    assert execute(masked, {"tuple": tuple}, expected={"keep": 7, "tuple": None}) == "TypeError"
    check(masked, source_path, lean_path,
          outcome(STOCK, "TypeError", '[("tuple", .none), ("keep", .int 7)]'),
          '#guard ordinaryTuple pythonSource == some ("TypeError", "int:7", "absent")')

    skipped = "assert (0,).__add__(()) == (1,) == tuple((2,))\n"
    assert execute(skipped, {}, expected={}) == "AssertionError:empty"
    check(skipped, source_path, lean_path, outcome("Namespace.empty", "AssertionError:empty", "[]"),
          "#guard tupleTrace pythonSource Namespace.empty == some (.ok false, "
          "[.ok (.object ⟨some 0, [.int 0]⟩), .ok (.object ⟨some 1, [.int 1]⟩)], #[[.int 0], [.int 1]])")
    return {"exact_alias": True, "empty_singleton": True, "live_lookup": True}


def replay_constructors(checkout, source_path, lean_path):
    source = SUITE["pinned_source"](checkout, CONSTRUCTORS_PIN, CONSTRUCTORS_SHA)
    first_statement = ast.Module(body=ast.parse(source).body[:1], type_ignores=[])
    empty_tuple = ()

    def equal_empty(left, right):
        assert left is empty_tuple and right is empty_tuple

    both = {"tuple": tuple, "___assertEqual": equal_empty}
    assert execute(first_statement, both, expected={}) == "normal"
    assert execute(first_statement, {"___assertEqual": equal_empty}, expected={}) == "NameError:tuple"
    assert execute(first_statement, {}, expected={}) == "NameError:___assertEqual"
    assert execute(first_statement, both, {"tuple": 7}, {"tuple": 7}) == "TypeError"
    assert execute(source, {"tuple": tuple, "___assertEqual": assert_equal, "___assertTrue": assert_true},
                   expected={"t0_3": (0, 1, 2, 3), "t0_3_bis": (0, 1, 2, 3)}) == "normal"

    first = "firstConstructorStatement"
    guards = ["""
private def firstConstructorStatement : Source.Module := ⟨pythonSource.body.take 1⟩
#guard (match Compile.ModuleEntry.Functions.Run.compile firstConstructorStatement with
  | .ok compiled => match compiled.instructions with
    | [.nestedCall .discard "___assertEqual" [.call "tuple" [], .scalar (.tuple [])]] => true
    | _ => false
  | _ => false)
#guard (Compile.ModuleEntry.Functions.Run.compile pythonSource).isOk
#guard ordinaryTuple pythonSource == some ("NameError:___assertEqual", "absent", "absent")
#guard ordinaryTuple firstConstructorStatement == some ("NameError:___assertEqual", "absent", "absent")
#guard Core.Module.SeededCall.invoke (.builtin .tuple) [.int 1] == .error .unsupported
""", outcome("Namespace.empty", "NameError:___assertEqual", "[]", source=first)]
    for placement in ("builtin", "preamble"):
        base = f'(initial "legacy_{placement}")'
        stock = f"(legacyTupleSeed .{placement})"
        missing_tuple = '[("tuple", .error (.raised (.runtime (.nameError "tuple"))))]'
        guards.extend((
            outcome(base, "NameError:tuple", f"{base}.moduleGlobals", missing_tuple, first),
            outcome(base, "NameError:tuple", f"{base}.moduleGlobals", missing_tuple),
            outcome(stock, "normal", f"{stock}.moduleGlobals",
                    '[("tuple", .ok (.returnedTuple [])), ("___assertEqual", .ok .none)]', first),
        ))
    mask = f'({STOCK}.bindGlobal "tuple" (.int 7))'
    guards.append(outcome(mask, "TypeError", f"{mask}.moduleGlobals",
                          '[("tuple", .error (.raised (.runtime .notCallable)))]', first))
    guards.append(outcome("Namespace.empty", "NameError:___assertEqual", "[]"))
    assert execute(source, {}, expected={}) == "NameError:___assertEqual"
    assert execute(source, {"___assertEqual": assert_equal}, expected={}) == "NameError:tuple"
    assert execute(source, {}, {"___assertEqual": assert_equal},
                   {"___assertEqual": assert_equal}) == "NameError:tuple"
    check(source, source_path, lean_path, *guards)

    # Replay the raw prefix through the original fourth statement.
    prefix_end = ast.parse(source).body[3].end_lineno
    prefix = "".join(source.splitlines(keepends=True)[:prefix_end])
    seen = []

    def observe_identity(value):
        seen.append(value)
        assert_true(value)

    bound = {"t0_3": (0, 1, 2, 3), "t0_3_bis": (0, 1, 2, 3)}
    helper = {"___assertTrue": observe_identity}
    assert execute(prefix, {**both, **helper}, expected=bound) == "normal"
    preamble = {"___assertEqual": equal_empty, **helper}
    assert execute(prefix, {"tuple": tuple}, preamble, {**preamble, **bound}) == "normal"
    assert len(seen) == 2 and all(value is True for value in seen)
    assert execute(prefix, both, expected=bound) == "NameError:___assertTrue"
    masked_helper = {"___assertTrue": None}
    assert execute(prefix, {**both, **helper}, masked_helper, {**masked_helper, **bound}) == "TypeError"
    guards = ["""
private def identityPrefix : Source.Module := ⟨pythonSource.body.take 4⟩
#guard (match Compile.ModuleEntry.Functions.Run.compile identityPrefix with
  | .ok compiled => match compiled.instructions with
    | [_, _, _, .callTupleIdentity .discard "___assertTrue" ⟨.global "t0_3", .is_, .global "t0_3_bis"⟩] => true
    | _ => false
  | _ => false)
#guard (Compile.ModuleEntry.Functions.Run.compile ⟨pythonSource.body.take 5⟩).isOk == true
#guard (Compile.ModuleEntry.Functions.Run.compile ⟨pythonSource.body.take 6⟩).isOk == true
#guard (Compile.ModuleEntry.Functions.Run.compile ⟨pythonSource.body.take 7⟩).isOk == true
#guard ordinaryTuple identityPrefix == some ("NameError:___assertEqual", "absent", "absent")
"""]
    items = "[.int 0, .int 1, .int 2, .int 3]"
    origin = f".tupleObject ⟨some 1, {items}⟩"
    bindings = f'[("t0_3_bis", {origin}), ("t0_3", {origin})]'
    calls = ('[("tuple", .ok (.returnedTuple [])), ("___assertEqual", .ok .none), '
             f'("tuple", .ok ({origin}))]')
    identity_call = '[("___assertTrue", .ok .none)]'
    for placement in ("builtin", "preamble"):
        unseeded_helper = f"(legacyTupleSeed .{placement})"
        stock_helper = f"(legacyTupleIdentitySeed .{placement})"
        guards.extend((
            outcome(unseeded_helper, "NameError:___assertTrue",
                    f"({bindings} ++ {unseeded_helper}.moduleGlobals)", calls, "identityPrefix", f"[{origin}]"),
            outcome(stock_helper, "normal", f"({bindings} ++ {stock_helper}.moduleGlobals)",
                    f"({calls} ++ {identity_call})", "identityPrefix", f"[{origin}]"),
        ))
    masked = '((legacyTupleIdentitySeed .builtin).bindGlobal "___assertTrue" .none)'
    failed_call = '[("___assertTrue", .error (.raised (.runtime .notCallable)))]'
    guards.append(outcome(masked, "TypeError", f"({bindings} ++ {masked}.moduleGlobals)",
                          f"({calls} ++ {failed_call})", "identityPrefix", f"[{origin}]"))
    # The fifth statement reaches a newly allocated empty list.
    empty_list_end = ast.parse(source).body[4].end_lineno
    empty_list_prefix = "".join(source.splitlines(keepends=True)[:empty_list_end])
    assert execute(empty_list_prefix, {**both, **helper}, expected=bound) == "normal"
    assert execute(empty_list_prefix, {"tuple": tuple}, preamble, {**preamble, **bound}) == "normal"
    assert len(seen) == 4 and all(value is True for value in seen)
    guards.append("""
private def emptyListPrefix : Source.Module := ⟨pythonSource.body.take 5⟩
#guard (match (Compile.ModuleEntry.Functions.Run.compile emptyListPrefix).toOption with
  | some compiled => match compiled.instructions.getLast? with
    | some (.callTupleFromListDisplay .discard [] (some ("___assertEqual", [.scalar (.tuple [])]))) => true
    | _ => false
  | none => false)
#guard ordinaryTupleLists emptyListPrefix == some (.raised (.nameError "___assertEqual"), #[[.int 31]], none)
""")
    list_calls = '[("tuple", .ok (.returnedTuple [])), ("___assertEqual", .ok .none)]'
    for placement in ("builtin", "preamble"):
        stock_helper = f"(legacyTupleIdentitySeed .{placement})"
        guards.append(outcome(stock_helper, "normal", f"({bindings} ++ {stock_helper}.moduleGlobals)",
                              f"({calls} ++ {identity_call} ++ {list_calls})", "emptyListPrefix",
                              f"[{origin}]", "[[]]"))
    # Replay through the nonempty list, empty text, and nonempty text calls.
    statements = ast.parse(source).body
    lines = source.splitlines(keepends=True)
    flat_helpers = {"___assertEqual": assert_equal, **helper}
    for index in (5, 6, 7):
        text = "".join(lines[:statements[index].end_lineno])
        assert execute(text, {"tuple": tuple, **flat_helpers}, expected=bound) == "normal"
        assert execute(text, {"tuple": tuple}, flat_helpers, {**flat_helpers, **bound}) == "normal"
    assert len(seen) == 10 and all(value is True for value in seen)
    guards.append("""
private def flatListPrefix : Source.Module := ⟨pythonSource.body.take 6⟩
private def textTuplePrefix : Source.Module := ⟨pythonSource.body.take 7⟩
#guard (match (Compile.ModuleEntry.Functions.Run.compile flatListPrefix).toOption with
  | some compiled => match compiled.instructions.getLast? with
    | some (.callTupleFromListDisplay .discard [.int 0, .int 1, .int 2, .int 3]
        (some ("___assertEqual", [.scalar (.tuple _)]))) => true
    | _ => false
  | none => false)
""")
    fresh = f".tupleObject ⟨some 2, {items}⟩"
    flat_calls = f'[("tuple", .ok ({fresh})), ("___assertEqual", .ok .none)]'
    text_items = "[.text ⟨[115], by decide⟩, .text ⟨[112], by decide⟩, " \
                 ".text ⟨[97], by decide⟩, .text ⟨[109], by decide⟩]"
    text_object = f".tupleObject ⟨some 3, {text_items}⟩"
    text_calls = f'[("tuple", .ok ({text_object})), ("___assertEqual", .ok .none)]'
    for placement in ("builtin", "preamble"):
        stock_helper = f"(legacyTupleIdentitySeed .{placement})"
        events = f"{calls} ++ {identity_call} ++ {list_calls} ++ {flat_calls}"
        for name, receipts, heap in (
            ("flatListPrefix", events, f"[{origin}, .returnedTuple {items}]"),
            ("textTuplePrefix", f"{events} ++ {list_calls}", f"[{origin}, .returnedTuple {items}]"),
            ("pythonSource", f"{events} ++ {list_calls} ++ {text_calls}",
             f"[{origin}, .returnedTuple {items}, .returnedTuple {text_items}]"),
        ):
            guards.append(outcome(stock_helper, "normal", f"({bindings} ++ {stock_helper}.moduleGlobals)",
                                  f"({receipts})", name, heap, f"[[], {items}]"))
    check(source, source_path, lean_path, *guards)

    alias = "saved = tuple\ntuple = 7\nanswer = saved()\nbad = tuple()\n"
    assert execute(alias, {"tuple": tuple},
                   expected={"saved": tuple, "tuple": 7, "answer": empty_tuple}) == "TypeError"
    check(alias, source_path, lean_path, outcome(
        STOCK, "TypeError", '[("answer", .returnedTuple []), ("tuple", .int 7), ("saved", .builtin .tuple)]',
        '[("saved", .ok (.returnedTuple [])), ("tuple", .error (.raised (.runtime .notCallable)))]'))
    return {"sha256": CONSTRUCTORS_SHA, "inner": "canonical empty tuple",
            "stock_seeded_prefix": "normal", "identity_prefix": "normal with saved origin",
            "empty_list_prefix": "normal", "flat_list_prefix": "normal", "empty_text_prefix": "normal",
            "whole_source": "normal with stock tuple and helpers in both placements"}


def replay_immutable_alias(checkout, source_path, lean_path):
    source = SUITE["pinned_source"](checkout, IMMUTABLE_ALIAS_PIN, IMMUTABLE_ALIAS_SHA)
    statements = ast.parse(source).body
    assert len(statements) == 22 and statements[15].lineno == 21
    lines = source.splitlines(keepends=True)
    expected = {"x": 2, "y": 3, "t": (1, 2, 3), "t1": (1, 2, 3, 4)}
    stopped = {"x": 2, "y": 1}
    assert execute(source, {}, expected=stopped) == "NameError:___assertEqual"

    guards = ["""
private def beforeTextBinding : Source.Module := ⟨pythonSource.body.take 15⟩
private def savedTextAlias : Source.Module := ⟨pythonSource.body.take 18⟩
#guard (Compile.ModuleEntry.Functions.Run.compile pythonSource).isOk

#guard ordinaryBindings pythonSource (.raised (.nameError "___assertEqual"))
  [("x", some (.int 2)), ("y", some (.int 1)), ("t", none), ("t1", none), ("s", none), ("s1", none)]
"""]
    guards.append(outcome("Namespace.empty", "NameError:___assertEqual", '[("x", .int 2), ("y", .int 1)]',
                          '[("___assertEqual", .error (.raised (.runtime (.nameError "___assertEqual"))))]'))
    bindings = ('[("t1", .returnedTuple [.int 1, .int 2, .int 3, .int 4]), '
                '("t", .returnedTuple [.int 1, .int 2, .int 3]), ("y", .int 3), ("x", .int 2)]')
    saved = '[("s", .text ⟨[50], by decide⟩), ("s1", .text ⟨[49], by decide⟩)]'
    finished = '[("s1", .text ⟨[51], by decide⟩), ("s", .text ⟨[50], by decide⟩)]'
    for placement in ("builtin", "preamble"):
        calls = []

        def observe(left, right):
            assert_equal(left, right)
            calls.append((left, right))

        helper = {"___assertEqual": observe}
        builtins, initial = (helper, {}) if placement == "builtin" else ({}, helper)
        space = f'(initial "legacy_{placement}")'
        for name, limit, namespace, extra, count in (
            ("beforeTextBinding", 15, expected, "[]", 7),
            ("savedTextAlias", 18, expected | {"s": "2", "s1": "1"}, saved, 7),
            ("pythonSource", 22, expected | {"s": "2", "s1": "3"}, finished, 10),
        ):
            calls.clear()
            prefix = "".join(lines[:statements[limit - 1].end_lineno])
            assert execute(prefix, builtins, initial, namespace | initial) == "normal"
            assert len(calls) == count
            if limit == 22:
                assert prefix == source
                assert calls[-3:] == [("1", "1"), ("3", "3"), ("2", "2")]
            guards.append(outcome(space, "normal", f"({extra} ++ {bindings} ++ {space}.moduleGlobals)",
                                  f'(List.replicate {count} ("___assertEqual", .ok .none))', name))
    check(source, source_path, lean_path, *guards)
    return {"sha256": IMMUTABLE_ALIAS_SHA, "ordinary_and_empty": "NameError:___assertEqual",
            "whole_source": "normal in both legacy helper placements", "receipts": 10}


def module_text_binding_controls(source_path, lean_path):
    seed = "(legacyTupleIdentitySeed .builtin)"
    value = "é😀\u0301\ud800"
    lexical_text = f".text ⟨{list(map(ord, value))}, by decide⟩"
    replacement = ".text ⟨[122], by decide⟩"
    source = f"original = {ascii(value)}\nsaved = original\noriginal = 'z'\n"
    prefix = source + f"___assertEqual(saved, {ascii(value)})\n"
    python_seed = {"___assertEqual": assert_equal, "___assertTrue": assert_true}
    expected = {"original": "z", "saved": value}
    residual = f'[("original", {replacement}), ("saved", {lexical_text})]'
    equal = '[("___assertEqual", .ok .none)]'
    failure = prefix + "saved = missing\nunreached = 'tail'\n"
    assert execute(failure, python_seed, expected=expected) == "NameError:missing"
    check(failure, source_path, lean_path, outcome(seed, "NameError:missing", residual, equal))

    read_failure = source + "saved = missing\nunreached = 'tail'\n"
    assert execute(read_failure, {}, expected=expected) == "NameError:missing"
    check(read_failure, source_path, lean_path,
          f'#guard ordinaryBindings pythonSource (.raised (.nameError "missing")) '
          f'[("original", some ({replacement})), ("saved", some ({lexical_text})), '
          '("missing", none), ("unreached", none)]',
          outcome("Namespace.empty", "NameError:missing", residual))

    mismatch = source + "___assertEqual(saved, original)\n"
    assert execute(mismatch, python_seed, expected=expected).startswith("AssertionError:")
    raised_text = (f".assertionError (.textPair ⟨{list(map(ord, value))}, by decide⟩ "
                   "⟨[122], by decide⟩)")
    check(mismatch, source_path, lean_path,
          f'#guard tupleOutcome pythonSource {seed} (raised ({raised_text})) {residual} '
          f'[("___assertEqual", .error (.raised ({raised_text})))]')

    same_alias = prefix + "alias = saved\n___assertTrue(alias is saved)\n"
    assert execute(same_alias, python_seed, expected=expected | {"alias": value}) == "normal"
    check(same_alias, source_path, lean_path,
          outcome(seed, "unsupported", f'(("alias", {lexical_text}) :: {residual})', equal))

    same_contents = prefix + f'other = {ascii(value)}\n___assertTrue(other is saved)\n'
    seen = []
    python_observer = python_seed | {"___assertTrue": seen.append}
    assert execute(same_contents, python_observer, expected=expected | {"other": value}) == "normal"
    assert len(seen) == 1 and type(seen[0]) is bool
    check(same_contents, source_path, lean_path,
          outcome(seed, "unsupported", f'(("other", {lexical_text}) :: {residual})', equal))
    return {"exact_code_points": list(map(ord, value)), "rebind_preserves_alias_contents": True,
            "failed_read_preserves_binding": True, "text_identity_outside_profile": True}


def tuple_helper_controls(source_path, lean_path):
    builtins = {"tuple": tuple, "___assertEqual": assert_equal}
    source = ("saved = ___assertEqual\n___assertEqual = 0\n"
              "saved((True, False, None, -2), (1, 0, None, -2))\n"
              "___assertEqual(tuple(), ())\nunreached = 9\n")
    assert execute(source, builtins, expected={"saved": assert_equal, "___assertEqual": 0}) == "TypeError"
    check(source, source_path, lean_path, outcome(
        STOCK, "TypeError", '[("___assertEqual", .int 0), ("saved", .helper .assertEqual)]',
        '[("saved", .ok .none), ("tuple", .ok (.returnedTuple [])), '
        '("___assertEqual", .error (.raised (.runtime .notCallable)))]'))

    for source, missing, receipts in (
        ("___assertEqual(missing_left, tuple())\n", "missing_left", "[]"),
        ("___assertEqual(tuple(), missing_right)\n", "missing_right", '[("tuple", .ok (.returnedTuple []))]'),
    ):
        assert execute(source, builtins, expected={}) == f"NameError:{missing}"
        check(source, source_path, lean_path, outcome(STOCK, f"NameError:{missing}", "[]", receipts))

    for left, right, left_lean, right_lean in (
        ((True, None), (1, 0), "[.bool true, .none]", "[.int 1, .int 0]"),
        ((), (False,), "[]", "[.bool false]"),
        ((1, 2), (2, 1), "[.int 1, .int 2]", "[.int 2, .int 1]"),
    ):
        source = f"___assertEqual({left!r}, {right!r})\nunreached = 9\n"
        namespace = {"__builtins__": builtins}
        try:
            exec(compile(source, "<tuple mismatch>", "exec", dont_inherit=True, optimize=0), namespace)
        except AssertionError as error:
            got_left, got_right = error.args[0]
            assert error.args == ((left, right),) and set(namespace) == {"__builtins__"}
            for actual, expected in ((got_left, left), (got_right, right)):
                assert [(type(item), item) for item in actual] == [(type(item), item) for item in expected]
        else:
            raise AssertionError("tuple mismatch completed")
        failure = f".assertionError (.tuplePair {left_lean} {right_lean})"
        check(source, source_path, lean_path,
              f'#guard tupleOutcome pythonSource {STOCK} (raised ({failure})) [] '
              f'[("___assertEqual", .error (.raised ({failure})))]')
    return {"numeric_scalar_equality": True, "failure_payloads": True, "callee_and_operand_order": True}


def replay_live_tuple_comparison(checkout, source_path, lean_path):
    source = SUITE["pinned_source"](checkout, LIVE_COMPARISON_PIN, LIVE_COMPARISON_SHA)
    bound = {"x": (5,)}
    assert execute(source, {}, expected=bound) == "NameError:tuple"
    assert execute(source, {"tuple": tuple}, expected=bound) == "normal"
    guards = [
        '#guard ordinaryTuple pythonSource == some ("NameError:tuple", "absent", "absent")',
        outcome("Namespace.empty", "NameError:tuple", '[("x", .returnedTuple [.int 5])]'),
    ]
    for placement in ("builtin", "preamble"):
        base = f'(initial "legacy_{placement}")'
        stock = f"(legacyTupleSeed .{placement})"
        binding = '[("x", .returnedTuple [.int 5])]'
        guards.append(outcome(base, "NameError:tuple", f"({binding} ++ {base}.moduleGlobals)"))
        guards.append(outcome(stock, "normal", f"({binding} ++ {stock}.moduleGlobals)"))
    live = f'({STOCK}.bindGlobal "x" (.returnedTuple [.int 5]))'
    guards.append(f"#guard tupleTrace pythonSource {live} == "
                  "some (.ok true, [.ok (.contents [.int 5]), .ok (.contents [.int 5])], #[])")
    check(source, source_path, lean_path, *guards)
    return {"sha256": LIVE_COMPARISON_SHA, "ordinary_and_no_tuple": "NameError:tuple",
            "stock_seeded": "normal"}


def live_comparison_controls(source_path, lean_path):
    x = (True, None, -7)
    left = f'({STOCK}.bindGlobal "x" (.returnedTuple [.bool true, .none, .int (-7)]))'
    for status, y, right in (
        ("normal", (1, None, -7), "[.int 1, .none, .int (-7)]"),
        ("AssertionError:empty", (1, None), "[.int 1, .none]"),
    ):
        init = {"x": x, "y": y}
        space = f'({left}.bindGlobal "y" (.returnedTuple {right}))'
        for source in ("assert x == tuple(y)", "assert tuple(x) == y"):
            assert execute(source, {"tuple": tuple}, init, init) == status
            check(source, source_path, lean_path, outcome(space, status, f"{space}.moduleGlobals"))

    cases = (
        ("assert missing_left == tuple(missing_argument)", "Namespace.empty", {}, {}, "NameError:missing_left"),
        ("assert left == tuple(missing_argument)", '(Namespace.empty.bindGlobal "left" (.int 0))',
         {}, {"left": 0}, "NameError:tuple"),
        ("assert left == tuple(missing_argument)", f'({MASKED}.bindGlobal "left" (.int 0))',
         {"tuple": tuple}, {"tuple": None, "left": 0}, "NameError:missing_argument"),
        ("assert left == tuple(left)", f'({MASKED}.bindGlobal "left" (.int 0))',
         {"tuple": tuple}, {"tuple": None, "left": 0}, "TypeError"),
        ("assert left == tuple(left)", f'({STOCK}.bindGlobal "left" (.int 0))',
         {"tuple": tuple}, {"left": 0}, "TypeError"),
        ("assert left == tuple(right)", f'(({STOCK}.bindGlobal "right" (.returnedTuple [])).bindGlobal "left" (.int 0))',
         {"tuple": tuple}, {"right": (), "left": 0}, "AssertionError:empty"),
    )
    for source, space, builtins, initial, status in cases:
        assert execute(source, builtins, initial, initial) == status
        check(source, source_path, lean_path, outcome(space, status, f"{space}.moduleGlobals"))

    rebinding = "stock = tuple\ntuple = 0\ntuple = stock\nx = (5,)\nassert x == tuple(x)\n"
    assert execute(rebinding, {"tuple": tuple}, expected={"stock": tuple, "tuple": tuple, "x": (5,)}) == "normal"
    check(rebinding, source_path, lean_path, outcome(
        STOCK, "normal", '[("x", .returnedTuple [.int 5]), ("tuple", .builtin .tuple), ("stock", .builtin .tuple)]'))
    return {"module_first_lookup": True, "ordered_failures": True, "contents_only": True}


def tuple_identity_controls(source_path, lean_path):
    seed = "(legacyTupleIdentitySeed .builtin)"
    python_seed = {"tuple": tuple, "___assertTrue": assert_true}
    value = (5, True, None)
    items = "[.int 5, .bool true, .none]"
    first = f".tupleObject ⟨some 1, {items}⟩"
    second = f".tupleObject ⟨some 2, {items}⟩"
    source = (
        "n = 5\nx = (n, True, None)\nsaved = tuple\ntuple = 0\nalias = saved(x)\n"
        "mirror = alias\nx = (n, True, None)\n___assertTrue(mirror is alias)\n"
        "___assertTrue(x is not alias)\n"
    )
    bindings = (f'[("x", {second}), ("mirror", {first}), ("alias", {first}), '
                '("tuple", .int 0), ("saved", .builtin .tuple), ("n", .int 5)]')
    expected = {"n": 5, "x": value, "alias": value, "mirror": value, "saved": tuple, "tuple": 0}
    calls = f'[("saved", .ok ({first})), ("___assertTrue", .ok .none), ("___assertTrue", .ok .none)]'
    assert execute(source, python_seed, expected=expected) == "normal"
    check(source, source_path, lean_path, outcome(seed, "normal", bindings, calls, allocated=f"[.returnedTuple {items}, .returnedTuple {items}]"))

    failure = source + "___assertTrue(x is alias)\ntail = 9\n"
    assert execute(failure, python_seed, expected=expected) == "AssertionError:bool:False"
    failure_call = '[("___assertTrue", .error (.raised (.assertionError (.boolean false))))]'
    check(failure, source_path, lean_path, outcome(seed, "AssertionError:bool:False", bindings,
          f"({calls} ++ {failure_call})", allocated=f"[.returnedTuple {items}, .returnedTuple {items}]"))

    empty = "x = ()\ny = tuple()\n___assertTrue(x is y)\n___assertTrue(y is ())\n"
    assert execute(empty, python_seed, expected={"x": (), "y": ()}, identity_warning=True) == "normal"
    check(empty, source_path, lean_path, outcome(seed, "normal",
          '[("y", .returnedTuple []), ("x", .returnedTuple [])]',
          '[("tuple", .ok (.returnedTuple [])), ("___assertTrue", .ok .none), ("___assertTrue", .ok .none)]'))

    order = (
        ("___assertTrue(left is right)", {}, "Namespace.empty", "NameError:___assertTrue", "[]"),
        ("___assertTrue(left is right)", {}, seed, "NameError:left", "[]"),
        ("___assertTrue(left is right)", {"___assertTrue": None, "left": 0},
         f'(({seed}.bindGlobal "left" (.int 0)).bindGlobal "___assertTrue" .none)', "NameError:right", "[]"),
        ("___assertTrue(() is ())", {"___assertTrue": None}, f'({seed}.bindGlobal "___assertTrue" .none)',
         "TypeError", '[("___assertTrue", .error (.raised (.runtime .notCallable)))]'),
    )
    for code, initial, space, status, receipts in order:
        supplied = {} if space == "Namespace.empty" else python_seed
        assert execute(code, supplied, initial, initial, identity_warning=code == "___assertTrue(() is ())") == status
        check(code, source_path, lean_path, outcome(space, status, f"{space}.moduleGlobals", receipts))

    dangling = f'({seed}.bindGlobal "dangling" ({first}))'
    check("___assertTrue(dangling is dangling)", source_path, lean_path,
          outcome(dangling, "unsupported", f"{dangling}.moduleGlobals"))

    seven = ".tupleObject ⟨some 1, [.int 7]⟩"
    closed = "x = (7,)\n___assertTrue(x is x)\n"
    assert execute(closed, python_seed, expected={"x": (7,)}) == "normal"
    check(closed, source_path, lean_path, outcome(seed, "normal",
          f'[("x", {seven})]', '[("___assertTrue", .ok .none)]', allocated=f"[{seven}]"))

    separate_literals = "x = (7,)\ny = (7,)\n___assertTrue(x is{} y)\n"
    equal_payload = ".tupleObject ⟨some 2, [.int 7]⟩"
    for negation, status in (("", "normal"), (" not", "AssertionError:bool:False")):
        code = separate_literals.format(negation)
        assert execute(code, python_seed, expected={"x": (7,), "y": (7,)}) == status
        check(code, source_path, lean_path, outcome(seed, "unsupported",
              f'[("y", {equal_payload}), ("x", {seven})]', allocated=f"[{seven}, {equal_payload}]"))
    check("x = (7,)\n___assertTrue(x is (7,))", source_path, lean_path,
          "#guard (Compile.ModuleEntry.Functions.Run.compile pythonSource).isOk == false")

    rebinding = (
        "x = (7,)\nsaved = tuple\ntuple = None\nfirst = saved(x)\nx = (8,)\n"
        "alias = first\nfinal = saved(alias)\n___assertTrue(final is first)\n"
    )
    values = {"x": (8,), "saved": tuple, "tuple": None, "first": (7,), "alias": (7,), "final": (7,)}
    assert execute(rebinding, python_seed, expected=values) == "normal"
    eight = ".tupleObject ⟨some 2, [.int 8]⟩"
    residual = (f'[("final", {seven}), ("alias", {seven}), ("x", {eight}), ("first", {seven}), '
                '("tuple", .none), ("saved", .builtin .tuple)]')
    constructor_receipts = f'[("saved", .ok ({seven})), ("saved", .ok ({seven}))]'
    truth_receipt = '[("___assertTrue", .ok .none)]'
    check(rebinding, source_path, lean_path, outcome(seed, "normal", residual,
          f"({constructor_receipts} ++ {truth_receipt})", allocated=f"[{seven}, {eight}]"))

    wrong_witness = f'({seed}.bindGlobal "wrong" (.tupleObject ⟨some 1, [.int 8]⟩))'
    bad_alias = "x = (7,)\n___assertTrue(x is wrong)\n"
    check(bad_alias, source_path, lean_path, outcome(wrong_witness, "unsupported",
          f'([("x", {seven})] ++ {wrong_witness}.moduleGlobals)', allocated=f"[{seven}]"))

    ordinary = "def receive(flag):\n    return flag\nn = 7\nx = (n,)\ny = x\ntail = receive(x is y)\n"
    namespace = {"__builtins__": {}}
    exec(compile(ordinary, "<tuple identity operand>", "exec", dont_inherit=True, optimize=0), namespace)
    assert namespace["tail"] is True and namespace["x"] is namespace["y"]
    check(ordinary, source_path, lean_path,
          '#guard ordinaryTuple pythonSource == some ("normal", "absent", "bool:True")')

    mask = "tuple = 0\nx = (1,)\ny = tuple(missing)\n___assertTrue(x is y)\n"
    assert execute(mask, python_seed, expected={"tuple": 0, "x": (1,)}) == "NameError:missing"
    one = ".tupleObject ⟨some 1, [.int 1]⟩"
    check(mask, source_path, lean_path, outcome(seed, "NameError:missing",
          f'[("x", {one}), ("tuple", .int 0)]',
          '[("tuple", .error (.raised (.runtime (.nameError "missing"))))]', allocated=f"[{one}]"))
    return {"tracked_constructor_alias": True, "canonical_empty": True, "failure_payload_and_order": True,
            "closed_origin_alias": True, "independent_closed_origins_unknown": True}


def tuple_empty_list_controls(source_path, lean_path):
    seed = "(legacyTupleIdentitySeed .builtin)"
    python_seed = {"tuple": tuple, "___assertEqual": assert_equal, "___assertTrue": assert_true}

    source = (
        "saved = tuple\ntuple = 7\ntuple = saved\nfirst = tuple([])\nsecond = tuple([])\n"
        "___assertTrue(first is second)\n"
    )
    bindings = ({"saved": tuple, "tuple": tuple, "first": (), "second": ()})
    assert execute(source, python_seed, expected=bindings) == "normal"
    check(source, source_path, lean_path, outcome(
        seed, "normal", '[("second", .returnedTuple []), ("first", .returnedTuple []), '
        '("tuple", .builtin .tuple), ("saved", .builtin .tuple)]',
        '[("tuple", .ok (.returnedTuple [])), ("tuple", .ok (.returnedTuple [])), ("___assertTrue", .ok .none)]',
        appended_lists="[[], []]"))

    # Preserve the list through both an inner and an outer mask, and skip it on a missing name.
    first_receipt = '[("tuple", .ok (.returnedTuple []))]'
    inner_missing = '[("tuple", .error (.raised (.runtime (.nameError "tuple"))))]'
    inner_masked = '[("tuple", .error (.raised (.runtime .notCallable)))]'
    outer_masked = '[("tuple", .ok (.returnedTuple [])), ("___assertEqual", .error (.raised (.runtime .notCallable)))]'
    no_tuple = '(initial "legacy_builtin")'
    no_helper = '(Namespace.mk [] [("tuple", .builtin .tuple)])'
    mask_outer = f'({seed}.bindGlobal "___assertEqual" .none)'
    for right, supplied, initial, space, status, receipts, lists in (
        ("missing", {"tuple": tuple}, {}, no_helper, "NameError:___assertEqual", "[]", "[]"),
        ("missing", {"___assertEqual": assert_equal}, {}, no_tuple, "NameError:tuple", inner_missing, "[]"),
        ("missing", python_seed, {"tuple": None}, f'({seed}.bindGlobal "tuple" .none)',
         "TypeError", inner_masked, "[[]]"),
        ("missing", python_seed, {"___assertEqual": None}, mask_outer,
         "NameError:missing", first_receipt, "[[]]"),
        ("()", python_seed, {"___assertEqual": None}, mask_outer, "TypeError", outer_masked, "[[]]"),
    ):
        code = f"___assertEqual(tuple([]), {right})\ntail = 9\n"
        assert execute(code, supplied, initial, initial) == status
        check(code, source_path, lean_path,
              outcome(space, status, f"{space}.moduleGlobals", receipts, appended_lists=lists))

    missing = "keep = 7\ntuple([])\ntail = 9\n"
    assert execute(missing, {}, expected={"keep": 7}) == "NameError:tuple"
    check(missing, source_path, lean_path,
          '#guard ordinaryTupleLists pythonSource == some (.raised (.nameError "tuple"), #[[.int 31]], some (.int 7))')

    ordinary = "def value():\n    return 7\nkeep = value()\ntuple = None\ntuple([])\ntail = 9\n"
    namespace = {"__builtins__": {}}
    try:
        exec(compile(ordinary, "<empty list tuple>", "exec", dont_inherit=True, optimize=0), namespace)
    except TypeError:
        assert namespace["keep"] == 7 and "tail" not in namespace
    else:
        raise AssertionError("The ordinary tuple binding is masked")
    check(ordinary, source_path, lean_path,
          '#guard ordinaryTupleLists pythonSource == some (.raised .notCallable, #[[.int 31], []], some (.int 7))')
    return {"canonical_empty": True, "reached_lists": True, "lookup_and_operand_order": True}


def tuple_flat_list_controls(source_path, lean_path):
    seed = "(legacyTupleIdentitySeed .builtin)"
    python_seed = {"tuple": tuple, "___assertEqual": assert_equal, "___assertTrue": assert_true}
    display = "[False, None, -7, 6]"
    values = (False, None, -7, 6)
    items = "[.bool false, .none, .int (-7), .int 6]"
    source = (
        f"first = tuple({display})\nsecond = tuple({display})\nsaved = first\n"
        "___assertTrue(saved is first)\n___assertTrue(first is not second)\n"
        "___assertEqual(first, (False, None, -7, 6))\n"
    )

    def equal_exact(left, right):
        assert_equal(left, right)
        assert tuple(map(type, left)) == (bool, type(None), int, int)

    bindings = {"first": values, "second": values, "saved": values}
    assert execute(source, {**python_seed, "___assertEqual": equal_exact}, expected=bindings) == "normal"
    argument = list(values)
    converted = tuple(argument)
    assert converted is not argument and converted == values

    first = f".tupleObject ⟨some 1, {items}⟩"
    second = f".tupleObject ⟨some 2, {items}⟩"
    residual = f'[("saved", {first}), ("second", {second}), ("first", {first})]'
    calls = (f'[("tuple", .ok ({first})), ("tuple", .ok ({second})), '
             '("___assertTrue", .ok .none), ("___assertTrue", .ok .none), ("___assertEqual", .ok .none)]')
    check(source, source_path, lean_path, outcome(seed, "normal", residual, calls,
          allocated=f"[.returnedTuple {items}, .returnedTuple {items}]", appended_lists=f"[{items}, {items}]"))

    nested = f"___assertEqual(tuple({display}), missing)\ntail = 9\n"
    assert execute(nested, python_seed, expected={}) == "NameError:missing"
    check(nested, source_path, lean_path, outcome(seed, "NameError:missing", "[]", f'[("tuple", .ok ({first}))]',
          allocated=f"[.returnedTuple {items}]", appended_lists=f"[{items}]"))

    masked = f'({seed}.bindGlobal "tuple" .none)'
    mask_receipt = '[("tuple", .error (.raised (.runtime .notCallable)))]'
    override = {"tuple": None}
    assert execute(nested, python_seed, override, override) == "TypeError"
    check(nested, source_path, lean_path, outcome(
        masked, "TypeError", f"{masked}.moduleGlobals", mask_receipt, appended_lists=f"[{items}]"))

    ordinary = f"keep = 7\ntuple = None\ntuple({display})\ntail = 9\n"
    assert execute(ordinary, {}, expected={"keep": 7, "tuple": None}) == "TypeError"
    check(ordinary, source_path, lean_path,
          f'#guard ordinaryTupleLists pythonSource == some (.raised .notCallable, #[[.int 31], {items}], some (.int 7))')
    return {"ordered_scalar_tags": True, "fresh_results": True, "reached_heaps_and_receipts": True}


def tuple_text_controls(source_path, lean_path):
    seed = "(legacyTupleIdentitySeed .builtin)"
    python_seed = {"tuple": tuple, "___assertEqual": assert_equal, "___assertTrue": assert_true}
    value = tuple("é😀e\u0301\ud800")
    assert tuple(map(ord, value)) == (233, 128512, 101, 769, 55296)
    literal = ascii("".join(value))
    items = "[" + ", ".join(f".text ⟨[{ord(item)}], by decide⟩" for item in value) + "]"
    first = f".tupleObject ⟨some 1, {items}⟩"
    second = f".tupleObject ⟨some 2, {items}⟩"
    source = (
        f"first = tuple({literal})\nsaved = tuple\ntuple = None\nsecond = saved({literal})\n"
        "empty = saved('')\n"
        "___assertTrue(first is not second)\n___assertTrue(empty is ())\n"
        f"___assertEqual(first, {ascii(value)})\n___assertEqual(first, second)\n"
    )
    expected = {"first": value, "second": value, "saved": tuple, "tuple": None, "empty": ()}
    assert execute(source, python_seed, expected=expected, identity_warning=True) == "normal"
    calls = (
        f'[("tuple", .ok ({first})), ("saved", .ok ({second})), ("saved", .ok (.returnedTuple [])), '
        '("___assertTrue", .ok .none), ("___assertTrue", .ok .none), '
        '("___assertEqual", .ok .none), ("___assertEqual", .ok .none)]'
    )
    bindings = (f'[("empty", .returnedTuple []), ("second", {second}), ("tuple", .none), '
                f'("saved", .builtin .tuple), ("first", {first})]')
    check(source, source_path, lean_path, outcome(seed, "normal", bindings, calls,
          allocated=f"[.returnedTuple {items}, .returnedTuple {items}]"))

    source = f"___assertEqual(tuple({literal}), missing)\ntail = 9\n"
    assert execute(source, python_seed, expected={}) == "NameError:missing"
    check(source, source_path, lean_path, outcome(seed, "NameError:missing", "[]",
          f'[("tuple", .ok ({first}))]', allocated=f"[.returnedTuple {items}]"))
    masked = f'({seed}.bindGlobal "tuple" .none)'
    assert execute(source, python_seed, {"tuple": None}, {"tuple": None}) == "TypeError"
    check(source, source_path, lean_path, outcome(masked, "TypeError", f"{masked}.moduleGlobals",
          '[("tuple", .error (.raised (.runtime .notCallable)))]'))
    assert execute(source, {"___assertEqual": assert_equal}, expected={}) == "NameError:tuple"
    check(source, source_path, lean_path, outcome('(initial "legacy_builtin")', "NameError:tuple", "[]",
          '[("tuple", .error (.raised (.runtime (.nameError "tuple"))))]'))

    assert tuple("é") != tuple("e\u0301")
    assert ("1",) != (1,)
    for source, left, right in (
        ("___assertEqual(tuple('é'), ('e', '\\u0301'))", "[.text ⟨[233], by decide⟩]",
         "[.text ⟨[101], by decide⟩, .text ⟨[769], by decide⟩]"),
        ("___assertEqual(('1',), (1,))", "[.text ⟨[49], by decide⟩]", "[.int 1]"),
    ):
        assert execute(source, python_seed, expected={}).startswith("AssertionError:")
        failure = f".assertionError (.tuplePair {left} {right})"
        constructor = source.startswith("___assertEqual(tuple")
        receipts = f'("tuple", .ok (.tupleObject ⟨some 1, {left}⟩)), ' if constructor else ""
        allocated = f"[.returnedTuple {left}]" if constructor else "[]"
        check(source, source_path, lean_path,
              f'#guard tupleOutcome pythonSource {seed} (raised ({failure})) [] '
              f'[{receipts}("___assertEqual", .error (.raised ({failure})))] {allocated}')
    return {"ordered_code_points": list(map(ord, value)), "fresh_nonempty": True,
            "canonical_empty": True, "ordered_errors_and_receipts": True}


def replay_tuple_truth(checkout, source_path, lean_path):
    source = SUITE["pinned_source"](checkout, TUPLE_TRUTH_PIN, TUPLE_TRUTH_SHA)
    raw = (checkout / TUPLE_TRUTH_PIN).read_bytes()
    assert raw == source.encode("utf-8")
    stock_helper = SUITE["pinned_truth_helper"](checkout)
    missing = "NameError:___assertTrue"
    assert execute(raw, {}, expected={}) == missing
    failed = '[("___assertTrue", .error (.raised (.runtime (.nameError "___assertTrue"))))]'
    receipts = '(List.replicate 2 ("___assertTrue", .ok .none))'
    guards = ['#guard ordinaryBindings pythonSource (.raised (.nameError "___assertTrue")) []']
    for profile in ("empty", "legacy_builtin", "legacy_preamble"):
        assert SUITE["cpython"](raw, profile, expected_globals={}) == [missing, "absent", "absent"]
        space = f'(initial {json.dumps(profile)})'
        guards.append(outcome(space, missing, f"{space}.moduleGlobals", failed))
    for placement in ("builtin", "preamble"):
        trace = []

        def observe(value):
            assert stock_helper(value) is None
            trace.append((type(value), value))

        helper = {"___assertTrue": observe}
        fallback, initial = (helper, {}) if placement == "builtin" else ({}, helper)
        assert execute(raw, fallback, initial, initial) == "normal"
        assert trace == [(bool, True), (tuple, (42,))]
        space = f"(legacyTupleIdentitySeed .{placement})"
        guards.extend((
            f"#guard tupleTruthArguments pythonSource {space} == some [.bool true, .returnedTuple [.int 42]]",
            outcome(space, "normal", f"{space}.moduleGlobals", receipts),
        ))
    check(source, source_path, lean_path, *guards)
    return {"sha256": TUPLE_TRUTH_SHA, "arguments": [True, [42]], "receipts": 2,
            "fixed_profiles": missing, "stock_helper_placements": "normal"}


def tuple_truth_controls(source_path, lean_path):
    seed = "(legacyTupleIdentitySeed .builtin)"
    python_seed = {"___assertTrue": assert_true}
    fixtures = []

    source = "keep = 7\n___assertTrue((0, False, None))\n___assertTrue(())\ntail = 9\n"
    assert execute(source, python_seed, expected={"keep": 7}) == "AssertionError:tuple:()"
    failure = '.error (.raised (.assertionError .emptyTuple))'
    receipts = f'[("___assertTrue", .ok .none), ("___assertTrue", {failure})]'
    fixtures.append((source, outcome(seed, "AssertionError:tuple:()", '[("keep", .int 7)]', receipts)))

    source = "___assertTrue(not (42,))\n"
    assert execute(source, python_seed, expected={}) == "AssertionError:bool:False"
    receipts = '[("___assertTrue", .error (.raised (.assertionError (.boolean false))))]'
    fixtures.append((source, outcome(seed, "AssertionError:bool:False", "[]", receipts)))

    source = "item = 0\nt = (item,)\nsaved = ___assertTrue\n___assertTrue = None\nsaved(t)\n"
    assert execute(source, python_seed, expected={"item": 0, "t": (0,), "saved": assert_true,
                                                  "___assertTrue": None}) == "normal"
    bindings = ('[("___assertTrue", .none), ("saved", .helper .assertTrue), '
                '("t", .tupleObject ⟨some 1, [.int 0]⟩), ("item", .int 0)]')
    fixtures.append((source, outcome(seed, "normal", bindings, '[("saved", .ok .none)]',
                                     allocated="[.returnedTuple [.int 0]]")))

    source = "___assertTrue = 0\n___assertTrue((missing,))\ntail = 9\n"
    assert execute(source, python_seed, expected={"___assertTrue": 0}) == "NameError:missing"
    fixtures.append((source, outcome(seed, "NameError:missing", '[("___assertTrue", .int 0)]')))

    source = "___assertTrue = 0\n___assertTrue((0,))\ntail = 9\n"
    assert execute(source, python_seed, expected={"___assertTrue": 0}) == "TypeError"
    receipts = '[("___assertTrue", .error (.raised (.runtime .notCallable)))]'
    fixtures.append((source, outcome(seed, "TypeError", '[("___assertTrue", .int 0)]', receipts)))

    INTAKE["check_lean_batch"](source_path, lean_path, fixtures, LEAN, extra_imports=SUITE["IMPORTS"])
    return {"fixtures": len(fixtures), "tuple_and_boolean_payloads": True, "tracked_tuple": True,
            "live_helper_and_error_order": True}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--upstream", type=Path, required=True)
    args = parser.parse_args()
    assert sys.version_info[:3] == (3, 13, 5), sys.version
    with tempfile.TemporaryDirectory() as scratch:
        source = Path(scratch) / "Fixture.py"
        lean = source.with_suffix(".lean")
        evidence = {"cpython": sys.version.split()[0], "pin": replay_pin(args.upstream, source, lean),
                    "methods": method_controls(), "chains": chain_controls(source, lean),
                    "constructors": constructor_controls(source, lean),
                    "linked_constructors": replay_constructors(args.upstream, source, lean),
                    "immutable_alias": replay_immutable_alias(args.upstream, source, lean),
                    "module_text_binding": module_text_binding_controls(source, lean),
                    "tuple_helper": tuple_helper_controls(source, lean),
                    "live_comparison_pin": replay_live_tuple_comparison(args.upstream, source, lean),
                    "live_comparisons": live_comparison_controls(source, lean),
                    "tuple_identity": tuple_identity_controls(source, lean),
                    "tuple_truth_pin": replay_tuple_truth(args.upstream, source, lean),
                    "tuple_truth_controls": tuple_truth_controls(source, lean),
                    "empty_list_tuple": tuple_empty_list_controls(source, lean),
                    "flat_list_tuple": tuple_flat_list_controls(source, lean),
                    "text_tuple": tuple_text_controls(source, lean)}
    print(json.dumps(evidence))

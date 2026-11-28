# SPDX-License-Identifier: MIT
"""Check dictionary argument preparation and stock equality against CPython."""

import argparse
import ast
import json
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile

DICTIONARY = runpy.run_path(str(Path(__file__).with_name("check-python-persistent-dictionary.py")))
PIN = "tests/python/programs/original/lambda-py/python-reference/dict/dict-clear.py"
SHA256 = "125aeabb914c920e323fb603bc43abedbf218ae8f991e9e8848d8e075e84f499"
FILENAME = "<dictionary arguments>"


def cpython(source, profile):
    objects, comparisons, clears = [], [], []
    builtins = {}
    namespace = {"__builtins__": builtins}

    def remember(value):
        if type(value) is dict and all(value is not other for other in objects):
            objects.append(value)

    def assert_equal(left, right):
        remember(left)
        remember(right)
        comparisons.append((left, right))
        assert left == right, (left, right)

    def trace(frame, event, _):
        if frame.f_code.co_filename != FILENAME:
            return None
        if event in ("line", "return"):
            for name, value in frame.f_globals.items():
                if name != "__builtins__":
                    remember(value)
        return trace

    def call(frame, event, callee):
        if (frame.f_code.co_filename == FILENAME and event == "c_return" and
                type(getattr(callee, "__self__", None)) is dict and callee.__name__ == "clear"):
            clears.append(callee.__self__)

    if profile == "builtin":
        builtins["___assertEqual"] = assert_equal
    if profile == "preamble":
        namespace["___assertEqual"] = assert_equal
    original_trace, original_profile = sys.gettrace(), sys.getprofile()
    try:
        sys.settrace(trace)
        sys.setprofile(call)
        exec(compile(source, FILENAME, "exec", dont_inherit=True, optimize=0), namespace)
        status = "normal"
    except NameError as error:
        status = f"NameError:{error.name}"
    except TypeError as error:
        assert str(error) == "'int' object is not callable"
        status = "TypeError"
    except AssertionError as error:
        left, right = comparisons[-1]
        ((actual_left, actual_right),) = error.args
        assert actual_left is left and actual_right is right
        status = "AssertionError"
    finally:
        sys.settrace(original_trace)
        sys.setprofile(original_profile)
    namespace.pop("__builtins__")
    if profile == "preamble" and namespace["___assertEqual"] is assert_equal:
        namespace.pop("___assertEqual")
    return status, namespace, objects, comparisons, len(clears), assert_equal


def fixture(source, ordinary_status, supplied_status=None, *, callee="___assertEqual",
            clear_receiver="d", reached_literal=None, outer_started=True, flat_call=False):
    guards, observations = [], {}
    names = {
        node.id for node in ast.walk(ast.parse(source))
        if isinstance(node, ast.Name) and isinstance(node.ctx, ast.Store)
    }
    for profile in ("ordinary", *DICTIONARY["PROFILES"]):
        status, bindings, objects, compared, clears, stock = cpython(source, profile)
        supplied = profile in ("builtin", "preamble")
        expected = supplied_status if supplied and supplied_status is not None else ordinary_status
        assert status == expected, (profile, status, expected)
        # CPython does not expose a temporary display when a later read or call
        # fails. The Lean guard checks the reached allocation separately.
        if reached_literal is not None:
            assert status != "normal" and not compared
            objects.append(reached_literal.copy())
        object_term = DICTIONARY["object_term"]
        values = [
            (name, ".helper .assertEqual" if value is stock else DICTIONARY["value_term"](value, objects))
            for name, value in bindings.items()
        ]
        values = "[" + ", ".join(f"({json.dumps(name)}, {value})" for name, value in values) + "]"
        ledger = "[" + ", ".join(object_term(i, value) for i, value in enumerate(objects, 1)) + "]"
        receipts = [f'("{clear_receiver}.clear", .ok .none)'] * clears
        ordinary_events = clears
        match status:
            case "normal":
                assert len(compared) == 1
                receipt, completion = ".ok .none", ".ok ()"
            case "AssertionError":
                assert len(compared) == 1
                entries = [DICTIONARY["entries_term"](value) for value in compared[0]]
                error = f'.raised (.assertionError (.dictionaryPair {entries[0]} {entries[1]}))'
                receipt, completion = f".error ({error})", f".error ({error})"
            case "TypeError":
                assert not compared
                receipt = completion = ".error (.raised (.runtime .notCallable))"
                ordinary, ordinary_events = ".raised .notCallable", ordinary_events + 1
            case _:
                assert status.startswith("NameError:") and not compared
                error = f'.nameError {json.dumps(status.removeprefix("NameError:"))}'
                completion = f".error (.raised (.runtime ({error})))"
                receipt = completion if flat_call else None
                ordinary = f".raised ({error})"
                ordinary_events += int(outer_started)
        if receipt is not None:
            receipts.append(f"({json.dumps(callee)}, {receipt})")
        if profile == "ordinary":
            assert status not in ("normal", "AssertionError")
            absent = json.dumps(sorted(names - bindings.keys()))
            guards.append(f"#guard ordinaryDictionary pythonSource ({ordinary}) {values} {absent} "
                          f"{ledger} {ordinary_events} {clears}")
        else:
            seed = DICTIONARY["PROFILES"][profile]
            guards.append(f"#guard seededDictionary pythonSource {seed} ({completion}) {values} {ledger} "
                          f"[{', '.join(receipts)}]")
        observations[profile] = {
            "completion": status, "bindings": values, "objects": ledger,
            "ordinary_event_count": ordinary_events if profile == "ordinary" else None,
            "receipts": [] if profile == "ordinary" else receipts,
        }
    return (source, "\n".join(guards)), observations


def controls(upstream):
    tests, observed = [], {}

    def add(label, source, status, supplied=None, **kwargs):
        test, outcome = fixture(source, status, supplied, **kwargs)
        tests.append(test)
        observed[label] = outcome

    missing_helper = "NameError:___assertEqual"
    add("two fresh empty displays", "___assertEqual({}, {})\n", missing_helper, "normal")
    add("insertion order and exact key/value equality", """d = {True: 3, 1: 'x', 'z': False, '\\ud800': None}
e = {'\\ud800': None, 'z': 0, 1: 'x'}
___assertEqual(d, e)
""", missing_helper, "normal", flat_call=True)
    add("unequal values for the same key", "___assertEqual({1: 2}, {True: 3})\n",
        missing_helper, "AssertionError")
    add("clear is visible via alias in mismatch", """d = {1: 2}
alias = d
d.clear()
___assertEqual(alias, {True: 2})
tail = 9
""", missing_helper, "AssertionError")
    add("clear is visible via either alias", """d = {1: 2}
alias = d
d.clear()
___assertEqual(d, alias)
""", missing_helper, "normal", flat_call=True)
    add("stock descriptor under a different name", """d = {1: 2}
compare = ___assertEqual
___assertEqual = 7
compare({1: 2}, d)
""", missing_helper, "normal", callee="compare", outer_started=False)
    add("noncallable mask after arguments", """d = {}
___assertEqual = 7
___assertEqual(d, {1: 2})
tail = 9
""", "TypeError", reached_literal={1: 2})
    add("callee miss skips display", "d = {1: 2}\nd.clear()\nabsent({}, missing)\n",
        "NameError:absent", callee="absent")
    add("first argument miss skips display", "entry = 7\nentry(missing, {1: 2})\n",
        "NameError:missing", callee="entry")
    add("first display survives later argument miss", "entry = 7\nentry({1: 2}, missing)\n",
        "NameError:missing", callee="entry", reached_literal={1: 2})

    rejected = "#guard (match compile pythonSource with | .error _ => true | _ => false)"
    tests.extend((source, rejected) for source in (
        "___assertEqual({1: {}}, {})\n",
        "___assertEqual({**d}, {})\n",
        "___assertEqual({1: name}, {})\n",
    ))
    if upstream is not None:
        raw = DICTIONARY["SUITE"]["pinned_source"](upstream, PIN, SHA256)
        lines = raw.splitlines(keepends=True)
        assert lines[2] == "___assertEqual(d, {})\n"
        assert lines[4].rstrip() == "___assertRaises(TypeError, d.clear, None)"
        add("unchanged pin prefix", "".join(lines[:3]), missing_helper, "normal")
        assert DICTIONARY["cpython"](raw, "builtin")[0] == "normal"
        tests.append((raw, """#guard (match compile pythonSource with
  | .error (.source (.scalar .expressionProfile)) => true
  | _ => false)"""))
    return tests, observed


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", type=Path)
    options = parser.parse_args()
    assert sys.implementation.name == "cpython"
    revision = None
    if options.upstream is not None:
        assert sys.version_info[:3] == (3, 13, 5), sys.version
        revision = subprocess.check_output(["git", "-C", str(options.upstream), "rev-parse", "HEAD"], text=True).strip()
        assert revision == DICTIONARY["SUITE"]["UPSTREAM_REVISION"]
    fixtures, observed = controls(options.upstream)
    with tempfile.TemporaryDirectory() as directory:
        src, lean = (Path(directory) / name for name in ("Fixture.py", "Fixtures.lean"))
        DICTIONARY["INTAKE"]["check_lean_batch"](src, lean, fixtures, DICTIONARY["LEAN"],
                                                extra_imports=DICTIONARY["SUITE"]["IMPORTS"])
    print(json.dumps({"cpython": sys.version.split()[0], "upstream": revision, "fixtures": len(fixtures),
                      "observations": observed}))

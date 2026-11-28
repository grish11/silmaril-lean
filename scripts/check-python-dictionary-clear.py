# SPDX-License-Identifier: MIT
"""Compare checked stock dictionary clearing with pinned CPython."""

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


def fixture(source, expected_status, returns, *, failed=None, expected_missing=()):
    guards, observations = [], {}
    names = {
        node.id for node in ast.walk(ast.parse(source))
        if isinstance(node, ast.Name) and isinstance(node.ctx, ast.Store)
    }
    for profile in ("ordinary", *DICTIONARY["PROFILES"]):
        method_events = []
        status, bindings, objects, helpers, _ = DICTIONARY["cpython"](source, profile, method_events)
        assert status == expected_status and not helpers, (profile, status, expected_status)
        assert sorted(names - bindings.keys()) == list(expected_missing)
        expected_methods = [(method, "c_return") for _, method, _ in returns]
        if status == "TypeError":
            assert failed is not None
            expected_methods.extend((("clear", "c_exception"), ("TypeError", "dict.clear() takes no arguments (1 given)")))
        assert method_events == expected_methods, (profile, method_events, expected_methods)

        object_term = DICTIONARY["object_term"]
        value_term = DICTIONARY["value_term"]
        ledger = "[" + ", ".join(object_term(index, obj) for index, obj in enumerate(objects, start=1)) + "]"
        values = "[" + ", ".join(f"({json.dumps(name)}, {value_term(value, objects)})"
                                  for name, value in bindings.items()) + "]"
        receipts = []
        clear_count = 0
        for receiver, method, destination in returns:
            if method == "clear":
                clear_count += 1
            value = bindings[destination] if destination is not None else None
            if method == "clear":
                assert value is None
            receipts.append(DICTIONARY["ok_receipt"](f"{receiver}.{method}", value, objects))

        match status:
            case "normal":
                ordinary, seeded = ".normal", ".ok ()"
            case "TypeError":
                error = ".positionalArity 0 1"
                ordinary, seeded = f".raised ({error})", f".error (.raised (.runtime ({error})))"
                receipts.append(f'("{failed}.clear", .error (.raised (.runtime ({error}))))')
            case "AttributeError:clear":
                ordinary, seeded = ".executorFault .unsupportedDictionaryOperand", ".error .unsupported"
                receipts.append(f'("{failed}.clear", .error .unsupported)')
            case name_error if name_error.startswith("NameError:"):
                error = f'.nameError {json.dumps(name_error.removeprefix("NameError:"))}'
                ordinary, seeded = f".raised ({error})", f".error (.raised (.runtime ({error})))"
                receipts.append(f'("{failed}.clear", .error (.raised (.runtime ({error}))))')
            case _:
                raise AssertionError(status)

        ordinary_receipts = [".complete (.ok .none)"] * clear_count
        arity = "none"
        if status == "TypeError":
            arity = "(some 1)"
            ordinary_receipts.append(".complete (.error (.positionalArity 0 1))")
        if profile == "ordinary":
            guards.append(f"#guard ordinaryDictionary pythonSource ({ordinary}) {values} "
                          f"{json.dumps(expected_missing)} {ledger} {len(ordinary_receipts)} {clear_count} {arity}")
        else:
            seed = DICTIONARY["PROFILES"][profile]
            guards.append(f"#guard seededDictionary pythonSource {seed} ({seeded}) "
                          f"{values} {ledger} [{', '.join(receipts)}]")
        observations[profile] = {
            "cpython_status": status,
            "runner_completion": ordinary if profile == "ordinary" else seeded,
            "bindings": values,
            "objects": ledger,
            "receipts": ordinary_receipts if profile == "ordinary" else receipts,
        }
    return (source, "\n".join(guards)), observations


def controls(upstream):
    tests, observations = [], {}
    for label, source, status, returns, failed, missing in (
        ("clear through alias and keep distinct dictionaries", """
d = {1: 3}
alias = d
other = {1: 3}
before = alias.get(1)
result = d.clear()
miss = alias.get(1, 9)
retained = other.get(1)
d = {1: 5}
alias.clear()
current = d.get(1)
empty = alias.get(1)
""", "normal", (("alias", "get", "before"), ("d", "clear", "result"), ("alias", "get", "miss"),
                ("other", "get", "retained"), ("alias", "clear", None), ("d", "get", "current"),
                ("alias", "get", "empty")), None, ()),
        ("truth follows live aliases", """
d = {1: 3}
alias = d
assert d
d.clear()
assert not alias
""", "normal", (("d", "clear", None),), None, ()),
        ("arity failure retains distinct object and earlier clear", """
d = {1: 3}
other = {1: 5}
done = d.clear()
bad = other.clear(None)
tail = 9
""", "TypeError", (("d", "clear", "done"),), "other", ("bad", "tail")),
        ("later argument lookup precedes arity", """
d = {1: 3}
prior = d.get(1)
bad = d.clear(prior, missing)
tail = 9
""", "NameError:missing", (("d", "get", "prior"),), "d", ("bad", "tail")),
        ("first argument lookup comes first", """
d = {1: 3}
bad = d.clear(first, second)
tail = 9
""", "NameError:first", (), "d", ("bad", "tail")),
        ("wrong receiver precedes argument lookup", """
d = {1: 3}
alias = d
d = 7
bad = d.clear(missing)
tail = 9
""", "AttributeError:clear", (), "d", ("bad", "tail")),
        ("missing receiver precedes argument lookup", """
d = {1: 3}
bad = absent.clear(missing)
tail = 9
""", "NameError:absent", (), "absent", ("bad", "tail")),
    ):
        test, observed = fixture(source, status, returns, failed=failed, expected_missing=missing)
        tests.append(test)
        observations[label] = observed

    rejects = "#guard (match compile pythonSource with | .error _ => true | _ => false)"
    tests.extend((source, rejects) for source in (
        "d = {1: 3}; callback = d.clear\n",
        "d = {1: 3}; d.clear(unchecked())\n",
        "d = {1: 3}; d.clear(*spread)\n",
        "d = {1: 3}; d.clear(extra=1)\n",
    ))
    if upstream is not None:
        source = DICTIONARY["SUITE"]["pinned_source"](upstream, PIN, SHA256)
        lines = source.splitlines(keepends=True)
        assert lines[1] == "d.clear()\n" and lines[2] == "___assertEqual(d, {})\n"
        assert lines[4].rstrip() == "___assertRaises(TypeError, d.clear, None)"
        test, observed = fixture("".join(lines[:2]), "normal", (("d", "clear", None),))
        tests.append(test)
        tests.append((source, rejects))
        assert DICTIONARY["cpython"](source, "builtin")[0] == "normal"
        observations["unchanged pin prefix"] = {
            "sha256": SHA256, "completed_through": 2, "profiles": observed,
            "following_line": lines[2].rstrip(), "later_line": lines[4].rstrip(),
        }
    return tests, observations


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
    tests, observations = controls(options.upstream)
    with tempfile.TemporaryDirectory() as directory:
        src, lean = (Path(directory) / name for name in ("Fixture.py", "Fixtures.lean"))
        DICTIONARY["INTAKE"]["check_lean_batch"](src, lean, tests, DICTIONARY["LEAN"],
                                                extra_imports=DICTIONARY["SUITE"]["IMPORTS"])
    print(json.dumps({"cpython": sys.version.split()[0], "upstream": revision, "fixtures": len(tests),
                      "observations": observations}))

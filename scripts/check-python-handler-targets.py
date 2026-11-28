# SPDX-License-Identifier: MIT
"""Check module handler targets and their implicit deletion against CPython 3.13.5."""

import argparse
import json
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile


RAISE = runpy.run_path(str(Path(__file__).with_name("check-python-stock-exception-raise.py")))
SUITE = RAISE["SUITE"]
INTAKE = RAISE["INTAKE"]
bindings = RAISE["bindings"]
truth_name = "___assertTrue"


def execute(raw, initial, builtin_names, expected, missing=None, identity=None):
    builtins = dict(builtin_names)
    namespace = dict(initial, __builtins__=builtins)
    try:
        exec(compile(raw, "<handler target>", "exec", dont_inherit=True, optimize=0), namespace)
    except NameError as error:
        assert missing is not None and type(error) is NameError and error.name == missing
    else:
        assert missing is None
    assert namespace.pop("__builtins__") is builtins and builtins == builtin_names
    assert namespace.keys() == expected.keys()
    for name, wanted in expected.items():
        actual = namespace[name]
        assert type(actual) is type(wanted)
        if isinstance(wanted, BaseException):
            assert actual.args == wanted.args
        else:
            assert actual == wanted
    if identity:
        first, second = identity
        assert namespace[first] is namespace[second]


def guard(source, writes, *, seed=None, missing=None, removed=(), identity=None):
    seed = seed or {}
    preamble = {name: value for name, value in seed.items() if name not in removed} | writes
    execute(source.encode(), seed, {}, preamble, missing, identity)
    execute(source.encode(), {}, seed, writes, missing, identity)
    ordinary, seeded = RAISE["errors"](None if missing is None else ("name", missing))
    initial = bindings(seed)
    return source, f"""#guard ordinaryRaise pythonSource {initial} {bindings(preamble)} ({ordinary})
#guard seededRaise pythonSource ⟨[], {initial}⟩ {bindings(writes)} ({seeded}) []
#guard seededRaise pythonSource ⟨{initial}, []⟩ {bindings(preamble)} ({seeded}) []"""


def controls(checkout):
    yield guard(r'''
try:
    body = 7
    raise Exception("\u00e9\U0001f600\ud800")
except Exception as caught:
    saved = caught
    alias = caught
    caught = 28
except Missing as unused:
    wrong = 1
else:
    wrong = 2
finally:
    cleaned = saved
tail = body
''', {"body": 7, "saved": Exception("é😀\ud800"), "alias": Exception("é😀\ud800"),
      "cleaned": Exception("é😀\ud800"), "tail": 7},
        seed={"Exception": Exception, "caught": 17}, removed=("caught",), identity=("saved", "alias"))

    yield guard("""
try:
    assert False
except TypeError as untouched:
    wrong = 1
except AssertionError as caught:
    saved = caught
    reached = 6
    stopped = handler_missing
    wrong = 2
finally:
    cleaned = reached
    escaped = saved
tail = 8
""", {"saved": AssertionError(), "reached": 6, "cleaned": 6, "escaped": AssertionError()},
        seed={"TypeError": TypeError, "AssertionError": AssertionError, "untouched": 11},
        missing="handler_missing", identity=("saved", "escaped"))

    yield guard("""
caught = 19
try:
    raise Exception()
except Exception as caught:
    saved = caught
    stopped = handler_missing
finally:
    cleaned = saved
    observed = caught
tail = 8
""", {"saved": Exception(), "cleaned": Exception()}, seed={"Exception": Exception},
        missing="caught", identity=("saved", "cleaned"))

    source = """
caught = 3
try:
    assert False
except AssertionError as caught:
    saved = caught
finally:
    fallback = caught
"""
    seed = {"AssertionError": AssertionError, "caught": 17}
    execute(source.encode(), {}, seed, {"saved": AssertionError(), "fallback": 17})
    yield source, f"""#guard seededRaise pythonSource ⟨[], {bindings(seed)}⟩
  {bindings({"saved": AssertionError(), "fallback": 17})} (.ok ()) []"""

    source = """
___assertTrue(True)
try:
    raise Exception("one")
except Exception as caught:
    saved = caught
finally:
    cleaned = saved
"""
    truth = SUITE["pinned_truth_helper"](checkout)
    receipt = []

    def trace(value):
        result = truth(value)
        receipt.append((truth_name, type(value), value, result))
        return result

    writes = {"saved": Exception("one"), "cleaned": Exception("one")}
    seed = {"Exception": Exception, truth_name: trace}
    execute(source.encode(), {}, seed, writes, identity=("saved", "cleaned"))
    assert receipt == [(truth_name, bool, True, None)]
    yield source, f"""#guard seededRaise pythonSource
  ⟨[], [("Exception", .exceptionClass .exception), ("{truth_name}", .helper .assertTrue)]⟩
  {bindings(writes)} (.ok ()) [("{truth_name}", .ok .none)]"""


def unchanged(checkout):
    path = f"tests/python/programs/original/k-python/programs/testtry1.py"
    source = SUITE["pinned_source"](checkout, path,
        "75b614661cf9767306b18a85c483659385b3e4d33b3f63a7de1d9c352a77bce7")
    raw = (checkout / path).read_bytes()
    assert source.encode() == raw
    expected = {"x": 5, "y": 6, "z": 7}
    execute(raw, {}, {}, expected)
    entries = bindings(expected)
    guards = [f"#guard ordinaryRaise pythonSource [] {entries} .normal"]
    for profile in (".empty", 'initial "legacy_builtin"', 'initial "legacy_preamble"'):
        guards.append(f'#guard let space : Namespace := {profile}; seededRaise pythonSource space '
                      f'({entries} ++ space.moduleGlobals) (.ok ()) []')
    return source, "\n".join(guards)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--upstream", type=Path, required=True)
    args = parser.parse_args()
    assert sys.version_info[:3] == (3, 13, 5)
    revision = subprocess.check_output(["git", "-C", str(args.upstream), "rev-parse", "HEAD"], text=True).strip()
    assert revision == SUITE["UPSTREAM_REVISION"]
    cases = list(controls(args.upstream))
    with tempfile.TemporaryDirectory() as scratch:
        source = Path(scratch) / "Fixture.py"
        INTAKE["check_lean_batch"](source, source.with_suffix(".lean"), [unchanged(args.upstream)] + cases,
                                   RAISE["LEAN"], extra_imports=SUITE["IMPORTS"])
    print(json.dumps({"cpython": "3.13.5", "unchanged_pins": 1, "reached_controls": len(cases)}))

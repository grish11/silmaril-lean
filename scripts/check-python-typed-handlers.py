# SPDX-License-Identifier: MIT
"""Replay named exception-handler selection against CPython 3.13.5."""

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
LEAN = RAISE["LEAN"]
bindings = RAISE["bindings"]
PIN_DIRECTORY = "tests/python/programs/original/k-python/programs"


def execute(raw, expected, status, *, seed=None, preamble=False, context=None):
    builtins = {} if preamble else (seed or {})
    initial = seed if preamble else {}
    namespace = dict(initial or {}, __builtins__=builtins)
    try:
        exec(compile(raw, "<typed handlers>", "exec", dont_inherit=True, optimize=0), namespace)
    except Exception as error:
        if type(error) is NameError:
            selected = ("name", error.name)
        elif type(error) is TypeError:
            assert error.args == ("catching classes that do not inherit from BaseException is not allowed",)
            selected = ("invalid", None)
        elif type(error) is RuntimeError:
            assert error.args == ("No active exception to reraise",)
            selected = ("inactive", None)
        else:
            assert type(error) is Exception and len(error.args) == 1 and type(error.args[0]) is str
            selected = ("exception", error.args[0])
        if context is not None:
            assert type(error.__context__) is context
    else:
        selected = None
    assert selected == status and namespace.pop("__builtins__") is builtins
    wanted = dict(initial or {}) | expected
    assert namespace.keys() == wanted.keys()
    assert all(type(actual) is type(wanted[key]) and actual == wanted[key] for key, actual in namespace.items())


def errors(status):
    if status in (("invalid", None), ("inactive", None)):
        error = ".invalidHandlerClass" if status[0] == "invalid" else ".noActiveException"
        return f".raised {error}", f".error (.raised (.runtime {error}))"
    return RAISE["errors"](status)


def guard(source, expected, status=None, *, seed=None, context=None):
    seed = seed or {}
    raw = source.encode()
    execute(raw, expected, status, seed=seed, context=context)
    execute(raw, expected, status, seed=seed, preamble=True, context=context)
    ordinary, seeded = errors(status)
    initial, residual, preamble = bindings(seed), bindings(expected), bindings(seed | expected)
    return source, f"""#guard ordinaryRaise pythonSource {initial} {preamble} ({ordinary})
#guard seededRaise pythonSource ⟨[], {initial}⟩ {residual} ({seeded}) []
#guard seededRaise pythonSource ⟨{initial}, []⟩ {preamble} ({seeded}) []"""


def controls(checkout):
    yield guard("""
masked = None
try:
    reached = 7
except Missing:
    wrong = 1
except masked:
    wrong = 2
else:
    copied = reached
finally:
    cleaned = copied
tail = 9
""", {"masked": None, "reached": 7, "copied": 7, "cleaned": 7, "tail": 9})

    yield guard("""
handler = TypeError
try:
    reached = 7
    handler = NameError
    failed = body_missing
except TypeError:
    wrong = 1
except handler:
    caught = reached
except LaterMissing:
    wrong = 2
else:
    wrong = 3
finally:
    cleaned = caught
tail = 9
""", {"handler": NameError, "reached": 7, "caught": 7, "cleaned": 7, "tail": 9},
        seed={"TypeError": TypeError, "NameError": NameError})

    yield guard("""
try:
    reached = True
    NameError = None
    failed = body_missing
except NameError:
    wrong = 1
except LaterMissing:
    wrong = 2
finally:
    cleaned = reached
tail = 9
""", {"NameError": None, "reached": True, "cleaned": True}, ("invalid", None),
        seed={"NameError": NameError}, context=NameError)

    yield guard("""
try:
    reached = True
    assert False
except TypeError:
    wrong = 1
except FirstMissing:
    wrong = 2
except SecondMissing:
    wrong = 3
finally:
    cleaned = reached
tail = 9
""", {"reached": True, "cleaned": True}, ("name", "FirstMissing"),
        seed={"TypeError": TypeError}, context=AssertionError)

    yield guard("""
try:
    reached = True
    assert False
except Missing:
    wrong = 1
finally:
    cleaned = reached
    replaced = cleanup_missing
tail = 9
""", {"reached": True, "cleaned": True}, ("name", "cleanup_missing"), context=NameError)

    yield guard(r'''
try:
    reached = None
    raise Exception("\u00e9\U0001f600\ud800")
except AssertionError:
    wrong = 1
finally:
    cleaned = reached
tail = 9
''', {"reached": None, "cleaned": None}, ("exception", "é😀\ud800"),
        seed={"Exception": Exception, "AssertionError": AssertionError})

    yield guard("""
try:
    reached = 7
    assert False
except Exception:
    caught = reached
except LaterMissing:
    wrong = 1
finally:
    cleaned = caught
tail = 9
""", {"reached": 7, "caught": 7, "cleaned": 7, "tail": 9}, seed={"Exception": Exception})

    yield guard("""
try:
    reached = 7
    assert missing_body
except TypeError:
    wrong = 1
except:
    caught = reached
finally:
    cleaned = caught
tail = 9
""", {"reached": 7, "caught": 7, "cleaned": 7, "tail": 9}, seed={"TypeError": TypeError})

    yield guard("""
try:
    reached = 7
    raise
finally:
    cleaned = reached
""", {"reached": 7, "cleaned": 7}, ("inactive", None))

    source = """___assertTrue(True)
try:
    reached = 7
    assert False
except Missing:
    wrong = 1
finally:
    cleaned = reached
"""
    truth = SUITE["pinned_truth_helper"](checkout)
    expected = {"reached": 7, "cleaned": 7}
    execute(source.encode(), expected, ("name", "Missing"), seed={"___assertTrue": truth}, context=AssertionError)
    yield source, f"""#guard seededRaise pythonSource ⟨[], [("___assertTrue", .helper .assertTrue)]⟩
  {bindings(expected)} (.error (.raised (.runtime (.nameError "Missing")))) [("___assertTrue", .ok .none)]"""


def unchanged(checkout):
    def pinned(name, digest):
        path = f"{PIN_DIRECTORY}/{name}"
        source = SUITE["pinned_source"](checkout, path, digest)
        assert source.encode() == (checkout / path).read_bytes()
        return source

    source = pinned("testtry2.py", "b7eddf22b16dfcdd871f796fc727c2b0ab655977bdeff03972dd813b07bec0ea")
    fixed = {"y": 7}
    execute(source.encode(), fixed, ("name", "x"), context=NameError)
    guards = [f'#guard ordinaryRaise pythonSource [] {bindings(fixed)} (.raised (.nameError "x"))']
    for profile in (".empty", 'initial "legacy_builtin"', 'initial "legacy_preamble"'):
        guards.append(f'#guard let space : Namespace := {profile}; seededRaise pythonSource space '
                      f'({bindings(fixed)} ++ space.moduleGlobals) (.error (.raised (.runtime (.nameError "x")))) []')
    _, checked = guard(source, {"x": 6, "y": 7}, seed={"RuntimeError": RuntimeError})
    yield source, "\n".join(guards + [checked])


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--upstream", type=Path, required=True)
    args = parser.parse_args()
    assert sys.version_info[:3] == (3, 13, 5)
    revision = subprocess.check_output(["git", "-C", str(args.upstream), "rev-parse", "HEAD"], text=True).strip()
    assert revision == SUITE["UPSTREAM_REVISION"]
    pins = list(unchanged(args.upstream))
    reached = list(controls(args.upstream))
    with tempfile.TemporaryDirectory() as scratch:
        source = Path(scratch) / "Fixture.py"
        INTAKE["check_lean_batch"](source, source.with_suffix(".lean"), pins + reached, LEAN,
                                   extra_imports=SUITE["IMPORTS"])
    print(json.dumps({"cpython": "3.13.5", "unchanged_pins": len(pins), "reached_controls": len(reached)}))

# SPDX-License-Identifier: MIT
"""Compare byte-identical exceptional-control fixtures with the checked scalar transfer."""

import argparse
import json
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile


NORMAL = runpy.run_path(str(Path(__file__).resolve().with_name("check-python-normal-try.py")))
INTAKE = NORMAL["INTAKE"]
SUITE = NORMAL["SUITE"]
execute = NORMAL["execute"]
bindings = NORMAL["bindings"]
IMPORTS = SUITE["IMPORTS"]
LEAN = NORMAL["LEAN"]


def guard(source, expected, ordinary, seeded):
    return source, NORMAL["guard_pair"](expected, ordinary, seeded)


def name_error(name):
    return f".raised (.nameError {json.dumps(name)})", f"NameError:{name}"


def fixtures(checkout):
    cases = []
    source = """target = 90
try:
    flag = True
    target = first_missing
    skipped = later_missing
finally:
    retained = flag
    order = 5
tail = 9
"""
    expected = {"target": 90, "flag": True, "retained": True, "order": 5}
    assert execute(source.encode(), expected) == "NameError:first_missing"
    cases.append(guard(source, expected, *name_error("first_missing")))

    source = """try:
    body = 1
    absent = body_missing
finally:
    cleanup = body
    replaced = cleanup_missing
    skipped = 7
tail = 9
"""
    expected = {"body": 1, "cleanup": 1}
    assert execute(source.encode(), expected) == "NameError:cleanup_missing"
    cases.append(guard(source, expected, *name_error("cleanup_missing")))

    source = """try:
    saved = None
    assert False
    skipped = 7
finally:
    copied = saved
tail = 9
"""
    expected = {"saved": None, "copied": None}
    assert execute(source.encode(), expected) == "AssertionError:empty"
    cases.append(guard(source, expected, ".assertionError", "AssertionError:empty"))

    source = """try:
    body = 3
    absent = body_missing
except:
    handled = body
else:
    skipped = else_missing
finally:
    cleanup = handled
tail = 9
"""
    expected = {"body": 3, "handled": 3, "cleanup": 3, "tail": 9}
    assert execute(source.encode(), expected) == "normal"
    cases.append(guard(source, expected, ".normal", "normal"))

    source = """try:
    assert body_missing
except:
    handled = True
    absent = handler_missing
else:
    skipped = else_missing
finally:
    cleanup = handled
tail = 9
"""
    expected = {"handled": True, "cleanup": True}
    assert execute(source.encode(), expected) == "NameError:handler_missing"
    cases.append(guard(source, expected, *name_error("handler_missing")))

    source = """try:
    body = True
except:
    skipped = handler_missing
else:
    reached_else = body
    absent = else_missing
finally:
    cleanup = reached_else
tail = 9
"""
    expected = {"body": True, "reached_else": True, "cleanup": True}
    assert execute(source.encode(), expected) == "NameError:else_missing"
    cases.append(guard(source, expected, *name_error("else_missing")))

    source = """___assertTrue(True)
try:
    body = 3
    absent = body_missing
finally:
    cleanup = body
    assert False
tail = 9
"""
    expected = {"body": 3, "cleanup": 3}
    truth = SUITE["pinned_truth_helper"](checkout)
    assert execute(source.encode(), expected, builtins={"___assertTrue": truth}) == "AssertionError:empty"
    assert execute(source.encode(), expected, initial={"___assertTrue": truth}) == "AssertionError:empty"
    assert execute(source.encode(), {}) == "NameError:___assertTrue"
    cases.append((source, f"""#guard tryOrdinary pythonSource (.raised (.nameError "___assertTrue")) [] true
#guard trySeeded pythonSource (legacyTupleIdentitySeed .builtin)
  "AssertionError:empty" {bindings(expected)} [("___assertTrue", .ok .none)]
#guard trySeeded pythonSource (legacyTupleIdentitySeed .preamble)
  "AssertionError:empty" {bindings(expected)} [("___assertTrue", .ok .none)]"""))

    source = """retained = False
absent = prefix_missing
try:
    pass
finally:
    unreached = True
"""
    expected = {"retained": False}
    assert execute(source.encode(), expected) == "NameError:prefix_missing"
    cases.append(guard(source, expected, *name_error("prefix_missing")))
    return cases


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--upstream", type=Path, required=True)
    args = parser.parse_args()
    assert sys.version_info[:3] == (3, 13, 5), sys.version
    revision = subprocess.check_output(["git", "-C", str(args.upstream), "rev-parse", "HEAD"], text=True).strip()
    assert revision == SUITE["UPSTREAM_REVISION"], revision
    tested = fixtures(args.upstream)
    with tempfile.TemporaryDirectory() as scratch:
        source = Path(scratch) / "Fixture.py"
        INTAKE["check_lean_batch"](source, source.with_suffix(".lean"), tested, LEAN, extra_imports=IMPORTS)
    print(json.dumps({"cpython": "3.13.5", "reached_controls": len(tested)}))

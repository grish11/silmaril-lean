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
IMPORTS = SUITE["IMPORTS"] + (
    "import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.ExceptionalTry.Thms",
    "meta import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.ExceptionalTry.Defs",
    "meta import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.ExceptionalTry.Defs",
)
LEAN = SUITE["LEAN"] + """
open Compile.ModuleEntry.Functions
open Compile.ModuleEntry.Functions.ExceptionalTry (Plan)

private def isTry : Source.Stmt → Bool
  | .try_ .. => true
  | _ => false

private structure CheckedCase where
  scope : Source.Scope
  names : List String
  prefixCode : List Source.Stmt
  plan : Plan (Compile.ModuleEntry.Action scope)
  suffixCode : List (Compile.ModuleEntry.Action scope)

private def checkedCase (source : Source.Module) : Option CheckedCase := do
  let prefixCode := source.body.takeWhile (fun stmt => !isTry stmt)
  let statement :: suffix ← some (source.body.drop prefixCode.length) | none
  let tree ← (Source.analyze source).toOption
  let plan ← ExceptionalTry.check tree.scope statement
  let suffixCode ← ExceptionalTry.suite? tree.scope suffix
  pure ⟨tree.scope, tree.scope.context.assigned.eraseDups, prefixCode, plan.val, suffixCode.val⟩

private def cleanupHeap : Core.Closure.Heap := ⟨1, fun slot => if slot == 0 then some (.int 23) else none⟩
private def cleanupLists : Core.Module.ListHeap := ⟨#[[.int 31]]⟩
private def cleanupTable : Core.Closure.Executor.CodeTable := fun _ => none

private def ordinaryCleanup (source : Source.Module) (completion : Except Run.Completion Unit)
    (bindings : Bindings) : Bool := Id.run do
  let some checked := checkedCase source | return false
  let some prefixCode := ExceptionalTry.suite? checked.scope checked.prefixCode | return false
  let initial := { Run.seed .empty cleanupHeap with lists := cleanupLists }
  let before := Run.ExceptionalTry.ordinarySuite cleanupTable initial prefixCode.val
  let outcome := if before.completion.isOk then
    Run.ExceptionalTry.ordinary cleanupTable before.reached checked.plan
  else before
  let reached := if outcome.completion.isOk then
    Run.ExceptionalTry.ordinarySuite cleanupTable outcome.reached checked.suffixCode
  else outcome
  let actual := checked.names.filterMap fun name =>
    (reached.reached.globals name).map fun value => (name, Run.Seeded.seededValue value)
  return reached.completion == completion && actual.length == bindings.length &&
    bindings.all actual.contains && reached.reached.lists == cleanupLists &&
    reached.reached.heap.next == cleanupHeap.next &&
    (reached.reached.heap.contents 0).map Run.Seeded.seededValue == some (.int 23)

private def seededCleanup (source : Source.Module) (space : Namespace)
    (completion : Except Run.Seeded.ModuleFailure Unit) (bindings : Bindings)
    (receipts : List (String × Result)) : Bool := Id.run do
  let some checked := checkedCase source | return false
  let .ok prefixCode := Run.compile ⟨checked.prefixCode⟩ | return false
  let initial := Run.Seeded.run space prefixCode cleanupHeap (lists := cleanupLists)
  let context : Run.Seeded.CallContext := { table := cleanupTable, heap := cleanupHeap, fuel := 1000 }
  let outcome := Run.ExceptionalTry.seeded context initial checked.plan
  let reached := if outcome.completion.isOk then
    (Run.ExceptionalTry.seededSuite context outcome checked.suffixCode).reached
  else outcome
  let actual := reached.residual.moduleGlobals
  let expected := bindings ++ space.moduleGlobals
  return reached.completion == completion && actual.length == expected.length &&
    expected.all actual.contains && reached.residual.builtins == space.builtins &&
    reached.lists == cleanupLists && reached.heap.next == cleanupHeap.next &&
    (reached.heap.contents 0).map Run.Seeded.seededValue == some (.int 23) &&
    reached.calls.all (·.observation.caught.isNone) &&
    reached.calls.map (fun call => (call.callee, call.observation.result)) == receipts
"""


def guard(source, expected, ordinary, seeded):
    bound = bindings(expected)
    return (source, f"#guard ordinaryCleanup pythonSource ({ordinary}) {bound}\n"
            f"#guard seededCleanup pythonSource .empty ({seeded}) {bound} []")


def name_error(name):
    text = json.dumps(name)
    return f".error (.raised (.nameError {text}))", f".error (.raised (.runtime (.nameError {text})))"


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
    cases.append(guard(source, expected, ".error .assertionError", ".error (.raised (.assertionError .empty))"))

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
    cases.append(guard(source, expected, ".ok ()", ".ok ()"))

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
    cases.append((source, f"""#guard seededCleanup pythonSource (Run.Seeded.legacyTupleIdentitySeed .builtin)
  (.error (.raised (.assertionError .empty))) {bindings(expected)} [("___assertTrue", .ok .none)]"""))

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


def historical_boundaries(checkout):
    prefix = NORMAL["PREFIX"]
    table = (
        (f"{prefix}/try-except-finally.py",
         "fba8104968df003a261e1f38921768503bf35746ad884bc7a249e0596bd15377",
         {"hit_except": True, "hit_finally": True}, "NameError:___assertTrue"),
        (f"{prefix}/try-except-else-finally.py",
         "a236fe94cf7db0c0ab1b4ccb01c37443e0c3a9dcb31592273b3ee4ccdd1cadbb",
         {"hit_except": True, "hit_else": False, "hit_finally": True}, "NameError:___assertTrue"),
        ("tests/python/programs/original/k-python/programs/testtry2.py",
         "b7eddf22b16dfcdd871f796fc727c2b0ab655977bdeff03972dd813b07bec0ea",
         {"y": 7}, "NameError:x"),
    )
    checked = []
    for path, digest, reached, completion in table:
        source = SUITE["pinned_source"](checkout, path, digest)
        raw = (checkout / path).read_bytes()
        assert source.encode() == raw and execute(raw, reached) == completion
        checked.append((source, "#guard (checkedCase pythonSource).isNone"))
    return checked


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--upstream", type=Path, required=True)
    args = parser.parse_args()
    assert sys.version_info[:3] == (3, 13, 5), sys.version
    revision = subprocess.check_output(["git", "-C", str(args.upstream), "rev-parse", "HEAD"], text=True).strip()
    assert revision == SUITE["UPSTREAM_REVISION"], revision
    tested = fixtures(args.upstream)
    rejected = historical_boundaries(args.upstream)
    with tempfile.TemporaryDirectory() as scratch:
        source = Path(scratch) / "Fixture.py"
        INTAKE["check_lean_batch"](source, source.with_suffix(".lean"), tested + rejected, LEAN, extra_imports=IMPORTS)
    print(json.dumps({"cpython": "3.13.5", "reached_controls": len(tested), "historical_boundaries": len(rejected)}))

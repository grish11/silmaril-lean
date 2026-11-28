# SPDX-License-Identifier: MIT
"""Compare the checked literal keyword-only default profile with CPython."""

from contextlib import redirect_stderr, redirect_stdout
from io import StringIO
from pathlib import Path
import runpy
import sys
import tempfile
from types import CodeType


IMPORTS = (
    "import Batteries.Data.Except",
    "import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Thms",
    "import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.Thms",
    "meta import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.Defs",
    "meta import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Defs",
    "meta import Silmaril.Languages.Python.Core.Module.Functions.Defs",
    "meta import Silmaril.Languages.Python.Core.Module.SeededCall.Defs",
    "meta import Silmaril.Languages.Python.Core.Closure.Defs",
    "meta import Silmaril.Languages.Python.Core.Closure.Executor.Defs",
)

LEAN = """
open Silmaril.Languages.Python
open Compile.ModuleEntry.Functions.Run
open Core.Module.SeededCall

private def initialHeap : Core.Closure.Heap :=
  ⟨1, fun address => if address = 0 then some (.int 37) else none⟩

private def heapRetained (heap : Core.Closure.Heap) : Bool :=
  match heap.lookup ⟨0⟩ with
  | some (some (.int 37)) => heap.next == 1
  | _ => false

private def savedDefault (entry : Compile.Closure.Run.ExecutorEntry) : Option Int := do
  unless entry.definition.parameters.slots.isEmpty && entry.definition.varnames.isNone &&
      entry.definition.cellvars.isNone && entry.definition.freevars.isNone &&
      entry.definition.codeNames.isNone do none
  let .store (.local slot) (.literal (.int value))
    (.assert (.eqInt (.slot (.local tested)) _) (.ret (.literal .none))) := entry.definition.body | none
  if slot == tested then some value else none

private def ordinaryInt : Option Core.Closure.Value → Option Int
  | some (.int value) => some value
  | _ => none

private def ordinaryFunction : Option Core.Closure.Value → Option Nat
  | some (.function function) => some function.code.key
  | _ => none

private def checks (source : Source.Module) (defaults : List Int) (entries : List Nat)
    (completion : Completion) (after : Option Int)
    (seededCompletion : Except Seeded.ModuleFailure Unit) (receipts : List (String × Result)) : Bool := Id.run do
  let .ok compiled := compile source | return false
  let initial := Core.Module.Functions.Session.mk (fun _ => none) initialHeap
  let (events, .finished result status) := runPrefix compiled.table 128 (.ready initial compiled.instructions)
    | return false
  let entered := events.filterMap fun
    | .enter (.function function) => some function.code.key
    | _ => none
  let expectedKey := defaults.length - 1
  let aliasKey := if defaults.length == 2 then some 0 else none
  return compiled.entries.map savedDefault == defaults.map some &&
    status == completion && entered == entries && heapRetained result.heap &&
    ordinaryInt (result.globals "kept") == some 7 && ordinaryInt (result.globals "after") == after &&
    ordinaryFunction (result.globals "probe") == some expectedKey &&
    ordinaryFunction (result.globals "alias") == aliasKey &&
    [Namespace.empty, Seeded.legacySeed .builtin, Seeded.legacySeed .preamble].all (fun space => Id.run do
      let seeded := Seeded.run space compiled initialHeap
      let some (.function function) := seeded.residual.lookupGlobal "probe" | return false
      let expected := space.bindGlobal "kept" (.int 7)
      let (savedKey, expected) := match seeded.residual.lookupGlobal "alias" with
        | some (.function original) =>
          (some original.code.key, (expected.bindGlobal "probe" (.function original)).bindGlobal "alias" (.function original))
        | _ => (none, expected)
      let expected := expected.bindGlobal "probe" (.function function)
      let expected := after.elim expected fun value => expected.bindGlobal "after" (.int value)
      return seeded.completion == seededCompletion && heapRetained seeded.heap &&
        seeded.residual.moduleGlobals == expected.moduleGlobals && seeded.residual.builtins == expected.builtins &&
        function.code.key == expectedKey && savedKey == aliasKey &&
        seeded.calls.map (fun call => (call.callee, call.observation.result)) == receipts &&
        seeded.calls.all (fun call => call.observation.caught.isNone))
"""

REBOUND = """kept = 7
def probe(*, value=4):
    assert value == 4
alias = probe
def probe(*, value=9):
    assert value == 9
probe()
alias()
after = 8
"""
FAILURE = """kept = 7
def probe(*, value=3):
    assert value == 4
probe()
after = 8
"""
POSITIONAL = """kept = 7
def probe(*, value=4):
    assert value == 4
probe(4)
after = 8
"""
EXPLICIT_KEYWORD = """def probe(*, value=3):
    assert value == 4
probe(value=4)
"""


def reference(source, placement):
    helpers = {"___assertEqual": lambda left, right: left == right,
               "___assertRaises": lambda *_: None}
    builtins = {} if placement == "empty" else {"AssertionError": AssertionError}
    if placement == "builtin":
        builtins.update(helpers)
    namespace = {"__builtins__": builtins}
    if placement == "preamble":
        namespace.update(helpers)
    initial = dict(namespace)
    unit = compile(source, "<keyword default>", "exec", dont_inherit=True, optimize=0)
    codes = {item for item in unit.co_consts if isinstance(item, CodeType)}
    entered = []

    def trace(frame, event, argument):
        if event == "call" and frame.f_code in codes:
            entered.append(frame.f_locals["value"])
        return trace

    completion = "normal"
    with redirect_stdout(StringIO()) as stdout, redirect_stderr(StringIO()) as stderr:
        sys.settrace(trace)
        try:
            exec(unit, namespace)
        except (AssertionError, TypeError) as error:
            completion = type(error).__name__
        finally:
            sys.settrace(None)
    assert stdout.getvalue() == stderr.getvalue() == ""
    assert all(namespace[name] is value for name, value in initial.items())
    assert namespace["probe"].__defaults__ is None
    assert list(namespace["probe"].__kwdefaults__) == ["value"]
    defaults = [namespace[name].__kwdefaults__["value"] for name in ("alias", "probe") if name in namespace]
    return completion, entered, defaults, namespace.get("kept"), namespace.get("after")


if __name__ == "__main__":
    shared = runpy.run_path(str(Path(__file__).resolve().parent.parent / "source-scope/check_intake.py"))
    fixtures = (
        (REBOUND, ("normal", [9, 4], [4, 9], 7, 8),
         '#guard checks pythonSource [4, 9] [1, 0] .normal (some 8) (.ok ()) '
         '[("probe", .ok .none), ("alias", .ok .none)]'),
        (FAILURE, ("AssertionError", [3], [3], 7, None),
         '#guard checks pythonSource [3] [0] (.raised .assertionError) none '
         '(.error (.raised (.assertionError .empty))) [("probe", .error (.raised (.assertionError .empty)))]'),
        (POSITIONAL, ("TypeError", [], [4], 7, None),
         '#guard checks pythonSource [4] [] (.raised (.positionalArity 0 1)) none '
         '(.error .unsupported) [("probe", .error .unsupported)]'),
    )
    with tempfile.TemporaryDirectory() as directory:
        src, lean = Path(directory) / "Example.py", Path(directory) / "Example.lean"
        checks = []
        for source, expected, guard in fixtures:
            for placement in ("empty", "builtin", "preamble"):
                assert reference(source, placement) == expected
            checks.append((source, guard))
        for placement in ("empty", "builtin", "preamble"):
            assert reference(EXPLICIT_KEYWORD, placement) == ("normal", [4], [3], None, None)
        for source, diagnostic in (
            (EXPLICIT_KEYWORD, ".argumentProfile"),
            (EXPLICIT_KEYWORD.replace('probe(value=4)', 'probe(**{"value": 4})'), ".argumentProfile"),
            ("def probe(*, value=1 + 2): assert value == 3\n", ".functionBody .parameterProfile"),
            ("def probe(*, value=3): return value\n", ".functionBody .parameterProfile"),
            ("def probe(*, value=3, other=4): assert value == 3\n", ".functionBody .parameterProfile"),
            ("def probe(*, value: int=3): assert value == 3\n", ".functionBody .parameterProfile"),
        ):
            guard = f"""
#guard (match compile pythonSource with | .error (.source ({diagnostic})) => true | _ => false)
"""
            checks.append((source, guard))
        shared["check_lean_batch"](src, lean, checks, LEAN, extra_imports=IMPORTS)
    print(f"CPython {sys.version.split()[0]} and Lean checked omitted keyword-only literal defaults.")

# SPDX-License-Identifier: MIT
"""Check the Python AST emitter, source scope and supported compiler profiles."""

import argparse
import functools
import inspect
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path
from types import CodeType


ROOT = Path(__file__).resolve().parents[4]
EMITTER = ROOT / "tools/python-source/source_ast.py"
LAKE = os.environ.get("LAKE", "lake")

# The snapshot goes through a file so nothing Lake prints can corrupt it.
LAKE_ENVIRONMENT = ("import json, os, pathlib, sys; "
                    "pathlib.Path(sys.argv[1]).write_text(json.dumps(dict(os.environ)))")


@functools.cache
def lake_environment():
    """Return the environment Lake gives its children, entering Lake once per driver."""
    with tempfile.TemporaryDirectory() as tmp:
        snapshot = Path(tmp) / "environment.json"
        subprocess.run([LAKE, "env", sys.executable, "-I", "-S", "-c", LAKE_ENVIRONMENT, str(snapshot)],
                       cwd=ROOT, check=True)
        return json.loads(snapshot.read_text())


def emit(source, destination, text, *, check=True):
    source.write_text(text, encoding="utf-8")
    return subprocess.run(
        [sys.executable, "-I", str(EMITTER), str(source), "--output", str(destination)],
        check=check,
        capture_output=True,
        text=True,
    )


def check_lean(destination, regression, *, extra_imports=(), capture_output=False):
    original = destination.read_text(encoding="utf-8")
    syntax = "Silmaril.Languages.Python.Source.Syntax.Defs"
    scope = "Silmaril.Languages.Python.Source.Scope.Defs"
    imports = "\n".join([f"public import {syntax}", f"import {scope}",
                         f"meta import {syntax}", f"meta import {scope}", *extra_imports])
    destination.write_text(
        original.replace(f"public import {syntax}", imports, 1) + "\n" + regression,
        encoding="utf-8",
    )
    result = subprocess.run(
        ["lean", "-DautoImplicit=false", "-DwarningAsError=true", str(destination)],
        cwd=ROOT,
        env=lake_environment(),
        capture_output=capture_output,
        text=True,
    )
    if capture_output and result.returncode:
        sys.stderr.write(result.stdout + result.stderr)
    result.check_returncode()
    return result


def check_lean_batch(source_path, destination, fixtures, regression, *, extra_imports=()):
    """Check each emitted fixture in its own namespace in one Lean process."""
    header = None
    cases = []
    for index, (source, guard) in enumerate(fixtures):
        emit(source_path, destination, source)
        prefix, declaration, body = destination.read_text(encoding="utf-8").partition("public def pythonSource")
        assert declaration and (header is None or header == prefix)
        header = prefix
        namespace = f"Fixture{index}"
        cases.append(f"namespace {namespace}\n{declaration}{body}\n{guard}\nend {namespace}\n")
    assert header is not None
    destination.write_text(header + regression + "\n" + "\n".join(cases), encoding="utf-8")
    check_lean(destination, "", extra_imports=extra_imports)


def check_scope_intake():
    with tempfile.TemporaryDirectory() as tmp:
        source = Path(tmp) / "Example.py"
        destination = Path(tmp) / "Example.lean"
        emit(source, destination, r'''
from pkg import thing as alias

def outer(seed):
    λ = "\ud800"
    rate = 1.0
    count = 5
    class C(*bases, metaclass=Meta):
        def method(self, *, key: Type = alias):
            return lambda: key
    return C
''')
        generated = destination.read_text(encoding="utf-8")
        assert ".text [55296]" in generated, generated
        assert ".floatDecimal 0xa (-0x1)" in generated, generated
        assert '.name "λ"' in generated, generated
        check_lean(destination, """
#guard ((analyze pythonSource).toOption.map (·.scope.access "alias")) == some (some .moduleName)
#guard ((analyze pythonSource).toOption.bind (·.atPath [0])).bind (·.access "Meta") ==
  some .implicitGlobal
#guard ((analyze pythonSource).toOption.bind (·.atPath [0])).bind (·.access "bases") ==
  some .implicitGlobal
#guard ((analyze pythonSource).toOption.bind (·.atPath [0])).bind (·.access "λ") ==
  some .local
#guard ((analyze pythonSource).toOption.bind (·.atPath [0, 0, 0, 0])).bind (·.access "key") ==
  some (.free [0, 0, 0])
""", extra_imports=("import Batteries.Tactic.Alias",))
        yields = """
def outer():
    def suspended():
        if False:
            yield 1
    return lambda: (yield 2)

def defaulted():
    def nested(value=(yield 3)):
        return value
    return nested
"""
        expected = {
            "outer": False, "suspended": True, "<lambda>": True,
            "defaulted": True, "nested": False,
        }

        def generators(code):
            result = {code.co_name: bool(code.co_flags & inspect.CO_GENERATOR)}
            for constant in code.co_consts:
                if isinstance(constant, CodeType):
                    result.update(generators(constant))
            return result

        assert generators(compile(yields, "<scope fixture>", "exec")) == {"<module>": False, **expected}
        emit(source, destination, yields)
        paths = {"outer": [0], "suspended": [0, 0], "<lambda>": [0, 1],
                 "defaulted": [1], "nested": [1, 0]}
        observations = [
            f"#guard hasYield {paths[name]} == some {str(value).lower()}"
            for name, value in expected.items()
        ]
        check_lean(destination, """
private def hasYield (path : BlockPath) : Option Bool :=
  ((analyze pythonSource).toOption.bind (·.atPath path)).map (·.context.containsYield)
#guard hasYield [] == some false
""" + "\n".join(observations))
        emit(source, destination, "[item for item in entries]\n")
        check_lean(destination, """
#guard (match analyze pythonSource with
  | .error diagnostic => diagnostic.error == .unsupportedExpression .listComprehension
  | .ok _ => false)
""")
        destination.unlink()
        rejected = emit(source, destination, "with resource: pass\n", check=False)
        assert rejected.returncode == 1 and "unsupported With" in rejected.stderr, rejected
        assert not destination.exists()


# Original MIT-licensed fixtures. Run only the successful intersection on CPython.
CLOSED_FIXTURES = (
    ("zero", "def answer(): return 0\n", "return 0"),
    ("literal", "def answer(): return 41\n", "return 41"),
    ("sum", "def answer(): return 1 + 2\n", "return 3"),
    ("right_nesting", "def answer(): return 1 + (2 + 3)\n", "return 6"),
    ("two_subtrees", "def answer(): return (1 + 2) + (3 + 4)\n", "return 10"),
    ("large_integer", "def answer(): return 18446744073709551616 + 7\n", "return 18446744073709551623"),
    ("module_nonlocal", "nonlocal missing\n", "scope nonlocalInModule"),
    ("takes_argument", "def answer(value): return value\n", "moduleShape"),
    ("dynamic_call", "def answer(): return helper()\n", "expressionShape"),
    ("floor_division", "def answer(): return 7 // 0\n", "expressionShape"),
)

CLOSED_OBSERVATION = """
open Silmaril.Languages.Python

private def observation (source : Module) : String :=
  match Compile.Closed.compile source with
  | .error (.scope ⟨_, .nonlocalInModule _⟩) => "scope nonlocalInModule"
  | .error (.scope _) => "scope other"
  | .error .moduleShape => "moduleShape"
  | .error .expressionShape => "expressionShape"
  | .ok body =>
    match Core.run .addition body body.start.budget with
    | some (.stop (.finished (.ok value)) (.observed (.returned (.ok observed)))) =>
      if value == observed then s!"return {value}" else "mismatched return observation"
    | _ => "unexpected runner result"
"""


def check_closed_compiler():
    with tempfile.TemporaryDirectory() as tmp:
        directory = Path(tmp)
        destination = directory / "Conformance.lean"
        programs = []
        observations = []
        for name, source, expected in CLOSED_FIXTURES:
            path = directory / (name + ".py")
            emit(path, destination, source)
            prelude, marker, term = destination.read_text(encoding="utf-8").partition(
                "public def pythonSource : Module :="
            )
            assert marker, "Missing source AST declaration"
            programs.append(f"private def {name} : Module :={term}")
            observations.append(f'#eval IO.println ("fixture {name} " ++ observation {name})')
            if expected.startswith("return "):
                reference = subprocess.run(
                    [sys.executable, "-I", "-c",
                     "import runpy, sys; print(runpy.run_path(sys.argv[1])['answer']())", str(path)],
                    check=True, capture_output=True, text=True, timeout=10,
                )
                assert "return " + reference.stdout.strip() == expected, (name, reference.stdout)
        destination.write_text(prelude + "\n".join(programs), encoding="utf-8")
        result = check_lean(destination, CLOSED_OBSERVATION + "\n".join(observations) + "\n",
                            extra_imports=(
                                "import Silmaril.Languages.Python.Compile.Closed.Thms",
                                "meta import Silmaril.Languages.Python.Compile.Closed.Defs",
                                "meta import Silmaril.Languages.Python.Core.Thms",
                            ), capture_output=True)
        expected = [f"fixture {name} {observation}" for name, _, observation in CLOSED_FIXTURES]
        actual = [line for line in result.stdout.splitlines() if line.startswith("fixture ")]
        assert actual == expected, {"actual": actual, "expected": expected}
        executed = sum(observation.startswith("return ") for _, _, observation in CLOSED_FIXTURES)
        print(json.dumps({
            "profile": "closed source addition",
            "cpython": sys.version.split()[0],
            "executed_on_both": executed,
            "checked_rejections": len(CLOSED_FIXTURES) - executed,
            "observations": actual,
        }))


def check_closure_bodies():
    body_header = "Silmaril.Languages.Python.Compile.Closure.Body.Defs"
    core_header = "Silmaril.Languages.Python.Core.Closure.Defs"
    imports = (f"import {body_header}", f"meta import {body_header}", f"meta import {core_header}")
    with tempfile.TemporaryDirectory() as tmp:
        source = Path(tmp) / "Example.py"
        destination = Path(tmp) / "Example.lean"
        fixtures = [("""
def outer(seed):
    offset = 2
    def middle(increment):
        def inner(value):
            nonlocal seed
            seed = seed + value
            return seed + offset
        return inner(increment)
    return middle(3)
""", """

private def captureSlots {parent child : Silmaril.Languages.Python.Core.Closure.Layout}
    (operands : Fin child.captures → Silmaril.Languages.Python.Core.Closure.CaptureSlot parent) :
    List (Bool × Nat) :=
  (List.finRange child.captures).map fun index => match operands index with
    | .owned slot => (true, slot.val)
    | .forwarded slot => (false, slot.val)

private def shape : Bool :=
  match compile pythonSource with
  | .ok compiled =>
    match compiled.code with
    | .assign (.owned offset) (.integer 2)
        (.closure (.local middle) [0, 0] _ middleParams middleCaptures
          (.closure (.local inner) [0, 0, 0] _ innerParams innerCaptures
            (.assign (.capture written) (.add (.read (.capture seed)) (.read (.local value)))
              (.ret (.add (.read (.capture result)) (.read (.capture added)))))
            (.ret (.call (.read (.local calledInner)) [.read (.local increment)])))
          (.ret (.call (.read (.local calledMiddle)) [.integer 3]))) =>
      middle.val == calledMiddle.val && inner.val == calledInner.val &&
      written.val == seed.val && seed.val == result.val && seed.val == 0 && added.val == 1 &&
      (match compiled.parameters.slots, middleParams.slots, innerParams.slots with
       | [.owned initial], [.local argument], [.local payload] =>
         argument.val == increment.val && payload.val == value.val &&
         captureSlots middleCaptures == [(true, initial.val), (true, offset.val)] &&
         captureSlots innerCaptures == [(false, 0), (false, 1)]
       | _, _, _ => false)
    | _ => false
  | .error _ => false

#guard shape
""")]
        fixtures.append(("""
def outer():
    def first():
        def inside():
            return 1
        return inside()
    def second():
        return 2
    return first() + second()
""", """
#guard ((compile pythonSource).toOption.map Compiled.paths) ==
  some [[0], [0, 0], [0, 0, 0], [0, 1]]
"""))
        fixtures.append(("def outer(value=1): return value\n", """
#guard (match compile pythonSource with | .error .parameterProfile => true | _ => false)
"""))
        fixtures.append(("def outer(fn): return fn(keyword=1)\n", """
#guard (match compile pythonSource with | .error .argumentProfile => true | _ => false)
"""))
        generator_cases = (
            ("def outer():\n    if False: yield 1\n    return 2\n", [0]),
            ("def outer():\n    def child():\n        yield 1\n    return 2\n", [0, 0]),
            ("def outer():\n    def child(value=0): yield value\n    return 2\n", [0, 0]),
            ("def outer():\n    def child(value=(yield 1)): return value\n    return 2\n", [0]),
        )
        for text, rejected_path in generator_cases:
            fixtures.append((text, f"""
#guard (match compile pythonSource with
  | .error (.unsupportedGenerator path) => path == {rejected_path}
  | _ => false)
"""))
        fixtures.append(("def outer(value=0): yield value\n", """
#guard (match compile pythonSource with | .error .parameterProfile => true | _ => false)
"""))
        check_lean_batch(source, destination, fixtures, f"open {body_header.removesuffix('.Defs')}\n",
                         extra_imports=imports)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    profiles = parser.add_mutually_exclusive_group()
    profiles.add_argument("--closed-compiler", action="store_true")
    profiles.add_argument("--closure-bodies", action="store_true")
    args = parser.parse_args()
    if args.closed_compiler:
        check_closed_compiler()
    elif args.closure_bodies:
        check_closure_bodies()
    else:
        check_scope_intake()

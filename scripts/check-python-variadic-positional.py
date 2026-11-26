# SPDX-License-Identifier: MIT
"""Check the ordered positional preparation and scalar variadic binder against CPython 3.13.5."""

import subprocess
import sys
import tempfile
from pathlib import Path


def exec_source(source, namespace):
    exec(compile(source, "<variadic positional>", "exec", dont_inherit=True, optimize=0), namespace)


def check_evaluation_order():
    state = {"trace": [], "cell": 37}
    source = '''
def selected(value, *rest):
    return ("original", value, rest)

def replacement(value, *rest):
    return ("replacement", value, rest)

def first():
    global selected
    trace.append("first")
    selected = replacement
    state["cell"] = 41
    return False

def spread():
    trace.append("spread")
    state["cell"] = 42
    return (3, None)

def after():
    trace.append("after")
    return 8

answer = selected(first(), *spread(), after())
'''
    scope = {"trace": state["trace"], "state": state}
    exec_source(source, scope)
    assert scope["answer"] == ("original", False, (3, None, 8))
    assert type(scope["answer"][1]) is bool
    assert scope["selected"] is scope["replacement"]
    assert state == {"trace": ["first", "spread", "after"], "cell": 42}

    def fixed(value):
        return value

    def bad():
        state["cell"] = 43
        return 11

    def missing():
        state["cell"] = 44
        return first_missing

    cases = (
        ("fixed(*bad(), missing())", TypeError, None, 43),
        ("fixed(*(), missing())", NameError, "first_missing", 44),
        ("fixed(*(1, 2, 3), missing())", NameError, "first_missing", 44),
        ("absent(*bad())", NameError, "absent", 37),
        ("fixed(*())", TypeError, None, 37),
        ("noncallable(*(1,), missing())", NameError, "first_missing", 44),
    )
    for source, kind, name, cell in cases:
        state["cell"] = 37
        try:
            exec_source(source, dict(fixed=fixed, bad=bad, missing=missing, noncallable=None))
        except (NameError, TypeError) as error:
            assert type(error) is kind and getattr(error, "name", None) == name
            if source == "fixed(*bad(), missing())":
                assert "iterable" in str(error)
        else:
            raise AssertionError(source)
        assert state["cell"] == cell


def lean_value(value):
    if value is None:
        return ".none"
    if type(value) is bool:
        return ".bool " + ("true" if value else "false")
    assert type(value) is int
    return f".int ({value})"


def lean_list(values):
    return "[" + ", ".join(map(lean_value, values)) + "]"


def binder_matrix():
    lines = [
        "import Silmaril.Languages.Python.Core.Closure.Call.Variadic.Thms",
        "open Silmaril.Languages.Python.Core.Closure",
        "open Silmaril.Languages.Python.Core.Closure.Call",
    ]
    checked = 0
    for fixed in range(5):
        fixed_names = [f"v{i}" for i in range(fixed)]
        slots = ", ".join(f".local ⟨{i}, by decide⟩" for i in range(fixed))
        lines += [
            f"def layout{fixed} : Layout := ⟨{fixed + 1}, 0, 0⟩",
            f"def signature{fixed} : VariadicParameters layout{fixed} :=",
            f"  ⟨⟨[{slots}], by decide⟩, .local ⟨{fixed}, by decide⟩, by decide⟩",
        ]
        namespace = {}
        signature = ", ".join([*fixed_names, "*tail"])
        result = ", ".join([*fixed_names, "tail"])
        exec_source(f"def collect({signature}):\n    return ({result},)\n", namespace)
        for actual in range(8):
            supplied = [None, 17, True, -23, False, 37, None][:actual]
            call = namespace["collect"]
            arguments = lean_list(supplied)
            try:
                values = call(*supplied)
            except TypeError:
                assert actual < fixed
                expected = f".error (.defined (.positionalArity {fixed} {actual}))"
            else:
                prefix, tail = values[:-1], values[-1]
                assert type(tail) is tuple
                assert len(prefix) == fixed and len(prefix) + len(tail) == actual
                pack = ", ".join([*map(lean_value, prefix), f".tuple {lean_list(tail)}"])
                expected = f".ok [{pack}]"
            lines.append(f"example : signature{fixed}.complete {arguments} = {expected} := rfl")
            checked += 1
    with tempfile.TemporaryDirectory() as directory:
        path = Path(directory) / "VariadicMatrix.lean"
        path.write_text("\n".join(lines) + "\n")
        subprocess.run(["lake", "env", "lean", "-DwarningAsError=true", str(path)], check=True)
    return checked


if __name__ == "__main__":
    assert sys.version_info[:3] == (3, 13, 5)
    check_evaluation_order()
    assert (lambda *items: items)(*[0, 1, 2]) == (0, 1, 2)
    assert (lambda *items: items)(*"abc") == ("a", "b", "c")
    assert (lambda *items: items)(*range(3)) == (0, 1, 2)
    checked = binder_matrix()
    print(f"CPython 3.13.5 agrees with {checked} variadic binding cases. Evaluation-order controls passed.")

"""Compare public module fixtures with ordinary, unoptimized CPython execution."""

import os
import platform
from pathlib import Path
import subprocess


FIXTURES = {
    "normal": "x = seed + True + 1\nflag = x == 42\nassert flag\n",
    "assertion": "x = 42\nassert 0\nx = 0\nlater = 1\n",
    "missing": "x = seed\nx = missing + (1 // 0)\n",
    "division": "assert 1 // 0\n",
}
NAMES = ["seed", "keep", "x", "flag", "later"]


def render_binding(namespace, name):
    if name not in namespace:
        return "absent"
    value = namespace[name]
    if type(value) is bool:
        return "bool:" + str(value).lower()
    if type(value) is int:
        return "int:" + str(value)
    raise TypeError(f"unexpected binding for {name}: {value!r}")


def cpython(name, source):
    namespace = {"__builtins__": {}, "seed": 40, "keep": True}
    completion = "normal"
    try:
        exec(compile(source, f"<{name}>", "exec", optimize=0), namespace)
    except (AssertionError, NameError, ZeroDivisionError) as error:
        completion = type(error).__name__
        if isinstance(error, NameError):
            completion += ":" + str(error.name)
    return [completion, *(render_binding(namespace, key) for key in NAMES)]


def main():
    if platform.python_implementation() != "CPython":
        raise SystemExit("these fixtures use a CPython oracle")
    root = Path(__file__).resolve().parents[4]
    fixture = Path(__file__).with_name("Regression.lean").resolve()
    output = subprocess.check_output(
        [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
         "-DwarningAsError=true", "--run", str(fixture)],
        cwd=root,
        text=True,
    )
    actual = {}
    for line in output.splitlines():
        if line.startswith("module-entry\t"):
            _, name, *values = line.split("\t")
            if name in actual:
                raise SystemExit(f"duplicate Lean fixture {name}")
            actual[name] = values
    expected = {name: cpython(name, source) for name, source in FIXTURES.items()}
    if actual != expected:
        raise SystemExit(f"module observations differ\nCPython: {expected!r}\nLean: {actual!r}")
    print(f"CPython {platform.python_version()} and Lean agree on {len(expected)} module fixtures")


if __name__ == "__main__":
    main()

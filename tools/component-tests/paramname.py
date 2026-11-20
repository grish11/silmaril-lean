"""Run the pinned tools on paramname.wasm (`f: func(y: u32)`) against hosts whose `f` has another
parameter name (evidence for docs/projects/component-tests.md, not a proof; not run in CI).

    python3 -I tools/component-tests/paramname.py    # writes examples/component-tests/paramname.json

Three ways of supplying the root import `f`:
* a host *component* (tools/component-tests/host.wat, `f: func(x: u32)`, and the same with the
  parameter named `y`) wired by the pinned wac 0.12.0 (`wac compose`), then `wasmtime run`;
* the same host component and the test binary nested in one outer component that instantiates
  the binary `(with "f" (func $hf))`: `wasm-tools validate` and `wasmtime run` (wasmparser's
  component type check of `instantiate` arguments);
* a wasmtime 50.0.0 `Linker` host function (`func_wrap`, typed `(u32,) -> ()` by its Rust
  parameter types; tools/component-tests/linker-host, built with `cargo build --release --locked`).
Every tool binary is SHA-256 checked against the pins, as in oracle.py.
"""
import hashlib
import json
import os
import pathlib
import re
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[2]
DIR = ROOT / "examples" / "component-tests"
LH = ROOT / "tools" / "component-tests" / "linker-host"


def pins(path):
    env = {"HOME": os.environ["HOME"]}
    for line in path.read_text().splitlines():
        m = re.match(r"^([A-Z_0-9]+)=(.*)$", line)
        if not m:
            continue
        v = m.group(2)
        v = re.sub(r"\$\{([A-Z_0-9]+):-([^}]*)\}", lambda g: os.environ.get(g.group(1), g.group(2)), v)
        v = re.sub(r"\$\{?([A-Z_0-9]+)\}?", lambda g: env.get(g.group(1), ""), v)
        env[m.group(1)] = v
    return env


def sha256(p):
    return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()


def check(path, want, name):
    if not pathlib.Path(path).is_file() or sha256(path) != want:
        sys.exit(f"paramname: {name} missing or not the pinned build at {path}")


def run(cmd, tmp):
    r = subprocess.run([str(c) for c in cmd], capture_output=True, text=True, timeout=600)

    def rel(c):
        return str(c).replace(str(tmp), "$TMP").replace(str(ROOT) + "/", "")

    return {"argv": [pathlib.Path(cmd[0]).name] + [rel(c) for c in cmd[1:]], "exit": r.returncode,
            "stdout": rel(r.stdout.strip()),
            "stderr": [rel(l).strip() for l in r.stderr.strip().splitlines() if l.strip()]}


def strip_comments(wat):
    return "\n".join(l for l in wat.splitlines() if not l.lstrip().startswith(";;"))


def main():
    wt = pins(ROOT / "tools" / "wasm-tools" / "tests" / "pins.sh")
    jco = pins(ROOT / "tools" / "wasm-jco" / "tests" / "pins.sh")
    WT, WASMTIME, WAC = wt["WT_UPSTREAM"], jco["WASMTIME"], jco["WAC"]
    check(WT, wt["WT_UPSTREAM_SHA256"], "wasm-tools")
    check(WASMTIME, jco["WASMTIME_SHA256"], "wasmtime")
    check(WAC, jco["WAC_SHA256"], "wac")
    subprocess.run(["cargo", "build", "--release", "--locked", "--quiet"], cwd=LH, check=True)
    lock = (LH / "Cargo.lock").read_text()
    wasmtime_crate = re.search(r'name = "wasmtime"\nversion = "([^"]+)"', lock).group(1)
    out = {"schema": "silmaril.component-tests.paramname.v1",
           "note": "evidence for the parameter-name counterexample; not a proof, not run in CI",
           "tools": {"wasm-tools": wt["WT_VERSION"], "wasmtime": jco["WASMTIME_VERSION"],
                     "wac": jco["WAC_VERSION"], "linker-host wasmtime crate": wasmtime_crate},
           "binaries": {n: {"path": f"examples/component-tests/{n}.wasm", "sha256": sha256(DIR / f"{n}.wasm")}
                        for n in ["starts", "paramname"]}}
    with tempfile.TemporaryDirectory() as tmp:
        tmp = pathlib.Path(tmp)
        for n in ["starts", "paramname"]:
            b = DIR / f"{n}.wasm"
            out["binaries"][n]["validate"] = run([WT, "validate", b], tmp)
            out["binaries"][n]["wit"] = run([WT, "component", "wit", b], tmp)
        host_wat = strip_comments((ROOT / "tools/component-tests/host.wat").read_text())
        hosts = {"x": host_wat, "y": host_wat.replace('(param "x" u32)', '(param "y" u32)')}
        for h, src in hosts.items():
            (tmp / f"host{h}.wat").write_text(src)
            subprocess.run([WT, "parse", tmp / f"host{h}.wat", "-o", tmp / f"host{h}.wasm"], check=True)
        out["wac"], out["nested"], out["linker_host"] = {}, {}, {}
        for h in hosts:
            for n in ["starts", "paramname"]:
                key = f"host f: func({h}: u32), {n}.wasm"
                wac = tmp / "t.wac"
                wac.write_text("package oracle:t;\nlet h = new host:log {};\nlet s = new test:b { f: h.f };\n"
                               "export s.get;\nexport h.trace;\nexport h.calls;\n")
                comp = tmp / f"c_{h}_{n}.wasm"
                e = {"compose": run([WAC, "compose", wac, "--dep", f"host:log={tmp / f'host{h}.wasm'}",
                                     "--dep", f"test:b={DIR / f'{n}.wasm'}", "-o", comp], tmp)}
                if e["compose"]["exit"] == 0:
                    e["invocations"] = {i: run([WASMTIME, "run", "--invoke", i, comp], tmp)
                                        for i in ["get()", "trace()", "calls()"]}
                out["wac"][key] = e
                inner = strip_comments((DIR / f"{n}.wat").read_text()).replace("(component", "(component $P", 1)
                nest = tmp / f"nest_{h}_{n}.wat"
                nest.write_text("(component\n" + hosts[h].replace("(component", "(component $H", 1) + "\n" + inner +
                                '\n  (instance $h (instantiate $H))\n  (alias export $h "f" (func $hf))\n'
                                '  (instance $p (instantiate $P (with "f" (func $hf))))\n'
                                '  (alias export $p "get" (func $g))\n  (export "get" (func $g)))\n')
                subprocess.run([WT, "parse", nest, "-o", tmp / f"nest_{h}_{n}.wasm"], check=True)
                out["nested"][key] = {"validate": run([WT, "validate", tmp / f"nest_{h}_{n}.wasm"], tmp),
                                      "run": run([WASMTIME, "run", "--invoke", "get()", tmp / f"nest_{h}_{n}.wasm"], tmp)}
        for n in ["starts", "paramname"]:
            out["linker_host"][f"func_wrap f: (u32,) -> (), {n}.wasm"] = run(
                [LH / "target" / "release" / "linker-host", DIR / f"{n}.wasm"], tmp)
    (DIR / "paramname.json").write_text(json.dumps(out, indent=2) + "\n")
    summary = {
        "wac": {k: v["compose"]["exit"] == 0 for k, v in out["wac"].items()},
        "nested_validates": {k: v["validate"]["exit"] == 0 for k, v in out["nested"].items()},
        "linker_host": {k: v["stdout"].splitlines()[-1] if v["exit"] == 0 else "error"
                        for k, v in out["linker_host"].items()},
    }
    print(json.dumps(summary, indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main())

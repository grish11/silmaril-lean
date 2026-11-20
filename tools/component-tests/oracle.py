"""Run the pinned wasmtime 50.0.0 on the component test binaries (an oracle, not a proof).

    python3 -I tools/component-tests/oracle.py          # writes examples/component-tests/oracle.json

wasmtime's CLI cannot supply a host function to a component import, so the host is itself a
component (tools/component-tests/host.wat, assembled with the pinned wasm-tools 1.262.0): its
`f(x)` appends `x` to a trace and counts the calls. The pinned wac 0.12.0 (`wac compose`) wires the
host's `f` into the test binary's import `f` and exports the binary's `get` with the host's `trace`
and `calls`. `wasmtime run --invoke 'get()'` (then 'trace()', 'calls()') instantiates the
composition, which instantiates the host and then the test binary (its start functions run then),
and calls the export. Each invocation is a fresh instantiation. Every tool is SHA-256 checked
against tools/wasm-tools/tests/pins.sh and tools/wasm-jco/tests/pins.sh. Not run in CI.
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


def pins(path):
    """The `NAME=value` assignments of a pins file, with `$VAR`/`${VAR:-d}` expanded."""
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


def tool(path, want, name):
    if not pathlib.Path(path).is_file():
        sys.exit(f"oracle: {name} missing at {path} (tools/wasm-jco/tests/install.sh)")
    got = sha256(path)
    if got != want:
        sys.exit(f"oracle: {name} SHA-256 {got} != pinned {want}")
    return {"path": str(path), "sha256": got}


def run(cmd, tmp):
    r = subprocess.run(cmd, capture_output=True, text=True, timeout=120)

    def rel(c):
        c = str(c)
        return c.replace(str(tmp), "$TMP").replace(str(ROOT) + "/", "")

    return {"argv": [pathlib.Path(cmd[0]).name] + [rel(c) for c in cmd[1:]],
            "exit": r.returncode, "stdout": r.stdout.strip(),
            "stderr": [rel(l).strip() for l in r.stderr.strip().splitlines()]}


def main():
    wt = pins(ROOT / "tools" / "wasm-tools" / "tests" / "pins.sh")
    jco = pins(ROOT / "tools" / "wasm-jco" / "tests" / "pins.sh")
    tools = {
        "wasm-tools": dict(version=wt["WT_VERSION"], **tool(wt["WT_UPSTREAM"], wt["WT_UPSTREAM_SHA256"], "wasm-tools")),
        "wasmtime": dict(version=jco["WASMTIME_VERSION"], **tool(jco["WASMTIME"], jco["WASMTIME_SHA256"], "wasmtime")),
        "wac": dict(version=jco["WAC_VERSION"], **tool(jco["WAC"], jco["WAC_SHA256"], "wac")),
    }
    WT, WASMTIME, WAC = wt["WT_UPSTREAM"], jco["WASMTIME"], jco["WAC"]
    for t in tools.values():
        t.pop("path")
    out = {"schema": "silmaril.component-tests.oracle.v1",
           "note": "wasmtime is an independent oracle for these two binaries only; not a proof, not run in CI",
           "tools": tools, "binaries": {}}
    with tempfile.TemporaryDirectory() as tmp:
        tmp = pathlib.Path(tmp)
        host = tmp / "host.wasm"
        subprocess.run([WT, "parse", ROOT / "tools/component-tests/host.wat", "-o", host], check=True)
        subprocess.run([WT, "validate", host], check=True)
        out["host"] = {"source": "tools/component-tests/host.wat", "sha256": sha256(host),
                       "f": "trace := trace * 10 + x; calls := calls + 1"}
        for name in ["starts", "trap"]:
            b = DIR / f"{name}.wasm"
            wac = tmp / f"{name}.wac"
            wac.write_text(f"package oracle:{name};\nlet h = new host:log {{}};\n"
                           f"let s = new test:{name} {{ f: h.f }};\n"
                           "export s.get;\nexport h.trace;\nexport h.calls;\n")
            comp = tmp / f"{name}.composed.wasm"
            subprocess.run([WAC, "compose", wac, "--dep", f"host:log={host}",
                            "--dep", f"test:{name}={b}", "-o", comp], check=True)
            entry = {"wac": wac.read_text().splitlines(), "binary": f"examples/component-tests/{name}.wasm", "sha256": sha256(b),
                     "composed_sha256": sha256(comp),
                     "embedded_verbatim": b.read_bytes() in comp.read_bytes(),
                     "alone": run([WASMTIME, "run", "--invoke", "get()", b], tmp),
                     "invocations": {}}
            for inv in ["get()", "trace()", "calls()"]:
                entry["invocations"][inv] = run([WASMTIME, "run", "--invoke", inv, comp], tmp)
            out["binaries"][name] = entry
    s, t = out["binaries"]["starts"]["invocations"], out["binaries"]["trap"]["invocations"]
    out["binaries"]["starts"]["observed"] = {
        "instantiates": s["get()"]["exit"] == 0,
        "import_trace": [int(d) for d in s["trace()"]["stdout"]] if s["trace()"]["exit"] == 0 else None,
        "calls": int(s["calls()"]["stdout"]) if s["calls()"]["exit"] == 0 else None,
        "get": int(s["get()"]["stdout"]) if s["get()"]["exit"] == 0 else None}
    out["binaries"]["trap"]["observed"] = {
        "instantiates": any(v["exit"] == 0 for v in t.values()),
        "trap": all(v["exit"] != 0 and any("unreachable" in l for l in v["stderr"])
                    for v in t.values())}
    out["binaries"]["starts"]["expected"] = {"instantiates": True, "import_trace": [1, 2], "calls": 2, "get": 42}
    out["binaries"]["trap"]["expected"] = {"instantiates": False, "trap": True}
    for v in out["binaries"].values():
        v["agrees"] = v["observed"] == v["expected"]
    (DIR / "oracle.json").write_text(json.dumps(out, indent=2) + "\n")
    print(json.dumps({k: v["agrees"] for k, v in out["binaries"].items()}))
    return 0 if all(v["agrees"] for v in out["binaries"].values()) else 1


if __name__ == "__main__":
    sys.exit(main())

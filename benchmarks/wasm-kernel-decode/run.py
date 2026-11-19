#!/usr/bin/env python3
"""Isolated native and kernel measurements on identical Wasm source/module pairs."""

import argparse
import csv
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[2]
BENCH = Path(__file__).resolve().parent
REF = "Silmaril.Wasm.Binary.Core.decode?"
FAST = "Silmaril.Wasm.Perf.CoreDecode.decodeF"
READERS = {"reference": REF, "fast": FAST}
HEADER = b"\0asm\x01\x00\x00\x00"


def uleb(value):
    tail = bytearray()
    while value >= 128:
        tail.append((value & 127) | 128)
        value >>= 7
    return bytes(tail) + bytes([value])


def section(index, payload):
    return bytes([index]) + uleb(len(payload)) + payload


def many_bodies(count):
    return (
        HEADER
        + section(1, b"\x01\x60\x00\x00")
        + section(3, uleb(count) + b"\x00" * count)
        + section(10, uleb(count) + b"\x03\x00\x01\x0b" * count)
    )


def large_data(count):
    payload = hashlib.shake_256(b"silmaril-wasm-kernel-decode-v1").digest(count)
    return HEADER + section(11, b"\x01\x01" + uleb(count) + payload)


def fixtures():
    for case, filename in (
        ("empty-check", "wasm-acceptors/empty_check.wasm"),
        ("ex-start", "wasm-acceptors/ex_start.wasm"),
        ("lrat", "wasm-checkers/lrat.wasm"),
    ):
        yield case, (ROOT / "examples" / filename).read_bytes(), False
    for count in (64, 512, 2048):
        yield f"bodies-{count}", many_bodies(count), False
    for size in (4, 8, 16, 32, 128, 1024):
        yield f"data-{size}k", large_data(size * 1024), True


def sample(directory, label, command, seconds, env):
    timer = directory / f"{label}.time"
    log = directory / f"{label}.log"
    args = ["/usr/bin/time", "-o", str(timer), "-f", "%e,%M",
            "timeout", "-k", "2", str(seconds), *command]
    with log.open("w") as output:
        status = subprocess.run(args, cwd=ROOT, env=env, stdout=output, stderr=output).returncode
    timing = timer.read_text().splitlines()[-1].split(",")
    matches = re.findall(r"(?:agreement_ns |native_ns )(\d+)", log.read_text(errors="replace"))
    return [label, *timing, status, matches[-1] if matches else ""]


def lean_command(args, source, *extra):
    return ["lake", "env", "lean", "-j1", f"-s{args.stack}", f"-M{args.memory}", "-DmaxHeartbeats=0",
            "-DmaxRecDepth=100000", "-DautoImplicit=false", "-E", "warning", *extra, str(source)]


def build_kernel_harness(out, args):
    build = out / "build"
    build.mkdir(exist_ok=True)
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join(part for part in (str(build), env.get("LEAN_PATH")) if part)
    subprocess.run(["lake", "build", "--wfail", "+Silmaril.Wasm.Perf.CoreDecode.Thms",
                    "+Silmaril.Prelude.Bytes.Elab.Defs"], cwd=ROOT, check=True)
    subprocess.run(lean_command(args, BENCH / "Quote.lean", f"--root={BENCH}",
                                "-o", str(build / "Quote.olean")), cwd=ROOT, check=True, env=env)
    return build, env


def kernel_cases(out, selected, args):
    build, env = build_kernel_harness(out, args)
    with (out / "kernel.csv").open("w") as csv_file:
        writer = csv.writer(csv_file)
        writer.writerow(["case", "run", "phase", "wall_s", "peak_rss_kib", "exit", "agreement_ns"])
        for case, binary, data in selected:
            directory = binary.parent
            defs = directory / "Fixture.lean"
            defs.write_text(f'module\nimport Quote\n\nwasm_bench_defs source expected from {json.dumps(binary.name)}\n')
            olean = build / "Fixture.olean"
            query = "data" if data else "funcs"
            source = directory / "Measure.lean"
            for repeat in range(1, args.runs + 1):
                olean.unlink(missing_ok=True)
                result = sample(directory, f"{repeat}-construct",
                                lean_command(args, defs, f"--root={directory}", "-o", str(olean)),
                                args.seconds, env)
                writer.writerow([case, repeat, "construct", *result[1:]])
                csv_file.flush()
                if result[3]:
                    continue
                (directory / f"{repeat}-fixture-olean.bytes").write_text(f"{olean.stat().st_size}\n")
                phases = {
                    "import": "",
                    "query": f"example : expected.{query}.head?.isSome = true := rfl\n",
                    **{name: f"wasm_bench_agreement agrees {reader} source expected\n"
                       for name, reader in READERS.items()},
                }
                for phase, body in phases.items():
                    source.write_text(f"module\nimport Fixture\nimport Quote\n\n{body}")
                    result = sample(directory, f"{repeat}-{phase}", lean_command(args, source),
                                    args.seconds, env)
                    writer.writerow([case, repeat, phase, *result[1:]])
                    csv_file.flush()


def window_cases(out, selected, args):
    build, env = build_kernel_harness(out, args)
    subprocess.run(lean_command(args, BENCH / "Window.lean", f"--root={BENCH}",
                                "-o", str(build / "Window.olean")), cwd=ROOT, check=True, env=env)
    with (out / "window.csv").open("w") as csv_file:
        writer = csv.writer(csv_file)
        writer.writerow(["case", "run", "phase", "wall_s", "peak_rss_kib", "exit", "agreement_ns"])
        for case, binary, data in selected:
            if not data:
                continue
            directory = binary.parent
            width = int(case.removeprefix("data-").removesuffix("k")) * 1024
            offset = binary.stat().st_size - width
            (directory / "payload.bin").write_bytes(binary.read_bytes()[offset:])
            defs = directory / "WindowInput.lean"
            defs.write_text('module\nimport Quote\n\nkbytes_def source from_file "source.wasm"\n'
                            f'kbytes_def payload from_file "payload.bin"\n@[expose] public def offset := {offset}\n')
            olean = build / "WindowInput.olean"
            source = directory / "MeasureWindow.lean"
            statement = ("(Decode.readBytes payload.len).run ⟨source.toByteArray, offset⟩ =\n"
                         "  .ok (payload.toByteArray, ⟨source.toByteArray, offset + payload.len⟩)")
            phases = {
                "length": "wasm_bench_refl lengthMatches : source.toByteArray.size = source.len\n",
                "raw": f"wasm_bench_refl readMatches : {statement}\n",
                "packed": (
                    "wasm_bench_refl packedMatches : checkWindow source offset payload = true\n"
                    f"theorem readMatches : {statement} :=\n"
                    "  checkWindow_sound source payload offset source.wf_true payload.wf_true packedMatches\n"
                ),
            }
            for repeat in range(1, args.runs + 1):
                olean.unlink(missing_ok=True)
                result = sample(directory, f"{repeat}-window-construct",
                                lean_command(args, defs, f"--root={directory}", "-o", str(olean)), args.seconds, env)
                writer.writerow([case, repeat, "construct", *result[1:]])
                csv_file.flush()
                if result[3]:
                    continue
                for phase, body in phases.items():
                    source.write_text("module\nimport WindowInput\nimport Window\nimport Quote\n"
                                      "\nopen WasmKernelBench Silmaril.Wasm.Binary.Core\n\n" + body)
                    result = sample(directory, f"{repeat}-window-{phase}", lean_command(args, source),
                                    args.seconds, env)
                    writer.writerow([case, repeat, phase, *result[1:]])
                    csv_file.flush()


def runtime_cases(out, selected, args):
    with tempfile.NamedTemporaryFile(prefix=".wasm-bench-", suffix=".toml", dir=ROOT) as config:
        config.write((ROOT / "lakefile.toml").read_bytes())
        config.write(b'\n[[lean_exe]]\nname = "wasm-kernel-decode-bench"\n'
                     b'root = "Runtime"\nsrcDir = "benchmarks/wasm-kernel-decode"\n')
        config.flush()
        subprocess.run(["lake", "-f", config.name, "build", "--wfail", "wasm-kernel-decode-bench"],
                       cwd=ROOT, check=True)
    executable = ROOT / ".lake/build/bin/wasm-kernel-decode-bench"
    with (out / "native.csv").open("w") as csv_file:
        writer = csv.writer(csv_file)
        writer.writerow(["case", "run", "phase", "wall_s", "peak_rss_kib", "exit", "native_ns"])
        for case, binary, _ in selected:
            for repeat in range(1, args.runs + 1):
                for reader in READERS:
                    result = sample(binary.parent, f"{repeat}-native-{reader}",
                                    [str(executable), reader, str(binary)], args.seconds, os.environ)
                    writer.writerow([case, repeat, reader, *result[1:]])
                    csv_file.flush()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("--cases", nargs="+")
    parser.add_argument("--mode", choices=("kernel", "native", "window", "both"), default="both")
    parser.add_argument("--seconds", type=int, default=30)
    parser.add_argument("--memory", type=int, default=4096, help="Lean allocator limit in MiB")
    parser.add_argument("--stack", type=int, default=65536, help="Lean worker stack in KiB")
    parser.add_argument("--runs", type=int, default=1)
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    selected = []
    manifest = {}
    for case, source, data in fixtures():
        if args.cases and case not in args.cases:
            continue
        directory = output / case
        directory.mkdir(exist_ok=True)
        binary = directory / "source.wasm"
        binary.write_bytes(source)
        manifest[case] = {"bytes": len(source), "sha256": hashlib.sha256(source).hexdigest()}
        selected.append((case, binary, data))
    if not selected or (args.cases and set(args.cases) != set(manifest)):
        parser.error("unknown fixture name")
    (output / "fixtures.json").write_text(json.dumps(manifest, indent=2) + "\n")
    if args.mode in ("kernel", "both"):
        kernel_cases(output, selected, args)
    if args.mode in ("native", "both"):
        runtime_cases(output, selected, args)
    if args.mode == "window":
        window_cases(output, selected, args)


if __name__ == "__main__":
    main()

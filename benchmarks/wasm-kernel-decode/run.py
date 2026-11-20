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
PINNED = {
    "empty-check": "54c4c74e6990f39b6cd1a5c7c1af7eae3a4dd6a725acd2eb7de2c21b1b0ce9ce",
    "ex-start": "bb4323bdfa85244147d28a9211f05540cd4bbce4c08c10820c70ebcb565ab259",
    "lrat": "2a7e04b514053262880547d1baf5d92fdfabddef6a4af2fce8bb7f1a08e1f2fc",
    "bodies-64": "39f658cc097c6795dd899ec806c2131debdc92a52967adfc8825c160895f2a3c",
    "bodies-512": "b7368c78cd5b1bd0640de8957944a26b90b928c696063af8b687c8486bfc3fdf",
    "data-4k": "4361a52f00ba3850106bc450930394b36b96ed44ce740e9ab8c963734208ed27",
    "data-1024k": "507568fd37b89414134ec9f96d8fa4b5d31993c0ef5527b9bcfde3e6f2fa10a6",
}


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


def kernel_cases(out, selected, args, *, bounded=False):
    build, env = build_kernel_harness(out, args)
    imports = "module\nimport Fixture\nimport Quote\n"
    if bounded:
        subprocess.run(["lake", "build", "--wfail", "+Silmaril.Wasm.Binary.Packed.Bounded.Thms"],
                       cwd=ROOT, check=True)
        imports += "import Silmaril.Wasm.Binary.Packed.Bounded.Thms\n"
        imports += "\nopen Silmaril.Wasm.Binary.Packed\n"
    with (out / "kernel.csv").open("w") as csv_file:
        writer = csv.writer(csv_file)
        writer.writerow(["case", "run", "phase", "wall_s", "peak_rss_kib", "exit", "agreement_ns"])
        for case, binary, data in selected:
            directory = binary.parent
            defs = directory / "Fixture.lean"
            declarations = f'wasm_bench_defs source expected from {json.dumps(binary.name)}\n'
            if bounded:
                ends = code_ends(binary.read_bytes())
                declarations += f'@[expose] public def codeEnds : Option (List Nat) := {ends}\n'
            defs.write_text(f'module\nimport Quote\n\n{declarations}')
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
                if bounded:
                    statement = f"{REF} source.toByteArray = some expected"
                    phases["fast"] = (
                        f"wasm_bench_agreement fastAgrees {FAST} source expected\n"
                        f"theorem agrees : {statement} := WasmKernelBench.reference_agrees _ _ fastAgrees\n"
                    )
                    phases["bounded"] = (
                        "wasm_bench_refl checked : Bounded.decode? source source.wf_true codeEnds = some expected\n"
                        f"theorem agrees : {statement} :=\n"
                        "  Bounded.decode_sound checked\n"
                    )
                for phase, body in phases.items():
                    source.write_text(f"{imports}\n{body}")
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


def read_u32(blob, offset, limit):
    value = 0
    for shift in range(0, 32, 7):
        if offset >= limit:
            raise ValueError("fixture has a truncated u32")
        byte = blob[offset]
        offset += 1
        value += (byte & 127) << shift
        if byte < 128 and value < 2**32:
            return value, offset
    raise ValueError("fixture has an invalid u32")


def section_extents(blob):
    if blob[:8] != HEADER:
        raise ValueError("fixture does not begin with a Core header")
    offset = 8
    while offset < len(blob):
        index = blob[offset]
        width, offset = read_u32(blob, offset + 1, len(blob))
        if offset + width > len(blob):
            raise ValueError("fixture has out-of-range section size")
        yield index, offset, width
        offset += width


def frame_layout(blob):
    return "[" + ", ".join(f"({index}, {width})" for index, _, width in section_extents(blob)) + "]"


def code_ends(blob):
    for index, start, width in section_extents(blob):
        if index == 10:
            limit = start + width
            count, offset = read_u32(blob, start, limit)
            ends = []
            for _ in range(count):
                size, offset = read_u32(blob, offset, limit)
                offset += size
                ends.append(offset - start)
            if offset != limit:
                raise ValueError("fixture has an invalid code entry extent")
            return f"some {ends}"
    return "none"


def framing_cases(out, selected, args):
    build, env = build_kernel_harness(out, args)
    subprocess.run(["lake", "build", "--wfail", "+Silmaril.Wasm.Binary.Packed.Thms"],
                   cwd=ROOT, check=True)
    with (out / "framing.csv").open("w") as csv_file:
        writer = csv.writer(csv_file)
        writer.writerow(["case", "run", "phase", "wall_s", "peak_rss_kib", "exit", "agreement_ns"])
        for case, binary, _ in selected:
            directory = binary.parent
            defs = directory / "FramingInput.lean"
            defs.write_text('module\nimport Quote\n\nkbytes_def source from_file "source.wasm"\n')
            olean = build / "FramingInput.olean"
            source = directory / "MeasureFrames.lean"
            layout = frame_layout(binary.read_bytes())
            finish = binary.stat().st_size
            statement = (f"scanFramesSpec.run cursor.spec =\n"
                         f"  .ok ({layout}, {{ cursor.spec with pos := {finish} }})")
            header = ("module\nimport Quote\npublic import FramingInput\n"
                      "public import Silmaril.Wasm.Binary.Packed.Thms\n\n"
                      "open Silmaril.Wasm.Binary.Packed\n"
                      "@[expose] public noncomputable def cursor : Cursor := ⟨source, source.wf_true, 0⟩\n")
            phases = {
                "import": "",
                "reference": f"wasm_bench_refl framed : {statement}\n",
                "packed": (
                    "wasm_bench_refl packedFramed : scanFrames.run cursor =\n"
                    f"  .ok ({layout}, {{ cursor with pos := {finish} }})\n"
                    f"theorem framed : {statement} :=\n"
                    f"  scanFramesSpec_of_ok cursor {layout} {finish} packedFramed\n"
                ),
            }
            result = sample(directory, "framing-construct",
                            lean_command(args, defs, f"--root={directory}", "-o", str(olean)), args.seconds, env)
            writer.writerow([case, 1, "construct", *result[1:]])
            for repeat in range(1, args.runs + 1):
                if result[3]:
                    break
                for phase, body in phases.items():
                    source.write_text(header + body)
                    result_phase = sample(directory, f"{repeat}-framing-{phase}",
                                          lean_command(args, source), args.seconds, env)
                    writer.writerow([case, repeat, phase, *result_phase[1:]])
                    csv_file.flush()


def passive_cases(out, selected, args):
    build, env = build_kernel_harness(out, args)
    subprocess.run(["lake", "build", "--wfail", "+Silmaril.Wasm.Binary.Packed.Passive.Thms"],
                   cwd=ROOT, check=True)
    with (out / "passive.csv").open("w") as csv_file:
        writer = csv.writer(csv_file)
        writer.writerow(["case", "run", "phase", "wall_s", "peak_rss_kib", "exit", "agreement_ns"])
        for case, binary, _ in selected:
            directory = binary.parent
            width = int(case.removeprefix("data-").removesuffix("k")) * 1024
            start = binary.stat().st_size - width
            mode_end = start - len(uleb(width))
            (directory / "passive.bin").write_bytes(binary.read_bytes()[start:])
            defs = directory / "PassiveInput.lean"
            defs.write_text('module\npublic import Quote\npublic import Silmaril.Wasm.Binary.Packed.Passive.Thms\n'
                            'open Silmaril.Wasm.Binary.Packed\n'
                            'wasm_bench_defs source expected from "source.wasm"\n'
                            'kbytes_def payload from_file "passive.bin"\n'
                            f'@[expose] public def plan : PassivePlan := ⟨{mode_end - 2}, {mode_end - 1}, '
                            f'{mode_end}, {start}⟩\n')
            olean = build / "PassiveInput.olean"
            source = directory / "MeasurePassive.lean"
            statement = f"{REF} source.toByteArray = some expected"
            phases = {
                "import": "",
                "reference": f"wasm_bench_agreement agreed {REF} source expected\n",
                "fast": (f"wasm_bench_agreement fastAgreed {FAST} source expected\n"
                         f"theorem agreed : {statement} := WasmKernelBench.reference_agrees _ _ fastAgreed\n"),
                "packed": (
                    "wasm_bench_refl spanOK : (source.slice plan.payloadStart payload.len).sameBytes 4096 payload = true\n"
                    "theorem verified : plan.Verified source source.wf_true payload where\n"
                    "  sectionPresent := by decide +kernel\n  countFits := by decide +kernel\n"
                    "  consumesInput := rfl\n  header := rfl\n  id := rfl\n  size := rfl\n  count := rfl\n"
                    "  mode := rfl\n  length := rfl\n  payloadMatches := spanOK\n"
                    f"theorem agreed : {statement} := verified.sound payload.wf_true\n"
                ),
            }
            result = sample(directory, "passive-construct",
                            lean_command(args, defs, f"--root={directory}", "-o", str(olean)), args.seconds, env)
            writer.writerow([case, 1, "construct", *result[1:]])
            for repeat in range(1, args.runs + 1):
                if result[3]:
                    break
                for phase, body in phases.items():
                    source.write_text("module\npublic import PassiveInput\n\n" + body)
                    result_phase = sample(directory, f"{repeat}-passive-{phase}",
                                          lean_command(args, source), args.seconds, env)
                    writer.writerow([case, repeat, phase, *result_phase[1:]])
                    csv_file.flush()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("--cases", nargs="+")
    parser.add_argument("--mode", choices=("kernel", "native", "window", "framing", "passive", "bounded", "both"),
                        default="both")
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
        if (args.cases and case not in args.cases) or (args.mode == "passive" and not data):
            continue
        directory = output / case
        directory.mkdir(exist_ok=True)
        binary = directory / "source.wasm"
        binary.write_bytes(source)
        digest = hashlib.sha256(source).hexdigest()
        if case in PINNED and PINNED[case] != digest:
            parser.error(f"{case}: fixture hash changed ({digest})")
        manifest[case] = {"bytes": len(source), "sha256": digest}
        selected.append((case, binary, data))
    if not selected or (args.cases and set(args.cases) != set(manifest)):
        parser.error("unknown fixture name")
    (output / "fixtures.json").write_text(json.dumps(manifest, indent=2) + "\n")
    if args.mode in ("kernel", "bounded", "both"):
        kernel_cases(output, selected, args, bounded=args.mode == "bounded")
    if args.mode in ("native", "both"):
        runtime_cases(output, selected, args)
    if args.mode == "window":
        window_cases(output, selected, args)
    if args.mode == "framing":
        framing_cases(output, selected, args)
    if args.mode == "passive":
        passive_cases(output, selected, args)


if __name__ == "__main__":
    main()

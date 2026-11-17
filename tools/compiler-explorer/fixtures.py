#!/usr/bin/env python3
"""Fixtures of the compiler explorer: builds, listings and problem manifests.

    python3 -I tools/compiler-explorer/fixtures.py build      # Docker: compile the demo programs
    python3 -I tools/compiler-explorer/fixtures.py listings   # Docker: objdump the compiles-to objects
    python3 -I tools/compiler-explorer/fixtures.py manifests  # no Docker: write the manifests

`build` and `listings` run the pinned gcc image of tools/c-tv (by digest) with no network
(`--network none`), the caller's uid and the sources mounted read-only. They write what they
produced and a receipt (image digest, command, tool versions and hashes, input and output
SHA-256) under examples/compiler-explorer/. `manifests` reads only committed files and is
deterministic: the manifests are a function of the sources, the receipts, the listings and
the c-tv correspondences.

Nothing here decides a proof status. A manifest names, per obligation, the Lean statement and
(when one exists) the theorem claimed to prove it; tools/compiler-explorer/export.lean decides
the status from the Lean build.
"""

from __future__ import annotations

import hashlib
import json
import os
import pathlib
import re
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[2]
EX = ROOT / "examples" / "compiler-explorer"
PROGRAMS = EX / "programs"
BUILDS = EX / "builds"
MANIFESTS = EX / "manifests"
COMPILES_TO = ROOT / "examples" / "compiles-to"
LISTINGS = EX / "compiles-to"

IMAGE = ("gcc:13.3.0@sha256:"
         "1d71f0f3450214bef38fe09e6f610fb6cca90cf97b43f4ce845bfc32a4168818")
OPTS = ["O0", "O2"]
S_FLAGS = ["-g", "-S", "-std=c11", "-fno-asynchronous-unwind-tables",
           "-fdebug-prefix-map=/src=."]
# The demo programs, in the order of the staged examples, with their link libraries.
PROGRAM_LIBS = {"hello": [], "msort": [], "fft": ["-lm"], "lisp": []}
# What each program should print, written down from its meaning (the FFT of four ones and four
# zeros: X_k = sum_{n<4} e^{-2 pi i k n / 8}), not copied from a run.
EXPECTED_STDOUT = {
    "hello": "hello, world\n",
    "msort": "1 2 3 4 5 6 7 8\n",
    "fft": ("0: +4.000 +0.000i\n1: +1.000 -2.414i\n2: +0.000 +0.000i\n3: +1.000 -0.414i\n"
            "4: +0.000 +0.000i\n5: +1.000 +0.414i\n6: +0.000 +0.000i\n7: +1.000 +2.414i\n"),
    "lisp": "11\n(1 2 3)\n",
}
SCHEMA = "silmaril.compiler-explorer.problem/1"
LEAN_MODULE = "CompilesToExamples.Explorer.Builds"


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def file_ref(path: pathlib.Path, media: str) -> dict:
    data = path.read_bytes()
    return {"path": path.relative_to(ROOT).as_posix(), "sha256": sha256(data),
            "size": len(data), "media": media}


def dump(path: pathlib.Path, obj) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=2, sort_keys=True, ensure_ascii=False) + "\n")


def docker(mounts: list[tuple[pathlib.Path, str, bool]], script: str) -> None:
    cmd = ["docker", "run", "--rm", "--network", "none", "-u", f"{os.getuid()}:{os.getgid()}"]
    for host, guest, ro in mounts:
        cmd += ["-v", f"{host}:{guest}" + (":ro" if ro else "")]
    cmd += ["-w", "/src", IMAGE, "sh", "-eu", "-c", script]
    subprocess.run(cmd, check=True)


TOOLS = ('gcc --version | head -n1 > /out/gcc.txt; as --version | head -n1 > /out/as.txt; '
         'sha256sum "$(gcc -print-prog-name=cc1)" "$(command -v as)" "$(command -v ld)" '
         '> /out/tools.txt')


def build() -> None:
    """Compile each program at each level to assembly, assemble and link that assembly, and run it."""
    for prog, libs in PROGRAM_LIBS.items():
        src = PROGRAMS / f"{prog}.c"
        for opt in OPTS:
            out = BUILDS / prog / opt
            out.mkdir(parents=True, exist_ok=True)
            with tempfile.TemporaryDirectory() as tmp:
                compile_cmd = " ".join(["gcc", f"-{opt}", *S_FLAGS, f"{prog}.c", "-o", f"/out/{prog}.s"])
                link_cmd = " ".join(["gcc", f"/out/{prog}.s", "-o", f"/out/{prog}", *libs])
                docker([(PROGRAMS, "/src", True), (pathlib.Path(tmp), "/out", False)],
                       f"{compile_cmd}; {link_cmd}; set +e; /out/{prog} > /out/stdout.txt; "
                       f"echo $? > /out/exit.txt; set -e; {TOOLS}")
                t = pathlib.Path(tmp)
                asm = (t / f"{prog}.s").read_bytes()
                (out / f"{prog}.s").write_bytes(asm)
                stdout = (t / "stdout.txt").read_bytes()
                receipt = {
                    "image": IMAGE, "workdir": "/src", "network": "none",
                    "command": compile_cmd.replace("/out/", ""),
                    "gcc": (t / "gcc.txt").read_text().strip(),
                    "as": (t / "as.txt").read_text().strip(),
                    "tools_sha256": (t / "tools.txt").read_text().strip().splitlines(),
                    "source": {"path": f"{prog}.c", "sha256": sha256(src.read_bytes())},
                    "assembly": {"path": f"{opt}/{prog}.s", "sha256": sha256(asm), "size": len(asm)},
                }
                run = {
                    "kind": "execution",
                    "what": ("the assembly above, assembled and linked by the same image against its "
                             "glibc, run once in the container with no input"),
                    "link": link_cmd.replace("/out/", ""),
                    "run": f"./{prog}",
                    "assembly_sha256": sha256(asm),
                    "exit": int((t / "exit.txt").read_text().strip()),
                    "stdout": stdout.decode("utf-8"),
                    "stdout_sha256": sha256(stdout),
                }
                dump(out / "RECEIPT.json", receipt)
                dump(out / "run.json", run)
                print(f"built {prog} -{opt}: {len(asm)} bytes of assembly, exit {run['exit']}")


def listings() -> None:
    """objdump the committed compiles-to objects (the bytes the Lean statements are about)."""
    for name in sorted(p.name for p in COMPILES_TO.iterdir() if (p / f"{p.name}.c").exists()):
        for opt in OPTS:
            obj_dir = COMPILES_TO / name / opt
            obj = obj_dir / f"{name}.o"
            if not obj.exists():
                continue
            out = LISTINGS / name / opt
            out.mkdir(parents=True, exist_ok=True)
            with tempfile.TemporaryDirectory() as tmp:
                cmd = f"objdump -d -w -j .text {name}.o"
                docker([(obj_dir, "/src", True), (pathlib.Path(tmp), "/out", False)],
                       f"{cmd} > /out/listing.txt; objdump --version | head -n1 > /out/objdump.txt")
                t = pathlib.Path(tmp)
                text = (t / "listing.txt").read_bytes()
                (out / "listing.txt").write_bytes(text)
                dump(out / "RECEIPT.json", {
                    "image": IMAGE, "workdir": "/src", "network": "none", "command": cmd,
                    "objdump": (t / "objdump.txt").read_text().strip(),
                    "object": {"path": f"examples/compiles-to/{name}/{opt}/{name}.o",
                               "sha256": sha256(obj.read_bytes())},
                    "listing": {"path": "listing.txt", "sha256": sha256(text), "size": len(text)},
                })
                print(f"listed {name} -{opt}")


# ---------------------------------------------------------------------------------------------
# Fragments: content-addressed sets of ranges


def fragment(artifact_sha: str, space: str, ranges: list[list[int]], role: str, label: str) -> dict:
    """A fragment: ranges in one artifact's coordinate space, identified by their content address."""
    ranges = sorted([list(r) for r in ranges])
    fid = sha256(f"{artifact_sha}:{space}:{json.dumps(ranges)}".encode())[:20]
    return {"id": fid, "artifact": role, "space": space, "ranges": ranges, "label": label}


def line_ranges(data: bytes) -> list[tuple[int, int]]:
    """Byte range [start, end) of each line (1-based index = position + 1), without newline."""
    out, start = [], 0
    for i, b in enumerate(data):
        if b == 0x0A:
            out.append((start, i))
            start = i + 1
    if start < len(data):
        out.append((start, len(data)))
    return out


class Builder:
    def __init__(self, src_bytes: bytes, src_sha: str, tgt_sha: str, tgt_space: str):
        self.lines = line_ranges(src_bytes)
        self.src_sha, self.tgt_sha, self.tgt_space = src_sha, tgt_sha, tgt_space
        self.fragments: dict[str, dict] = {}
        self.edges: list[dict] = []

    def add(self, f: dict) -> str:
        self.fragments.setdefault(f["id"], f)
        return f["id"]

    def src_lines(self, lines: list[int]) -> str:
        ranges = [list(self.lines[n - 1]) for n in sorted(set(lines)) if 0 < n <= len(self.lines)]
        label = "line " + ",".join(str(n) for n in sorted(set(lines)))
        if len(set(lines)) > 1 and sorted(set(lines)) == list(range(min(lines), max(lines) + 1)):
            label = f"lines {min(lines)}-{max(lines)}"
        return self.add(fragment(self.src_sha, "bytes", ranges, "source", label))

    def tgt(self, ranges: list[list[int]], label: str) -> str:
        return self.add(fragment(self.tgt_sha, self.tgt_space, ranges, "target", label))


# ---------------------------------------------------------------------------------------------
# Assembly (gcc -S): the `.loc` directives, as a compiler explorer reads them

LOC = re.compile(r"^\s*\.loc\s+(\d+)\s+(\d+)")
FILE = re.compile(r'^\s*\.file\s+(\d+)\s+"([^"]*)"(?:\s+"([^"]*)")?')
LABEL = re.compile(r"^([A-Za-z_.$][\w.$]*):")


def is_instruction(line: str) -> bool:
    s = line.strip()
    return bool(s) and not s.startswith(".") and not s.startswith("#") and not LABEL.match(s)


def asm_navigation(b: Builder, asm: bytes, src_name: str) -> dict:
    """Navigation edges from `.loc`: per (function, source line), the instruction lines after a
    `.loc` of that line in that function. Debug information, not semantics."""
    files: dict[str, str] = {}
    cur_fn = None
    cur_loc: tuple[str, int] | None = None
    groups: dict[tuple[str, int], list[list[int]]] = {}
    other: dict[str, int] = {}
    unattributed = 0
    offset = 0
    for raw in asm.split(b"\n"):
        start, end = offset, offset + len(raw)
        offset = end + 1
        line = raw.decode("utf-8")
        if m := FILE.match(line):
            files[m.group(1)] = m.group(3) or m.group(2)
            continue
        if (m := LABEL.match(line)) and not m.group(1).startswith("."):
            cur_fn, cur_loc = m.group(1), None
            continue
        if m := LOC.match(line):
            cur_loc = (m.group(1), int(m.group(2)))
            continue
        if not is_instruction(line):
            continue
        if cur_loc is None or cur_fn is None:
            unattributed += 1
            continue
        fname = files.get(cur_loc[0], "?")
        if fname != src_name:
            other[fname] = other.get(fname, 0) + 1
            continue
        groups.setdefault((cur_fn, cur_loc[1]), []).append([start, end])
    for (fn, ln), ranges in sorted(groups.items(), key=lambda kv: (kv[0][0], kv[0][1])):
        s = b.src_lines([ln])
        t = b.tgt(ranges, f"{fn}: {len(ranges)} instruction(s) of line {ln}")
        b.edges.append({"id": f"nav/{fn}/{ln}", "kind": "navigation", "origin": "dwarf-loc",
                        "function": fn, "source": [s], "target": [t]})
    return {"unattributed_instructions": unattributed,
            "instructions_from_other_files": dict(sorted(other.items()))}


def program_manifests() -> list[dict]:
    out = []
    for prog in PROGRAM_LIBS:
        src = PROGRAMS / f"{prog}.c"
        for opt in OPTS:
            d = BUILDS / prog / opt
            receipt = json.loads((d / "RECEIPT.json").read_text())
            run = json.loads((d / "run.json").read_text())
            asm_path = d / f"{prog}.s"
            src_ref, asm_ref = file_ref(src, "text/x-c"), file_ref(asm_path, "text/x-asm")
            assert receipt["source"]["sha256"] == src_ref["sha256"], f"{prog}: source changed since build"
            assert receipt["assembly"]["sha256"] == asm_ref["sha256"], f"{prog}: assembly changed"
            b = Builder(src.read_bytes(), src_ref["sha256"], asm_ref["sha256"], "bytes")
            stats = asm_navigation(b, asm_path.read_bytes(), f"{prog}.c")
            obligations = [
                {"id": "translation", "kind": "translation", "decl": None, "statement": None,
                 "unsupported": ("no source semantics in Lean covers this program: the C "
                                 "elaborator of Silmaril.Project.CompilesTo has no loops, calls, "
                                 "pointers, floating point or I/O, and no x86 model here covers "
                                 "the linked program with glibc")},
                {"id": "abi", "kind": "abi", "decl": None, "statement": None,
                 "unsupported": "no ABI statement is attempted for this program"},
                {"id": "mapping", "kind": "mapping", "decl": None, "statement": None,
                 "unsupported": "no semantic mapping: only the compiler's debug line table"},
                {"id": "refinement", "kind": "refinement", "decl": None, "statement": None,
                 "unsupported": "no comorphism relation is generated for this program"},
            ]
            out.append({
                "schema": SCHEMA,
                "id": f"programs/{prog}/{opt}",
                "title": f"{prog}.c, gcc 13.3.0 -{opt} (assembly)",
                "direction": "compiled",
                "artifacts": {"source": src_ref, "target": asm_ref,
                              "receipt": file_ref(d / "RECEIPT.json", "application/json"),
                              "run": file_ref(d / "run.json", "application/json")},
                "view": {"source": "source", "target": "target"},
                "derivation": {"kind": "compiler", "compiler": "gcc", "version": receipt["gcc"],
                               "image": IMAGE, "command": receipt["command"], "opt": opt,
                               "target": "x86_64-linux-gnu", "receipt": "receipt"},
                "context": {
                    "source_model": None, "target_model": None, "abi": None,
                    "mapping_relation": None, "comorphism": None,
                },
                "fragments": sorted(b.fragments.values(), key=lambda f: f["id"]),
                "edges": b.edges,
                "navigation_stats": stats,
                "obligations": obligations,
                "tests": [{"id": "run", "kind": "execution", "artifact": "run",
                           "about": "target", "expected_stdout": EXPECTED_STDOUT[prog]}],
                "lean": {"family": None, "modules": []},
            })
    return out


# ---------------------------------------------------------------------------------------------
# The compiles-to examples: the objects the Lean statements are about

# The Lean theorems of CompilesToExamples.Explorer.Builds, per (file, build): its namespace, and
# whether every segment of the build is proved.
LEAN_BUILDS = {("straight", "O0"): ("StraightO0", True), ("straight", "O2"): ("StraightO2", True),
               ("branch", "O0"): ("BranchO0", True), ("branch", "O2"): ("BranchO2", False)}
OBJDUMP = re.compile(r"^\s*([0-9a-f]+):\t([0-9a-f ]+)\t(.*)$")


def cexplorer():
    """The database module, for its statement templates (one definition of each statement)."""
    import importlib.util
    spec = importlib.util.spec_from_file_location("cexplorer", pathlib.Path(__file__).with_name("cexplorer.py"))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def listing_rows(text: bytes) -> list[tuple[int, int, int, int]]:
    """(text offset, instruction length, byte start, byte end) of each instruction line."""
    rows, offset = [], 0
    for raw in text.split(b"\n"):
        start, end = offset, offset + len(raw)
        offset = end + 1
        if m := OBJDUMP.match(raw.decode("utf-8")):
            rows.append((int(m.group(1), 16), len(m.group(2).split()), start, end))
    return rows


def compiles_to_manifests() -> list[dict]:
    cx = cexplorer()
    out = []
    for name in ["straight", "branch", "loop"]:
        src = COMPILES_TO / name / f"{name}.c"
        corr = json.loads((COMPILES_TO / name / "correspondence.json").read_text())
        cname = name.capitalize()
        for opt in OPTS:
            obj = COMPILES_TO / name / opt / f"{name}.o"
            receipt_path = COMPILES_TO / name / opt / "RECEIPT.json"
            receipt = json.loads(receipt_path.read_text())
            lst = LISTINGS / name / opt / "listing.txt"
            lst_receipt = json.loads((LISTINGS / name / opt / "RECEIPT.json").read_text())
            src_ref, obj_ref = file_ref(src, "text/x-c"), file_ref(obj, "application/x-elf-relocatable")
            lst_ref = file_ref(lst, "text/x-objdump")
            assert receipt["object"]["sha256"] == obj_ref["sha256"]
            assert lst_receipt["object"]["sha256"] == obj_ref["sha256"], "listing of another object"
            assert lst_receipt["listing"]["sha256"] == lst_ref["sha256"]
            rows = listing_rows(lst.read_bytes())
            for fn in corr[opt]:
                fname = fn["name"]
                b = Builder(src.read_bytes(), src_ref["sha256"], obj_ref["sha256"], "text-offset")
                base = fn["off"]
                notes = {(u["line"], u["start"]): u["reason"] for u in fn.get("unsupported", [])}
                # navigation: the DWARF line table, as c-tv read it (`ranges`)
                for r in fn["ranges"]:
                    s = b.src_lines([r["line"]])
                    t = b.tgt([[base + r["start"], base + r["end"]]],
                              f"[{base + r['start']:#x}, {base + r['end']:#x})")
                    e = {"id": f"nav/{fname}/{r['line']}/{r['start']}", "kind": "navigation",
                         "origin": "dwarf-line-table", "function": fname, "source": [s], "target": [t]}
                    if (r["line"], r["start"]) in notes:
                        e["note"] = "no statement-level point (c-tv): " + notes[(r["line"], r["start"])]
                    b.edges.append(e)
                ns, proved = LEAN_BUILDS.get((name, opt), (None, False))
                unsupported_reason = fn.get("function_unsupported")
                pts = [] if unsupported_reason or ns is None else fn["points"]
                F = f"CompilesToExamples.{cname}.{opt}.{fname}"
                lean_vars = {"fn": F, "ail": f"CompilesToExamples.{cname}.ail", "cname": fname,
                             "isa": "Silmaril.X86.Open.isa",
                             "comorphism": "Silmaril.Project.CompilesTo.dwarf",
                             "target_value": f"silmaril.compiles_to.{name}.{opt.lower()}.obj"}
                X = f"CompilesToExamples.Explorer.{ns}"

                def ob(oid, kind, decl, edge=None, point=None, line=None):
                    o = {"id": oid, "kind": kind, "decl": decl,
                         "statement": cx.statement_for("c-function-x86", lean_vars, kind, point, line)}
                    if edge:
                        o["edge"] = edge
                    return o

                obligations = []
                last_line = max(r["line"] for r in fn["ranges"])
                for i, p in enumerate(pts):
                    lo = p["line"]
                    hi = pts[i + 1]["line"] if i + 1 < len(pts) else last_line + 1
                    end = pts[i + 1]["off"] if i + 1 < len(pts) else fn["size"]
                    s = b.src_lines(list(range(lo, hi)))
                    t = b.tgt([[base + p["off"], base + end]],
                              f"from {base + p['off']:#x} (point {p['index']})")
                    kind = p["kind"] if isinstance(p["kind"], str) else next(iter(p["kind"]))
                    eid = f"seg/{fname}/{p['index']}"
                    b.edges.append({"id": eid, "kind": "semantic", "point": p["index"], "line": p["line"],
                                    "point_kind": kind, "function": fname, "source": [s], "target": [t]})
                    k = p["index"]
                    obligations.append(ob(f"edge/{k}", "edge", f"{X}.edge_{k}" if proved else None,
                                          eid, k, p["line"]))
                    obligations.append(ob(f"point/{k}", "point",
                                          f"CompilesToExamples.{cname}.{opt}.{fname}_point_{k}", eid, k, p["line"]))
                if pts:
                    obligations += [
                        ob("translation", "translation", f"{X}.translation_valid" if proved else None),
                        ob("mapping", "mapping", f"{X}.mapping_valid" if proved else None),
                        ob("refinement", "refinement", f"{X}.refines_dwarf"),
                        ob("abi", "abi", f"CompilesToExamples.{cname}.{opt}.{fname}_enterable" if proved else None),
                        ob("elaboration", "elaboration", f"{X}.elaboration"),
                        ob("artifact", "artifact", f"CompilesToExamples.Explorer.{name}_{opt}_code"),
                        ob("nonvacuity/canonical", "nonvacuity_canonical", f"{X}.canonical" if proved else None),
                        ob("nonvacuity/universal", "nonvacuity_universal", None),
                    ]
                    lean = {"family": "c-function-x86", "vars": lean_vars,
                            "modules": [LEAN_MODULE, "CompilesToExamples.Explorer.Code"],
                            "registry": {"source": f"silmaril.compiles_to.{name}.source",
                                         "target": f"silmaril.compiles_to.{name}.{opt.lower()}.object"}}
                    ctx = {
                        "source_model": {"family": "cerberus-core",
                                         "decl": "Silmaril.Project.CompilesTo.FnData.source",
                                         "version": "Lean port of Cerberus Core (Project.Shapes.C.ElabAil, LP64)"},
                        "target_model": {"family": "x86-64", "decl": "Silmaril.X86.Open.isa",
                                         "version": "silmaril open x86-64 model (SegVC, single thread)"},
                        "abi": {"id": "sysv-amd64-integer",
                                "decl": "Silmaril.Project.CompilesTo.FnData.Holds (PointKind.entry)",
                                "version": "System V AMD64 psABI: INTEGER-class arguments, LP64"},
                        "mapping_relation": {"family": "cut-point",
                                             "decl": "Silmaril.Project.CompilesTo.FnData.mapping",
                                             "version": "c-tv program points"},
                        "comorphism": {"family": "observation", "decl": "Silmaril.Project.CompilesTo.dwarf",
                                       "version": "C objects at their DWARF DW_OP_fbreg frame slots"},
                    }
                else:
                    reason = unsupported_reason or "c-tv produced no program points for this function"
                    for k in ["translation", "mapping", "refinement", "abi"]:
                        obligations.append({"id": k, "kind": k, "decl": None, "statement": None,
                                            "unsupported": reason})
                    lean = {"family": None, "modules": []}
                    ctx = {"source_model": None, "target_model": None, "abi": None,
                           "mapping_relation": None, "comorphism": None}
                listing_map = [[o, o + n, s, e] for (o, n, s, e) in rows]
                out.append({
                    "schema": SCHEMA,
                    "id": f"compiles-to/{name}/{opt}/{fname}",
                    "title": f"{name}.c, gcc 13.3.0 -{opt}, {fname} (object code)",
                    "direction": "compiled",
                    "artifacts": {"source": src_ref, "target": obj_ref, "listing": lst_ref,
                                  "receipt": file_ref(receipt_path, "application/json"),
                                  "listing_receipt": file_ref(LISTINGS / name / opt / "RECEIPT.json",
                                                              "application/json")},
                    "view": {"source": "source", "target": "listing", "target_map": listing_map},
                    "derivation": {"kind": "compiler", "compiler": "gcc", "version": receipt["gcc"],
                                   "image": receipt["image"], "command": receipt["command"], "opt": opt,
                                   "target": "x86_64-linux-gnu", "receipt": "receipt"},
                    "context": ctx,
                    "fragments": sorted(b.fragments.values(), key=lambda f: f["id"]),
                    "edges": b.edges,
                    "obligations": obligations,
                    "tests": [],
                    "lean": lean,
                })
    return out


def manifests() -> None:
    MANIFESTS.mkdir(parents=True, exist_ok=True)
    for old in MANIFESTS.glob("*.json"):
        old.unlink()
    for m in compiles_to_manifests() + program_manifests():
        dump(MANIFESTS / (m["id"].replace("/", "--") + ".json"), m)
        print(f"wrote {m['id']}: {len(m['edges'])} edges, {len(m['obligations'])} obligations")


def main(argv: list[str]) -> int:
    cmds = {"build": build, "listings": listings, "manifests": manifests}
    if len(argv) != 2 or argv[1] not in cmds:
        print(__doc__, file=sys.stderr)
        return 2
    cmds[argv[1]]()
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))

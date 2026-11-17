#!/usr/bin/env python3
"""Classify the sysvScalar-claimable functions of the pinned math.h against the pinned libm.

    python3 -I scripts/libm-rows/gen.py [--check]

Reads examples/elf/pinned/glibc-2.36-libm.so.6 (checked against its SHA-256) and the list of
functions `claimable sysvScalar sysvCcs glibcMath` (printed by scripts/libm-rows/claimable.lean
under `lake env lean`), and writes

* Silmaril/Elf/Abi/Libm/Table/Defs.lean: the classification as a Lean literal (`classes`) and
  the code bytes of the stated rows. Nothing in it is trusted: `Silmaril.Elf.Abi.Libm.Thms`
  checks in the kernel that the names are the import's claimable functions in order, that every
  class is what ld.so's versioned lookup finds in the file's parse, and that the code bytes are
  the file's.
* examples/elf/libm-rows/classification.txt: the report, one line per function, with the
  unverified sweep of each plain function's code (GNU objdump's disassembly of
  [st_value, st_value + st_size)): RIP-relative operands, %fs, calls, branches leaving the
  symbol, indirect branches, VEX/EVEX and BMI forms, x87 forms, stores below %rsp. The sweep is
  a recipe-level listing, not a theorem.

With --check, regenerate into a temporary directory and fail if either file differs. The report
records the objdump version; --check compares the report only when the local objdump is that
version (as scripts/elf-reader/gen.sh does for its listings).
"""
import hashlib
import os
import re
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
LIB = "examples/elf/pinned/glibc-2.36-libm.so.6"
SHA = "7f2ca87f652f56b094462474b076749e90e689d0ecb9cb63c7679820b271b4e7"
LEAN_OUT = "Silmaril/Elf/Abi/Libm/Table/Defs.lean"
REPORT = "examples/elf/libm-rows/classification.txt"

# The rows stated in Silmaril.Elf.Abi.Libm: plain double-argument functions whose code the sweep
# finds clean (no RIP-relative operand, no %fs, no call, no branch out of the symbol, no indirect
# branch, no VEX/EVEX, BMI or x87 form; fmax/fmin store in the red zone) and whose every
# instruction the model steps (lround/llround use `bts`, __issignaling `btc`: model gaps).
ROWS = ["__fpclassify", "__signbit", "__finite", "finite", "round", "lrint", "llrint", "lrintf",
        "llrintf", "fmax", "fmin"]

# The status of the functions the rows considered (Silmaril.Elf.Abi.Libm); every other plain
# function is unstated, for the reasons its sweep flags give.
NOTES = {
    "lrint": "row: conformance PROVED (Libm.lrint_conforms)",
    "llrint": "row: conformance PROVED (Libm.llrint_conforms)",
    "lrintf": "row: open (Task.libm_lrintf)",
    "llrintf": "row: open (Task.libm_llrintf)",
    "round": "row: open (Task.libm_round)",
    "fmax": "row: open (Task.libm_fmax), red-zone store (frame 8)",
    "fmin": "row: open (Task.libm_fmin), red-zone store (frame 8)",
    "__fpclassify": "row: open (Task.libm_fpclassify)",
    "__signbit": "row: open (Task.libm_signbit)",
    "__finite": "row: open (Task.libm_finiteInternal)",
    "finite": "row: open (Task.libm_finite)",
    "lround": "model gap: bts (stuck on Str9L)",
    "llround": "model gap: bts (stuck on Str9L)",
    "__issignaling": "model gap: btc (stuck on Str9L)",
    "fabs": "not stated: reads a .rodata mask; Placed.data grants execute permission only",
    "fabsf": "not stated: reads a .rodata mask; Placed.data grants execute permission only",
    "copysign": "model gap: movq xmm, [rip+d] (stuck on Str9L); also .rodata",
    "copysignf": "not stated: reads a .rodata mask; Placed.data grants execute permission only",
}

# Lean names of the row functions whose C names start with `__`.
IDENT = {"__fpclassify": "fpclassify", "__signbit": "signbit", "__finite": "finiteInternal"}

BMI = {"andn", "bextr", "blsi", "blsmsk", "blsr", "bzhi", "mulx", "pdep", "pext", "rorx",
       "sarx", "shlx", "shrx", "tzcnt", "lzcnt", "adcx", "adox", "movbe"}


def elf_hash(name: str) -> int:
    h = 0
    for c in name.encode():
        h = ((h << 4) + c) & 0xFFFFFFFF
        g = h & 0xF0000000
        if g:
            h ^= g >> 24
        h &= ~g & 0xFFFFFFFF
    return h


def run(*cmd):
    return subprocess.run(cmd, cwd=ROOT, check=True, capture_output=True, text=True).stdout


def dynsyms():
    """(index, value, size, type, bind, ndx, name, version, default) of every .dynsym entry."""
    out = []
    for line in run("readelf", "--dyn-syms", "-W", LIB).splitlines():
        m = re.match(r"\s*(\d+): ([0-9a-f]+)\s+(\d+)\s+(\w+)\s+(\w+)\s+\w+\s+(\w+)\s+(\S+)", line)
        if not m:
            continue
        idx, val, size, typ, bind, ndx, full = m.groups()
        if "@@" in full:
            name, ver, default = *full.split("@@"), True
        elif "@" in full:
            name, ver, default = *full.split("@"), False
        else:
            name, ver, default = full, None, True
        out.append((int(idx), int(val, 16), int(size), typ, bind, ndx, name, ver, default))
    return out


def disasm():
    """address -> (bytes, text) for every instruction objdump lists."""
    ins = {}
    for line in run("objdump", "-d", "-w", "-z", LIB).splitlines():
        m = re.match(r"\s*([0-9a-f]+):\t([0-9a-f ]+)\t(.*)$", line)
        if m:
            ins[int(m.group(1), 16)] = (bytes.fromhex(m.group(2).replace(" ", "")), m.group(3))
    return ins


def sweep(ins, lo, hi):
    """The flags of the instructions in [lo, hi), and the instruction count."""
    flags = set()
    n = 0
    a = lo
    while a < hi:
        if a not in ins:
            flags.add("unlisted")
            break
        b, text = ins[a]
        n += 1
        mn = text.split()[0] if text.split() else ""
        if mn in ("rep", "repz", "repnz", "lock", "notrack", "bnd", "data16", "cs", "ds"):
            mn = text.split()[1] if len(text.split()) > 1 else mn
        if "(%rip)" in text:
            flags.add("rip")
        if "%fs:" in text:
            flags.add("fs")
        if mn.startswith("call"):
            flags.add("call")
        if mn.startswith("j") or mn.startswith("call"):
            if "*" in text:
                flags.add("indirect")
            else:
                t = re.search(r"\s([0-9a-f]+) <", text)
                if t and not (lo <= int(t.group(1), 16) < hi):
                    flags.add("branch-out")
        if b and b[0] in (0xC4, 0xC5, 0x62) or mn.startswith("v"):
            flags.add("vex")
        if mn in BMI:
            flags.add("bmi")
        if mn.startswith("f") and mn not in ("fabs",) and re.match(
                r"f(ld|st|add|sub|mul|div|chs|abs|xch|com|ucom|rndint|scale|sqrt|prem|init|"
                r"nstcw|ldcw|stcw|nstsw|stsw|wait|i|bstp|bld|yl2x|2xm1|patan|sin|cos|free|"
                r"cmov|xam|tst|ld1|ldz|ldl|ldpi|nop)", mn):
            flags.add("x87")
        if mn in ("rdssp", "rdsspq", "incssp", "incsspq", "endbr64"):
            flags.add("cet")
        if re.search(r"(mov|st)\S*\s+\S+,-0x[0-9a-f]+\(%rsp\)", text):
            flags.add("redzone")
        a += len(b)
    return sorted(flags), n


def lean_bytes(b):
    rows = [b[i:i + 16] for i in range(0, len(b), 16)]
    return "[" + ",\n    ".join(", ".join(f"0x{x:02X}" for x in r) for r in rows) + "]"


def generate(names, outdir):
    syms = dynsyms()
    ins = disasm()
    objdump_v = run("objdump", "--version").splitlines()[0]
    classes = []
    report = []
    for f in names:
        defs = [s for s in syms if s[6] == f and s[5] != "UND"]
        dflt = [s for s in defs if s[8]]
        compat = sorted({s[7] for s in defs if not s[8]})
        if not defs:
            classes.append((f, "absent", None))
            report.append((f, "absent", "", "", "", ""))
            continue
        assert len(dflt) == 1, (f, defs)
        idx, val, size, typ, bind, ndx, name, ver, _ = dflt[0]
        assert ver is not None, f
        if typ == "IFUNC":
            classes.append((f, "ifunc", (ver, idx)))
            report.append((f, "ifunc", ver, ",".join(compat), f"{val:#x}+{size}", "resolver chooses the code"))
        else:
            assert typ == "FUNC", (f, typ)
            flags, n = sweep(ins, val, val + size)
            classes.append((f, "plain", (ver, idx, val, size)))
            report.append((f, "plain", ver, ",".join(compat), f"{val:#x}+{size}",
                           f"{n} insns: " + (" ".join(flags) if flags else "clean")
                           + (f"; {NOTES[f]}" if f in NOTES else "")))
    # Lean literal.
    vers = sorted({c[2][0] for c in classes if c[2]})
    vname = {v: "v" + v.replace("GLIBC_", "").replace(".", "_") for v in vers}
    L = []
    L.append("module\n\npublic import Silmaril.Elf.Ast.Defs\npublic import Silmaril.Elf.Lookup.Defs\n")
    L.append("/-! # glibc 2.36 `libm.so.6`: the classification of the claimable `math.h` functions "
             "(generated: do not edit)\n")
    L.append("Written by `scripts/libm-rows/gen.py` from `examples/elf/pinned/glibc-2.36-libm.so.6` "
             f"(SHA-256 `{SHA}`) and\n`scripts/libm-rows/claimable.lean`; "
             "`gen.py --check` regenerates it and compares byte for byte.\n"
             "Untrusted data: `Silmaril.Elf.Abi.Libm.Thms` checks every entry against the import "
             "(`classes_names`) and the\nfile's parse (`classes_check`), and the row bytes "
             "against the file (`*_code`). -/\n")
    L.append("@[expose] public section\n\nnamespace Silmaril.Elf.Abi.Libm\n\nopen Silmaril.Elf\n")
    L.append("""/-- **What ld.so's lookup of a function's default version finds** in the file: a plain
`STT_FUNC` definition (version, `.dynsym` index, `st_value`, `st_size`), an `STT_GNU_IFUNC`
definition (version, index: the resolver chooses the code at load time), or no definition. -/
inductive Class where
  | plain (ver : Ver) (index value size : Nat)
  | ifunc (ver : Ver) (index : Nat)
  | absent
  deriving DecidableEq, Repr
""")
    for v in vers:
        L.append(f"/-- The version `{v}` as a reference requests it: name, ELF hash, not hidden. -/\n"
                 f"def {vname[v]} : Ver := ⟨nameOf \"{v}\", {elf_hash(v)}, false⟩\n")
    L.append("/-- **Every claimable function of the pinned `math.h`, in the import's order**, with "
             "what ld.so's lookup\nof its default version finds in the file (`Class`). -/")
    L.append("def classes : List (String × Class) := [")
    items = []
    for f, k, d in classes:
        if k == "absent":
            items.append(f"  (\"{f}\", .absent)")
        elif k == "ifunc":
            items.append(f"  (\"{f}\", .ifunc {vname[d[0]]} {d[1]})")
        else:
            items.append(f"  (\"{f}\", .plain {vname[d[0]]} {d[1]} {d[2]:#x} {d[3]})")
    L.append(",\n".join(items) + "]\n")
    by = {f: d for f, k, d in classes}
    for f in ROWS:
        ver, idx, val, size = by[f]
        b = open(os.path.join(ROOT, LIB), "rb").read()
        # The code is in the R+X PT_LOAD whose file offset equals its address (checked by
        # `CodeAt` in the kernel).
        code = b[val:val + size]
        L.append(f"/-- The code of `{f}` (`.dynsym` entry {idx}, `{f}@@{ver}`): {size} bytes at "
                 f"`{val:#x}`. -/")
        L.append(f"def {IDENT.get(f, f)}Bytes : List (BitVec 8) :=\n  {lean_bytes(code)}\n")
    L.append("end Silmaril.Elf.Abi.Libm\n\nend\n")
    lean = "\n".join(L)
    # Report.
    cnt = {k: sum(1 for c in classes if c[1] == k) for k in ("plain", "ifunc", "absent")}
    nondef = sum(1 for c in classes if c[2] and c[2][0] != "GLIBC_2.2.5")
    withcompat = sum(1 for r in report if r[3])
    clean = [r[0] for r in report if r[1] == "plain" and r[5].split(";")[0].endswith("clean")]
    R = []
    R.append("# glibc 2.36 libm.so.6 (Debian 12 libc6 2.36-9+deb12u14) against the pinned math.h")
    R.append("# GENERATED by scripts/libm-rows/gen.py; do not edit")
    R.append(f"# file: {LIB} sha256 {SHA}")
    R.append(f"# sweep: {objdump_v} (objdump -d -w -z; unverified listing, not a theorem)")
    R.append("# functions: claimable sysvScalar sysvCcs glibcMath (288; Machine.Abi.Conformance."
             "Import.Thms.glibcMath_coverage_sysvScalar)")
    R.append("# class: what ld.so's lookup of the default (@@) version finds in .dynsym "
             "(checked in the kernel: Silmaril.Elf.Abi.Libm.classes_check)")
    R.append(f"# counts: plain {cnt['plain']}, ifunc {cnt['ifunc']}, absent {cnt['absent']}; "
             f"default version other than GLIBC_2.2.5: {nondef}; with compat (@) versions: "
             f"{withcompat}")
    R.append(f"# sweep-clean plain functions: {len(clean)}: {' '.join(clean)}")
    R.append("# flags: rip = RIP-relative operand (rodata constant or GOT slot); fs = %fs: (TLS, "
             "errno); call; branch-out = jump leaving the symbol (tail call, PLT, shared code); "
             "indirect; vex; bmi; x87; cet; redzone = store below %rsp")
    R.append("# name\tclass\tversion\tcompat versions\tvalue+size\tsweep")
    for r in report:
        R.append("\t".join(r))
    rep = "\n".join(R) + "\n"
    os.makedirs(os.path.join(outdir, os.path.dirname(LEAN_OUT)), exist_ok=True)
    os.makedirs(os.path.join(outdir, os.path.dirname(REPORT)), exist_ok=True)
    open(os.path.join(outdir, LEAN_OUT), "w").write(lean)
    open(os.path.join(outdir, REPORT), "w").write(rep)
    return objdump_v


def main():
    check = sys.argv[1:] == ["--check"]
    if hashlib.sha256(open(os.path.join(ROOT, LIB), "rb").read()).hexdigest() != SHA:
        sys.exit(f"gen.py: {LIB} is not the pinned file")
    names = run("lake", "env", "lean", "scripts/libm-rows/claimable.lean").split()
    if len(names) != 288:
        sys.exit(f"gen.py: expected 288 claimable functions, got {len(names)}")
    if not check:
        generate(names, ROOT)
        print("gen.py: wrote", LEAN_OUT, "and", REPORT)
        return
    with tempfile.TemporaryDirectory() as d:
        v = generate(names, d)
        bad = False
        if open(os.path.join(d, LEAN_OUT)).read() != open(os.path.join(ROOT, LEAN_OUT)).read():
            print(f"gen.py: {LEAN_OUT} differs", file=sys.stderr); bad = True
        committed = open(os.path.join(ROOT, REPORT)).read()
        if f"# sweep: {v} " not in committed:
            print(f"gen.py: {REPORT} was written by another objdump; not compared", file=sys.stderr)
        elif open(os.path.join(d, REPORT)).read() != committed:
            print(f"gen.py: {REPORT} differs", file=sys.stderr); bad = True
        if bad:
            sys.exit(1)
    print("gen.py: ok")


if __name__ == "__main__":
    main()

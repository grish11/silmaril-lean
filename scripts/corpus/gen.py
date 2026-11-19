#!/usr/bin/env python3
"""Generate the kernel-checked ELF reader modules of the corpus (corpus/elf/<pkg>/<arch>/<object>).

    python3 -I scripts/corpus/gen.py [--check] [PKG...]

For every object listed in `corpus/elf/<pkg>/<arch>/SHA256SUMS` (the file's SHA-256 is checked
first), `elf-staged emit-reader` (`lake build elf-staged`) writes
`Silmaril/Elf/Staged/Corpus/<Pkg>/<Arch>/<Obj>/{Bytes,Defs,Thms,Functions,Decomp}.lean` in the
namespace `Silmaril.Elf.Staged.Corpus.<Pkg>.<Arch>.<Obj>`: every part of the file checked by the
kernel on its bytes, one theorem per function symbol, and one structural decomposition
(`Silmaril.Elf.Staged.Decomp.Decomposes`) per executable section with function symbols.
`Silmaril/Elf/Staged/Corpus.lean` imports every `Decomp` module, and `corpus/DECOMP.md` tabulates
the decompositions. With --check nothing is written and the command fails on any difference.
"""
import hashlib, re, subprocess, sys, tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
EMIT = ROOT / ".lake/build/bin/elf-staged"
ARCHES = ["x86_64", "aarch64"]


def camel(s):
    out = "".join(p[:1].upper() + p[1:] for p in re.split(r"[^A-Za-z0-9]+", s) if p)
    return ("N" + out) if out[:1].isdigit() else out


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    check = "--check" in sys.argv
    pkgs = args or sorted(p.name for p in (ROOT / "corpus/elf").iterdir() if p.is_dir())
    tmp = Path(tempfile.mkdtemp(prefix="corpus-gen-"))
    files, mods, rows = {}, [], []
    for pkg in pkgs:
        version = re.search(r'^version = "([^"]+)"', (ROOT / "corpus" / pkg / "package.toml").read_text(), re.M)[1]
        for arch in ARCHES:
            d = ROOT / "corpus/elf" / pkg / arch
            if not (d / "SHA256SUMS").exists():
                continue
            for line in (d / "SHA256SUMS").read_text().splitlines():
                if not line.strip():
                    continue
                digest, name = line.split(maxsplit=1)
                f = d / name.strip().lstrip("*")
                if sha(f) != digest:
                    sys.exit(f"gen: {f}: sha256 differs from SHA256SUMS")
                on = camel(f.name)
                if on == camel(pkg):  # `…Corpus.Openssl.X8664.Openssl` trips the duplicated-namespace linter
                    on += "Exe"
                parts = ["Silmaril", "Elf", "Staged", "Corpus", camel(pkg), camel(arch), on]
                mod = ".".join(parts)
                rel = f.relative_to(ROOT)
                title = f"{pkg} {version} `{f.name}` ({arch}; `{rel}`)"
                r = subprocess.run([str(EMIT), "emit-reader", str(rel), "/".join(parts[4:]), digest, title,
                                    str(tmp / "Silmaril/Elf/Staged/Corpus"), "--namespace", mod,
                                    "--include-path", "../" * len(parts) + str(rel),
                                    "--generator", "scripts/corpus/gen.py",
                                    "--max-table-entries", "2000"],
                                   cwd=ROOT, capture_output=True, text=True)
                if r.returncode:
                    sys.exit(f"gen: {f}: {r.stderr}{r.stdout}")
                base = Path(*parts)
                for m in ["Bytes", "Defs", "Thms", "Functions", "Decomp"]:
                    files[str(base / f"{m}.lean")] = (tmp / base / f"{m}.lean").read_text()
                for part in sorted((tmp / base / "Functions").glob("Part*.lean")):
                    files[str(base / "Functions" / part.name)] = part.read_text()
                for part in sorted((tmp / base / "Bodies").glob("Part*.lean")):
                    files[str(base / "Bodies" / part.name)] = part.read_text()
                # Whole-table body theorems of large symbol tables (tens of thousands of entries)
                # exceed the default heartbeat budget of one kernel check; lift it for Thms only.
                files[str(base / "Thms.lean")] = files[str(base / "Thms.lean")].replace(
                    "@[expose] public section\n", "set_option maxHeartbeats 0\n\n@[expose] public section\n", 1)
                mods.append(mod + ".Decomp")
                dec = files[str(base / "Decomp.lean")]
                tabs = re.findall(r"^\| `([^`]*)` \((\d+)\) \| (\d+) \| (\d+) \| (\d+) \(([\d.]+)%\) \| (\d+) \((\d+)\) \| (\d+) \| (\d+) \| (\d+) \|$", dec, re.M)
                along = re.search(r"Along (\S+)\.", dec)[1]
                if not tabs:
                    rows.append(f"| {pkg} | {arch} | `{f.name}` | {f.stat().st_size} | {along} | — | | | | | | |")
                for t in tabs:
                    rows.append(f"| {pkg} | {arch} | `{f.name}` | {f.stat().st_size} | {along} | `{t[0]}` | {t[2]} | {t[3]} | {t[4]} ({t[5]}%) | {t[6]} ({t[7]}) | {t[8]} | {t[9]} / {t[10]} |")
    files["Silmaril/Elf/Staged/Corpus.lean"] = ("module\n\n" + "".join(f"public import {m}\n" for m in sorted(mods)) +
        "\n/-! # The ELF corpus (`corpus/`): every object's structural function decomposition\n\n"
        "GENERATED by `scripts/corpus/gen.py`; do not edit. -/\n")
    files["corpus/DECOMP.md"] = """# Structural function decompositions of the corpus

GENERATED by `scripts/corpus/gen.py`; do not edit. One row per executable section with function
symbols, per object and architecture. Each row is the theorem
`Silmaril.Elf.Staged.Corpus.<Pkg>.<Arch>.<Obj>.decomp_<x>`. It is checked by the kernel on the file's bytes,
standard axioms only, and states that the function extents named by the symbol table plus the listed gaps
tile the section exactly. It says **nothing** about instruction decoding, control flow or behaviour.
*overlap / zero-size*: symbols left out because their extent overlaps a chosen one, and symbols of size 0.

| package | arch | object | bytes | along | section | section bytes | functions | covered | gaps (bytes) | aliases | overlap / zero-size |
|---|---|---|---|---|---|---|---|---|---|---|---|
""" + "\n".join(rows) + "\n"
    changed = []
    for p, text in files.items():
        path = ROOT / p
        if not path.exists() or path.read_text() != text:
            changed.append(p)
            if not check:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text)
    if check and changed:
        sys.exit("gen: out of date: " + ", ".join(changed[:10]))
    print(f"gen: {len(files)} files, {len(changed)} {'stale' if check else 'written'}")


if __name__ == "__main__":
    main()

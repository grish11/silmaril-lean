#!/usr/bin/env python3
"""Check the Wasm specification library (docs/projects/wasm-spec-library.md).

For every `Silmaril/WasmSpec/<Name>/manifest.toml` (and `<Name>/V<n>/manifest.toml`):

* the manifest parses and has the required tables (`results` and solutions only when the
  entry's `status` is not `stated`, which a stated entry must not list);
* `program.source` exists beside it, and the `wat3!` quotation of `program.lean` in
  `program.module` is the same text (up to surrounding whitespace);
* every named Lean module exists as a file;
* every solution's audited `axioms` are the standard three (the trust policy admits no others);
* every audited solution appears in a `#print axioms` audit of the entry's `Thms.lean`.

This compares texts only. The audits themselves are `#guard_msgs` checks, run by the Lean build.
"""
from __future__ import annotations

import pathlib
import re
import sys
import tomllib

ROOT = pathlib.Path(__file__).resolve().parent.parent
LIBRARY = ROOT / "Silmaril" / "WasmSpec"
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
MODES = {"tactic", "tactic+smt", "tactic+script", "all-in"}


def module_path(module: str) -> pathlib.Path:
    return ROOT / (module.replace(".", "/") + ".lean")


def quoted_wat(source: str, decl: str) -> str | None:
    """The raw-string body of `def <decl> … := wat3! r#"…"#` in `source`."""
    short = decl.rsplit(".", 1)[-1]
    m = re.search(r"def\s+" + re.escape(short) + r"\b[^\n]*?:=\s*wat3!\s*r#\"(.*?)\"#", source, re.S)
    return m.group(1) if m else None


def check(manifest: pathlib.Path) -> list[str]:
    errs: list[str] = []
    rel = manifest.relative_to(ROOT)
    try:
        m = tomllib.loads(manifest.read_text())
    except tomllib.TOMLDecodeError as e:
        return [f"{rel}: {e}"]
    # A `stated` entry has a specification but no results yet (no `results`, no solutions).
    stated = m.get("status") == "stated"
    for key in ("name", "version", "summary", "status", "program", "spec") + (() if stated else ("results",)):
        if key not in m:
            errs.append(f"{rel}: missing `{key}`")
    if stated and (m.get("results") or m.get("solution")):
        errs.append(f"{rel}: a `stated` entry lists results or solutions")
    if errs:
        return errs
    prog = m["program"]
    src = manifest.parent / prog.get("source", "")
    if not src.is_file():
        errs.append(f"{rel}: program.source {prog.get('source')!r} does not exist")
    mod = module_path(prog["module"])
    if not mod.is_file():
        errs.append(f"{rel}: program.module {prog['module']} has no file")
    elif src.is_file():
        q = quoted_wat(mod.read_text(), prog["lean"])
        if q is None:
            errs.append(f"{rel}: no `wat3!` quotation of {prog['lean']} in {prog['module']}")
        elif q.strip() != src.read_text().strip():
            errs.append(f"{rel}: {prog['lean']} does not quote {src.name} verbatim")
    for table in ("spec",) + (() if stated else ("results",)):
        if not module_path(m[table]["module"]).is_file():
            errs.append(f"{rel}: {table}.module {m[table]['module']} has no file")
    if stated:
        return errs
    thms = module_path(m["results"]["module"])
    audits = thms.read_text() if thms.is_file() else ""
    for sol in m.get("solution", []):
        if sol.get("mode") not in MODES:
            errs.append(f"{rel}: solution {sol.get('theorem')}: unknown mode {sol.get('mode')!r}")
        if not module_path(sol.get("module", "")).is_file():
            errs.append(f"{rel}: solution module {sol.get('module')} has no file")
        extra = set(sol.get("axioms", [])) - STANDARD
        if extra:
            errs.append(f"{rel}: solution {sol.get('theorem')} audits non-standard axioms {sorted(extra)}")
        if f"#print axioms {sol.get('theorem')}" not in audits:
            errs.append(f"{rel}: solution {sol.get('theorem')} has no `#print axioms` audit in {thms.name}")
    return errs


def main() -> int:
    manifests = sorted(LIBRARY.glob("*/manifest.toml")) + sorted(LIBRARY.glob("*/V*/manifest.toml"))
    errs = [e for p in manifests for e in check(p)]
    for e in errs:
        print(f"error: {e}", file=sys.stderr)
    if not errs:
        print(f"wasm-spec: {len(manifests)} entries, programs quoted verbatim, audits standard")
    return 1 if errs else 0


if __name__ == "__main__":
    sys.exit(main())

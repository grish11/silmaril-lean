#!/usr/bin/env python3
"""Per-function translation-validation contexts of the corpus, and their coverage matrix.

    python3 -I corpus/tv.py [--check]

Reads, per object and architecture, the function map (`corpus/<pkg>/funcmap/<arch>/<obj>.json`,
tool-derived from the object's debug twin by twin.sh) and the kernel-checked structural
decomposition (`Silmaril/Elf/Staged/Corpus/<Pkg>/<Arch>/<Obj>/{Defs,Decomp}.lean`). Writes

* `corpus/<pkg>/tv/<arch>/<obj>.tsv`: one **context** per function symbol of `.text`: the binary
  side (symbol, address, size, whether it is a piece of the proved decomposition, which theorem),
  the source binding (translation unit, C name, declaration line, linkage) when the DWARF of the
  debug twin gives one, the C signature classes (parameters, result, variadic), the direct
  callees and the number of indirect calls (DWARF call sites), and the **blockers**: what must
  exist before a contextual C-to-ELF refinement statement can be instantiated for it;
* `corpus/TV.md`: the coverage matrix (counts per object, architecture and blocker).

Nothing here is a translation-validation statement. A context is the data a statement needs; the
blockers say why none is instantiated (see corpus/TV.md, "Blockers").
"""
import json, re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BLOCKERS = {
    "isa-semantics": "no ISA semantics for the target in silmaril-lean (AArch64)",
    "no-source-binding": "no C function: start-up/runtime code without DWARF, assembly, or an ambiguous name",
    "compiler-clone": "a compiler-generated clone (.part/.isra/.constprop/.cold): no C function of its own; validating it needs the clone's specialised contract",
    "not-in-decomposition": "the symbol is not a piece of the proved structural decomposition (alias of another piece, overlapping extent, or outside .text)",
    "signature-unknown": "bound by the line table only (no subprogram DIE, e.g. macro-generated functions): translation unit known, C signature and callees not derived",
    "frontend-rejected": "the Lean port of the Cerberus frontend rejects the function's translation unit as the pinned build preprocessed it (corpus/<pkg>/frontend/<arch>.tsv; mostly GNU extensions in glibc and gcc headers), so no Core semantics can be bound to its actual text",
    "core-binding": "the frontend accepts the translation unit (typed Ail), but its elaboration to Core and the function's CFn are not generated yet, so no statement is instantiated",
    "frontend-unmatched": "no preprocessed unit of the frontend run could be matched to the function's translation unit",
    "memory-correspondence": "pointer or aggregate parameters/result: needs a C-object to machine-memory correspondence (absent)",
    "float-abi": "floating-point parameters/result: outside the System V INTEGER fragment of the existing ABI shapes",
    "variadic": "variadic function: no va_list ABI model",
    "callee-contracts": "direct calls: needs callee contracts (none stated)",
    "indirect-calls": "indirect calls: needs a call-target contract",
    "globals": "the globals the function reads or writes are not derived (needs code decoding); context incomplete",
}


def camel(s):
    out = "".join(p[:1].upper() + p[1:] for p in re.split(r"[^A-Za-z0-9]+", s) if p)
    return ("N" + out) if out[:1].isdigit() else out


def decomposition(mod_dir):
    """value -> (theorem, k, i) for the function pieces of the proved decompositions."""
    defs = (mod_dir / "Defs.lean").read_text()
    val = {}
    for m in re.finditer(r"^def s(\d+)_(\d+) : ObjectSymbol := ⟨⟨\d+, \d+, \d+, (\d+), (\d+), (\d+)⟩", defs, re.M):
        val[(int(m[1]), int(m[2]))] = (int(m[3]), int(m[4]), int(m[5]))
    dec = (mod_dir / "Decomp.lean").read_text()
    out = {}
    for sec in re.findall(r"^theorem decomp_(\d+) :", dec, re.M):
        for m in re.finditer(rf"^def pieces_{sec}_\d+ : List Piece :=\n((?:.*\n)*?)\n", dec, re.M):
            for k, i in re.findall(r"\.fn (\d+) (\d+) s", m[1]):
                shndx, v, z = val[(int(k), int(i))]
                out[v] = (f"decomp_{sec}", int(k), int(i), z)
    return out


def clean_tu(t):
    return re.sub(r"^\(indirect (line )?string, offset: (0x)?[0-9a-f]+\):\s*", "", t or "")


def unit_index(units):
    """stem -> [(unit, status)]: every suffix of a unit's file stem after `-`, `_` or the start."""
    idx = {}
    for u, st in units:
        name = Path(u).with_suffix("").name
        for m in re.finditer(r"(?:^|[-_])(?=(.+)$)", name):
            idx.setdefault(m.group(1), []).append((u, st))
    return idx


def frontend_status(units, tu):
    """The frontend's answer for the unit the build preprocessed from `tu` (a source path)."""
    if not units: return "frontend-unmatched"
    tu = clean_tu(tu)
    stem = Path(tu).stem
    parts = [x for x in Path(tu).parent.parts if x not in (".", "")]
    cand = list(dict.fromkeys(units.get(stem, [])))
    if len(cand) > 1 and parts:
        cand = [(u, st) for u, st in cand if str(Path(u).parent).endswith(parts[-1])] or cand
    # several units of one source (OpenSSL compiles libcrypto once for the static and once for the
    # shared library): one answer when they all agree
    if not cand or len({st for _, st in cand}) != 1: return "frontend-unmatched"
    return "core-binding" if cand[0][1] == "accepted" else "frontend-rejected"


def blockers(arch, r, piece, fe="frontend-unmatched"):
    b = []
    if arch == "aarch64": b.append("isa-semantics")
    if piece is None: b.append("not-in-decomposition")
    if r["status"] == "clone": b.append("compiler-clone")
    elif r["status"] == "bound-line": b += [fe, "signature-unknown"]
    elif r["status"] != "bound": b.append("no-source-binding"); return b
    else:
        b.append(fe)
        kinds = set(r.get("params", [])) | {r.get("result", "void")}
        if kinds & {"ptr", "struct", "other"}: b.append("memory-correspondence")
        if "float" in kinds: b.append("float-abi")
        if r.get("variadic"): b.append("variadic")
        if r.get("callees"): b.append("callee-contracts")
        if r.get("indirect_calls"): b.append("indirect-calls")
    b.append("globals")
    return b


def main():
    check = "--check" in sys.argv
    files, matrix = {}, []
    totals = {k: 0 for k in BLOCKERS}
    tot_fn = tot_bound = tot_dec = tot_profile = tot_nocode = 0
    for fm in sorted((ROOT / "corpus").glob("*/funcmap/*/*.json")):
        pkg, arch, obj = fm.parts[-4], fm.parts[-2], fm.stem
        d = json.loads(fm.read_text())
        on = camel(obj) + ("Exe" if camel(obj) == camel(pkg) else "")
        mod = ROOT / "Silmaril/Elf/Staged/Corpus" / camel(pkg) / camel(arch) / on
        mname = "Silmaril.Elf.Staged.Corpus." + ".".join([camel(pkg), camel(arch), on])
        dec = decomposition(mod)
        fe_file = ROOT / "corpus" / pkg / "frontend" / f"{arch}.tsv"
        units = unit_index([tuple(l.split("\t")[:2]) for l in fe_file.read_text().splitlines() if l and not l.startswith("#")] if fe_file.exists() else [])
        ctxs, cnt = [], {k: 0 for k in BLOCKERS}
        nbound = nprofile = nalias = 0
        groups = {}
        for r in d["functions"]:
            groups.setdefault((r["value"], r["size"]), []).append(r)
        for g in groups.values():
            g.sort(key=lambda r: ({"GLOBAL": 0, "WEAK": 1}.get(r["bind"], 2), r["symbol"]))
        for r in d["functions"]:
            g = groups[(r["value"], r["size"])]
            piece = dec.get(r["value"]) if dec.get(r["value"], (0, 0, 0, -1))[3] == r["size"] else None
            role = "piece" if r is g[0] else "alias"
            nalias += role == "alias"
            bl = blockers(arch, r, piece, frontend_status(units, r.get("tu")) if r["status"] in ("bound", "bound-line") else None)
            for x in bl: cnt[x] += 1
            if r["status"] in ("bound", "bound-line"): nbound += 1
            profile = r["status"] == "bound" and not (set(bl) - {"isa-semantics", "frontend-rejected", "core-binding", "frontend-unmatched", "globals"})
            nprofile += profile
            ctxs.append({
                "symbol": r["symbol"], "value": r["value"], "size": r["size"], "binding": r["bind"],
                "decomposition": {"theorem": f"{mname}.{piece[0]}", "extent_of_entry": [piece[1], piece[2]], "role": role,
                                  "same_extent": [x["symbol"] for x in g if x is not r]} if piece else None,
                "source": {k: r.get(k) for k in ("tu", "c_name", "decl_line", "external", "first_line", "via")} if r["status"] in ("bound", "bound-line", "clone") else None,
                "signature": {k: r.get(k) for k in ("params", "result", "variadic", "prototyped")} if r["status"] == "bound" else None,
                "callees": r.get("callees", []), "indirect_calls": r.get("indirect_calls", 0),
                "target": {"x86_64": "x86-64 System V (AMD64 psABI)", "aarch64": "AArch64 AAPCS64"}[arch],
                "int_profile": profile, "blockers": bl})
        # one line per function: the binary side, the decomposition role and the blockers; the source
        # binding and signature are in the function map (funcmap/), not repeated here
        lines = ["# " + json.dumps({"package": pkg, "arch": arch, "object": obj, "decomposition_module": mname + ".Decomp",
                                     "twin_code_identical": d["twin_code_identical"],
                                     "twin_symbols_identical": d.get("twin_symbols_identical", d["twin_code_identical"]),
                                     "twin_text_bytes_differing": d.get("twin_text_bytes_differing", 0),
                                     "function_map": f"corpus/{pkg}/funcmap/{arch}/{obj}.json"}, sort_keys=True),
                 "# symbol\tvalue\tsize\tdecomposition (theorem, role)\tc_name\ttu\tint_profile\tblockers"]
        for c in ctxs:
            dd = c["decomposition"]
            src = c["source"] or {}
            lines.append("\t".join([c["symbol"], hex(c["value"]), str(c["size"]),
                                    f"{dd['theorem'].rsplit('.', 1)[-1]} {dd['role']}" if dd else "-",
                                    str(src.get("c_name") or "-"), clean_tu(src.get("tu")) or "-",
                                    "yes" if c["int_profile"] else "no", ",".join(c["blockers"])]))
        files[f"corpus/{pkg}/tv/{arch}/{obj}.tsv"] = "\n".join(lines) + "\n"
        twin = "yes" if d["twin_code_identical"] else (f"symbols yes; {d.get('twin_text_bytes_differing')} `.text` bytes differ (RIP-relative data displacements)" if d.get("twin_symbols_identical") else "**NO**")
        n = len(ctxs)
        tot_fn += n; tot_bound += nbound; tot_dec += sum(1 for c in ctxs if c["decomposition"]); tot_profile += nprofile
        tot_nocode += d["c_functions_without_code"]
        for k in BLOCKERS: totals[k] += cnt[k]
        matrix.append(f"| {pkg} | {arch} | `{obj}` | {n} | {sum(1 for c in ctxs if c['decomposition'])} | {nbound} | {d['counts'].get('clone', 0)} | "
                      f"{d['counts'].get('no-dwarf', 0) + d['counts'].get('ambiguous', 0)} | {d['c_functions_without_code']} | {nprofile} | "
                      + " | ".join(str(cnt[k]) for k in ["memory-correspondence", "float-abi", "variadic", "callee-contracts", "indirect-calls"]) + f" | {nalias} | {twin} |")
    md = """# Translation validation of the corpus: contexts, coverage and blockers

GENERATED by `corpus/tv.py`; do not edit.

**Status: no contextual C-to-ELF translation-validation statement is instantiated yet.**
Instantiated statements: **0**. Proved: **0**. Each `.text` function symbol has a **context**
(`corpus/<pkg>/tv/<arch>/<obj>.tsv`, with the source side in `corpus/<pkg>/funcmap/<arch>/<obj>.json`): the data a statement needs, plus the **blockers** that say
why none exists yet. This file counts them. A context is not a statement.

* *functions*: defined function symbols of `.text` with nonzero size (the matrix covers every one).
* *in decomposition*: pieces of the kernel-checked structural decomposition
  (`Silmaril.Elf.Staged.Decomp`). That decomposition is a symbol-table tiling with explicit gaps: it is
  not instruction decoding, control flow or semantics.
* *bound*: the debug twin's DWARF gives the symbol a C function (or, with `signature-unknown`, only the line table places it in a translation unit): translation unit, C name, declaration
  line and linkage. The twin's `.text` and function symbols are checked byte-identical to the pinned
  object (*twin = pinned*). The binding is tool-derived (binutils on the twin), not proved.
* *aliases*: symbols with the same extent as another symbol. They share that symbol's decomposition
  piece (`role: alias` in the context); the decomposition lists the extent once.
* *twin = pinned*: the debug twin has the pinned object's function symbols (name, value, size). Its
  `.text` is byte-identical except where noted. In the one exception (OpenSSL `libcrypto.so.3`, x86-64),
  `-g` moved some read-only data (`__func__` strings), so RIP-relative displacements differ. The function
  extents, and hence the mapping, are unchanged.
* *clones*: compiler-generated (`.part`, `.isra`, `.constprop`, `.cold`).
* *no source*: start-up/runtime code (`_start`, libgcc, crt), assembly, or ambiguous names.
* *C without code*: C functions of the translation units with no code of their own (inlined
  everywhere or eliminated). They have no ELF function to validate.
* *int profile*: bound functions whose only blockers are the frontend or Core binding, the ISA (AArch64) and
  globals. That means INTEGER-class parameters and result, not variadic, no calls. These fall in the
  profile of the existing `silmaril.shapes.c.compiles_to.open9` shape, once the frontend binds their
  Core (x86-64 only).

## Blockers

| blocker | meaning | functions |
|---|---|---|
""" + "\n".join(f"| `{k}` | {v} | {totals[k]} |" for k, v in BLOCKERS.items()) + f"""

Totals: {tot_fn} functions, {tot_dec} in decompositions, {tot_bound} bound to C, {tot_profile} in the int profile,
{tot_nocode} C functions without code.

## What a statement will say (when instantiated)

For one bound x86-64 function in its context: the C function, given by its actual translation unit
through the Lean Cerberus frontend and elaborator (preprocessing by the pinned gcc as a stated trusted
step), has Cerberus Core semantics. The ELF function is the proved decomposition piece, whose bytes are
the file's. It is placed under the System V AMD64 ABI, and the stated callee contracts and global-memory
correspondence hold. Then, for every ABI-related pair of entry states on which the Core run is safe,
the x86 machine run (Open9) refines it: it returns only results the Core run may return, with the
callee-saved registers and the stack discipline preserved. The non-vacuity obligations (a safe entry
exists, the correspondence is inhabited) are separate problems. On AArch64 the same context is kept,
but the statement cannot be instantiated: silmaril-lean has no AArch64 ISA semantics.

## Matrix

| package | arch | object | functions | in decomposition | bound | clones | no source | C without code | int profile | memory | float | variadic | callees | indirect | aliases | twin = pinned |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
""" + "\n".join(matrix) + "\n"
    files["corpus/TV.md"] = md
    changed = []
    for p, t in files.items():
        f = ROOT / p
        if not f.exists() or f.read_text() != t:
            changed.append(p)
            if not check:
                f.parent.mkdir(parents=True, exist_ok=True); f.write_text(t)
    if check and changed: sys.exit("tv: out of date: " + ", ".join(changed[:10]))
    print(f"tv: {tot_fn} functions, {tot_bound} bound, {tot_profile} int profile; {len(changed)} files {'stale' if check else 'written'}")


if __name__ == "__main__":
    main()

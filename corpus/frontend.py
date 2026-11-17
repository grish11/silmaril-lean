#!/usr/bin/env python3
"""Run silmaril-lean's Lean port of the Cerberus frontend on every preprocessed translation unit.

    python3 -I corpus/frontend.py PPDIR [--jobs N] [--timeout S]

PPDIR is pp.sh's output: PPDIR/<pkg>/<arch>/pp/<path>.i, the translation units exactly as the
pinned build preprocessed them (gcc -save-temps). For each, `cerb-lean parse --level tail` (built
by `lake build cerb-lean`) either produces the typed Ail document or fails. The result, per unit,
goes to `corpus/<pkg>/frontend/<arch>.tsv`: unit, status (accepted / rejected / timeout), seconds,
and the first line of the error. Accepted means the frontend reaches typed Ail; it is not
elaboration to Core, and it is not a statement about any function.
"""
import concurrent.futures as cf, os, subprocess, sys, time
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
EXE = ROOT / ".lake/build/bin/cerb-lean"
pp = Path(sys.argv[1])
jobs = int(sys.argv[sys.argv.index("--jobs") + 1]) if "--jobs" in sys.argv else 6
tmo = int(sys.argv[sys.argv.index("--timeout") + 1]) if "--timeout" in sys.argv else 300

def run(i):
    t0 = time.time()
    try:
        r = subprocess.run([str(EXE), "parse", "--level", "tail", str(i)], capture_output=True, text=True, timeout=tmo, errors="replace")
        dt = time.time() - t0
        ok = r.returncode == 0 and r.stdout.startswith("($document_tail")
        err = "" if ok else (r.stderr.strip() or r.stdout.strip()[:300]).splitlines()[0][:300] if (r.stderr.strip() or r.stdout.strip()) else f"exit {r.returncode}"
        return ("accepted" if ok else "rejected", dt, err.replace("\t", " ").replace(str(i), "<unit>"))
    except subprocess.TimeoutExpired:
        return ("timeout", time.time() - t0, f"no answer in {tmo} s")

for pkgdir in sorted(p for p in pp.iterdir() if p.is_dir()):
    for archdir in sorted(p for p in pkgdir.iterdir() if p.is_dir()):
        units = sorted((archdir / "pp").rglob("*.i"))
        if not units: continue
        with cf.ThreadPoolExecutor(jobs) as ex:
            res = list(ex.map(run, units))
        out = ROOT / "corpus" / pkgdir.name / "frontend" / f"{archdir.name}.tsv"
        out.parent.mkdir(parents=True, exist_ok=True)
        rows = [f"{u.relative_to(archdir / 'pp')}\t{s}\t{dt:.1f}\t{e}" for u, (s, dt, e) in zip(units, res)]
        out.write_text("# unit\tstatus\tseconds\tfirst error\n" + "\n".join(rows) + "\n")
        n = {k: sum(1 for s, _, _ in res if s == k) for k in ("accepted", "rejected", "timeout")}
        print(f"{pkgdir.name}/{archdir.name}: {len(units)} units, {n}", flush=True)

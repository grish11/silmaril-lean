#!/usr/bin/env python3
"""Time `decide +kernel` of one native-interpreter run on a module with `pages` memory pages.

Usage (from the repository root, after `lake build Silmaril.Wasm.Interp.MemExample.Defs`):
    python3 -I benchmarks/native-memory-kernel/bench.py 0 1

For each page count it writes a Lean file that declares `memMod` with that many pages
(otherwise identical to `Silmaril.Wasm.Interp.MemExample.memMod`) and checks by kernel
evaluation that `f(7)` (store 7 at address 0, load it back) has the expected behaviour:
`traps` for 0 pages, `returns [7]` otherwise. It prints one TSV row per case:
pages, expected, seconds, status.
"""
import os, subprocess, sys, tempfile, time

TEMPLATE = r'''
import Silmaril.Wasm.Interp.MemExample.Defs
open Silmaril.Wasm Silmaril.Wasm.Interp.MemExample Silmaril.Wasm.Execution.Core
set_option maxRecDepth 100000
def benchMod : Module := {{ memMod with memories := [⟨.i32, ⟨{pages}, none⟩⟩] }}
def benchStore : Store Empty :=
  ((prepare? evalConst? ({{}} : Store Empty) benchMod []).getD (⟨{{}}, {{}}, []⟩, none)).1.store
example : ((Binaryen.invokeRun 20 benchStore 0 [Val.i32 7]).bind fun r => Binaryen.flowBeh r.2) =
    some {expected} := by decide +kernel
'''

def main():
    pages = [int(a) for a in sys.argv[1:]] or [0, 1]
    print("pages\texpected\tseconds\tstatus")
    for p in pages:
        expected = ".traps" if p == 0 else "(.returns [Val.i32 7])"
        with tempfile.TemporaryDirectory() as d:
            path = os.path.join(d, "Bench.lean")
            with open(path, "w") as fh:
                fh.write(TEMPLATE.format(pages=p, expected=expected))
            t0 = time.time()
            try:
                r = subprocess.run(["lake", "env", "lean", path], capture_output=True, text=True,
                                   timeout=900)
                out = (r.stdout + r.stderr).strip().replace(d, "<tmp>")
                status = "ok" if r.returncode == 0 else ("deterministic timeout"
                    if "deterministic timeout" in out else "error: " + out.splitlines()[0])
            except subprocess.TimeoutExpired:
                status = "script timeout (900 s)"
            print(f"{p}\t{expected}\t{time.time() - t0:.2f}\t{status}", flush=True)

if __name__ == "__main__":
    main()

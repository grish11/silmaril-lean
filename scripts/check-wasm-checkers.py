#!/usr/bin/env python3
"""Check that each verified Wasm binary file holds exactly the bytes its Lean module states.

For each pair below, the `def bytes` literal of the Lean module (the bytes its theorems
`encodeModule_eq` / `decode_bytes` are about) must equal the file, byte for byte. The Lean side is
checked by the Lean build; this compares texts only (docs/projects/wasm-catalog.md, section 2).
"""
from __future__ import annotations

import hashlib
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
PAIRS = [
    ("Silmaril/Wasm/Examples/LRAT/Bytes/Defs.lean", "examples/wasm-checkers/lrat.wasm"),
    ("Silmaril/Wasm/Examples/Farkas/Bytes/Defs.lean", "examples/wasm-checkers/farkas.wasm"),
    ("Silmaril/Wasm/Examples/MemberCheck/Defs.lean", "examples/wasm-acceptors/member_check.wasm"),
    ("Silmaril/Wasm/Examples/EmptyCheck/Defs.lean", "examples/wasm-acceptors/empty_check.wasm"),
    ("Silmaril/Wasm/Examples/RustAdder/Defs.lean", "examples/wasm-demos/rust-adder/wasm/adder.wasm"),
    ("Silmaril/Wasm/Examples/CAdder/Defs.lean", "examples/wasm-demos/c-adder/wasm/adder.wasm"),
    ("Silmaril/Wasm/Examples/AsAdder/Defs.lean", "examples/wasm-demos/as-adder/wasm/adder.wasm"),
]


def lean_bytes(text: str) -> bytes | None:
    m = re.search(r"def bytes\s*:[^=]*:=\s*(?:⟨#)?\[(.*?)\]", text, re.S)
    if not m:
        return None
    nums = re.findall(r"0x[0-9a-fA-F]+|\d+", m.group(1))
    return bytes(int(n, 0) for n in nums)


def main() -> int:
    bad = 0
    for lean, wasm in PAIRS:
        lb = lean_bytes((ROOT / lean).read_text())
        fb = (ROOT / wasm).read_bytes()
        if lb is None:
            print(f"error: no `def bytes` literal in {lean}", file=sys.stderr)
            bad += 1
        elif lb != fb:
            print(f"error: {wasm} ({len(fb)} bytes) differs from `bytes` of {lean} ({len(lb)} bytes)",
                  file=sys.stderr)
            bad += 1
        else:
            print(f"ok {wasm}: {len(fb)} bytes, sha256 {hashlib.sha256(fb).hexdigest()}")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())

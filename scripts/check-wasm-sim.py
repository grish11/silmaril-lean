#!/usr/bin/env python3
"""Check the files of examples/wasm-sim against what Lean quotes (docs/projects/wasm-sim.md).

* `Silmaril/Sim/X86Real/Defs.lean` quotes `x86-g.wat` and `x86-m.wat` verbatim
  (the blocks between `-- BEGIN GENERATED: x86-<v>.wat` and `-- END GENERATED`);
* `Silmaril/Sim/X86/Max2/Defs.lean` quotes `problems/max2.wat` (from `(module` on), and
  `Silmaril/Sim/Reduce/Toy/Dbl/Defs.lean` quotes `reduce/toy/insn/dbl.wat` (`wat3!`);
* the `.text` section of `reduce/toy/toy.elf` is the `code` literal of
  `Silmaril/Sim/Reduce/Toy/Defs.lean`, the bytes the toy's theorems are about.

Texts only; no Rust build needed (`wasm-sim lean-quote --check` does the first with the tool).
"""
from __future__ import annotations

import pathlib
import re
import struct
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
EX = ROOT / "examples" / "wasm-sim"
errors: list[str] = []


def quote(lean: pathlib.Path, decl: str) -> str | None:
    m = re.search(r"def\s+" + re.escape(decl) + r"\b[^\n]*?:=\s*wat3!\s*r#\"(.*?)\"#", lean.read_text(), re.S)
    return m.group(1) if m else None


def from_module(text: str) -> str:
    """The text from the first line starting `(module` (leading header comments are not quoted)."""
    i = text.find("\n(module")
    return text if text.startswith("(module") or i < 0 else text[i + 1:]


def same(what: str, quoted: str | None, path: pathlib.Path) -> None:
    if quoted is None:
        errors.append(f"{what}: no quotation found")
    elif quoted.strip() not in (path.read_text().strip(), from_module(path.read_text()).strip()):
        errors.append(f"{what} does not quote {path.relative_to(ROOT)} verbatim")
    else:
        print(f"ok {path.relative_to(ROOT)}: quoted by {what}")


def elf_text(path: pathlib.Path) -> bytes:
    b = path.read_bytes()
    assert b[:4] == b"\x7fELF" and b[4] == 2 and b[5] == 1, "expected ELF64 little-endian"
    shoff, = struct.unpack_from("<Q", b, 0x28)
    shentsize, shnum, shstrndx = struct.unpack_from("<HHH", b, 0x3A)
    def sh(i: int):
        return struct.unpack_from("<IIQQQQIIQQ", b, shoff + i * shentsize)
    stroff = sh(shstrndx)[4]
    for i in range(shnum):
        name, _, _, _, off, size, *_ = sh(i)
        end = b.index(b"\0", stroff + name)
        if b[stroff + name:end] == b".text":
            return b[off:off + size]
    raise ValueError("no .text")


def main() -> int:
    real = (ROOT / "Silmaril/Sim/X86Real/Defs.lean").read_text()
    for v in "gm":
        m = re.search(r"-- BEGIN GENERATED: x86-" + v + r"\.wat\n.*?r#\"\n(.*?)\"#\n.*?-- END GENERATED", real, re.S)
        same(f"X86Real sim{v.upper()}", m.group(1) if m else None, EX / "x86" / f"x86-{v}.wat")
    same("Sim.X86.Max2.max2M", quote(ROOT / "Silmaril/Sim/X86/Max2/Defs.lean", "max2M"),
         EX / "x86/problems/max2.wat")
    same("Sim.Reduce.Toy.Dbl.dblModule", quote(ROOT / "Silmaril/Sim/Reduce/Toy/Dbl/Defs.lean", "dblModule"),
         EX / "reduce/toy/insn/dbl.wat")
    toy = (ROOT / "Silmaril/Sim/Reduce/Toy/Defs.lean").read_text()
    m = re.search(r"def code : List Byte :=\s*\[(.*?)\]", toy, re.S)
    code = bytes(int(x, 16) for x in re.findall(r"0x([0-9a-fA-F]+)", m.group(1))) if m else None
    text = elf_text(EX / "reduce/toy/toy.elf")
    if code != text:
        errors.append(f"toy.elf .text ({len(text)} bytes) differs from Sim.Reduce.Toy.code")
    else:
        print(f"ok examples/wasm-sim/reduce/toy/toy.elf: .text is Sim.Reduce.Toy.code ({len(text)} bytes)")
    for e in errors:
        print(f"error: {e}", file=sys.stderr)
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())

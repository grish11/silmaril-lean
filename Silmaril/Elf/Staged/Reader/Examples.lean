module

public import Silmaril.Elf.Staged.Pinned.HelloGcc.Thms
public import Silmaril.Prelude.Bytes.Write.Defs

/-! # The per-part reader: what it refuses (kernel-checked)

The windows of a part are binding: a run of a reader on a window narrower than its footprint, on
another part's window, or against a different claimed value fails, so a theorem cannot be
re-associated with other bytes by renaming it or by editing explorer metadata. Truncated and
malformed files, and the ELF variants the specification does not support (ELFCLASS32,
big-endian), are refused rather than misread. All on `examples/dyn/pinned/hello-gcc`
(`Silmaril.Elf.Staged.Pinned.HelloGcc`) or small literal files; every `decide +kernel` here runs
on kernel bytes.
-/

@[expose] public section

namespace Silmaril.Elf.Staged.Reader.Examples

open Silmaril.Elf Silmaril.Elf.Staged Silmaril.Elf.Staged.Reader
open Silmaril.Elf.Staged.Pinned.HelloGcc (K hdr ph0 ph1 L)

/-! ## Windows are binding -/

/-- The header with its last byte outside the window is refused. -/
example : Parse.header.run (window [⟨0, 63⟩] (kread K)) = none := by decide +kernel

/-- Program header 0 cannot be read from program header 1's bytes. -/
example : (Parse.phdr 64).run (window [⟨120, 56⟩] (kread K)) = none := by decide +kernel

/-- Program header 1's bytes do not hold program header 0. -/
example : (Parse.phdr 120).run (window [⟨120, 56⟩] (kread K)) ≠ some ph0 := by decide +kernel

/-- A different claimed entry point is refused. -/
example : Parse.header.run (window [⟨0, 64⟩] (kread K)) ≠ some { hdr with entry := 0 } := by
  decide +kernel

/-- The layout needs the section-name bytes: the header tables alone do not suffice. -/
example : readLayout.run (window [⟨0, 64⟩, ⟨64, 56 * 13⟩, ⟨13976, 64 * 31⟩] (kread K)) = none := by
  decide +kernel

/-! ## Truncated and malformed files -/

/-- A file shorter than the ELF header. -/
example : Parse.header.run (kread (K.slice 0 40)) = none := by decide +kernel

/-- The file cut just before its section header table (at `e_shoff = 13976`). -/
example : readLayout.run (kread (K.slice 0 13976)) = none := by decide +kernel

/-- A bad magic number. -/
example : Parse.header.run (kread (K.write 0 1 0x7e)) = none := by decide +kernel

/-- An unsupported `e_phentsize` (32-bit program headers are 32 bytes). -/
example : readLayout.run (kread (K.write 54 2 32)) = none := by decide +kernel

/-- No section header table (`e_shnum = 0`): the layout has no sections; program headers and
the loader's view are still read. -/
example : (readLayout.run (kread (K.write 60 2 0))).map (·.sections.length) = some 0 := by
  decide +kernel

/-! ## Unsupported variants are refused, not misread -/

/-- `ELFCLASS32`. -/
example : Parse.header.run (kread (K.write 4 1 1)) = none := by decide +kernel

/-- `ELFDATA2MSB` (big-endian). -/
example : Parse.header.run (kread (K.write 5 1 2)) = none := by decide +kernel

/-- Any `e_machine` is accepted: the reader is not specific to x86-64 (the header records it). -/
example : (Parse.header.run (kread (K.write 18 2 183))).map (·.machine) = some 183 := by
  decide +kernel

end Silmaril.Elf.Staged.Reader.Examples

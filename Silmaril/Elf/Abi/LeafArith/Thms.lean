module

public import Silmaril.Elf.Abi.LeafArith.Defs
public import Silmaril.Machine.Abi.Conformance.LeafArith.Thms
import Silmaril.Proofs.Elf.Abi.LeafArith

/-! # ABI conformance rows of `leaf-arith`: proved and open

PROVED (standard axioms), proofs in `Silmaril.Proofs.Elf.Abi.LeafArith`:

* `clamp_row`, `sat_row`: **the rows `silmaril.elf.abi.leaf_arith.clamp_i32` and
  `….sat_add_u32`**: the `.symtab` symbols name the functions at `0x4013a0` (19 bytes) and
  `0x401400` (29 bytes), the file maps the 181 code bytes at `0x401370` read-only executable, and
  the code conforms (`Machine.Abi.Conformance.LeafArith.clamp_conforms`, `sat_conforms`);
* `header_row`: **the row `silmaril.elf.abi.leaf_arith.arith_h`**: the coverage of `arith.h`
  is checked against the header, the nine `absent` declarations (`rt_write`, `memcpy`, …) are
  absent from the file's `.symtab`, and the two claimed functions are the rows above;
* `gcd_code`, `bswap_code`: the file facts of the open rows.

OPEN: `silmaril.elf.abi.leaf_arith.gcd_u32` and `….bswap32_manual`, from
`Task.gcd_conforms` and `Task.bswap_conforms` (`gcd_row_of`, `bswap_row_of`).
-/

@[expose] public section

namespace Silmaril.Elf.Abi.LeafArith

open Silmaril.Machine.Abi.Conformance.LeafArith (Task.gcd_conforms Task.bswap_conforms)

/-- **`clamp_i32` of the pinned `leaf-arith` conforms to the System V AMD64 psABI.** -/
@[solves "silmaril.elf.abi.leaf_arith.clamp_i32"]
theorem clamp_row : silmaril.elf.abi.leaf_arith.clamp_i32 :=
  Silmaril.Proofs.Elf.Abi.LeafArith.clamp_row

/-- **`sat_add_u32` of the pinned `leaf-arith` conforms to the System V AMD64 psABI.** -/
@[solves "silmaril.elf.abi.leaf_arith.sat_add_u32"]
theorem sat_row : silmaril.elf.abi.leaf_arith.sat_add_u32 :=
  Silmaril.Proofs.Elf.Abi.LeafArith.sat_row

/-- **`leaf-arith` satisfies the claimed part of `arith.h`.** -/
@[solves "silmaril.elf.abi.leaf_arith.arith_h"]
theorem header_row : silmaril.elf.abi.leaf_arith.arith_h :=
  Silmaril.Proofs.Elf.Abi.LeafArith.header_row

theorem gcd_row_of (h : Task.gcd_conforms) : silmaril.elf.abi.leaf_arith.gcd_u32 :=
  ⟨Silmaril.Proofs.Elf.Abi.LeafArith.gcd_code, h⟩

theorem bswap_row_of (h : Task.bswap_conforms) : silmaril.elf.abi.leaf_arith.bswap32_manual :=
  ⟨Silmaril.Proofs.Elf.Abi.LeafArith.bswap_code, h⟩

end Silmaril.Elf.Abi.LeafArith

end

silmaril group silmaril.abi
  (title := "ABI conformance: the shapes and the leaf-arith rows")
  (children := [silmaril.shapes.abi.conforms, silmaril.shapes.abi.conforms.sysv_int_open,
    silmaril.shapes.abi.conforms.sysv_int_open9, silmaril.shapes.abi.header_sat,
    silmaril.shapes.abi.header_sat.sysv_int_open, silmaril.shapes.elf.abi_conforms,
    silmaril.shapes.elf.abi_conforms.sysv_int_open, silmaril.shapes.elf.abi_conforms.sysv_int_open9,
    silmaril.shapes.elf.abi_header_sat, silmaril.shapes.elf.abi_header_sat.sysv_int_open,
    silmaril.elf.abi.leaf_arith.clamp_i32, silmaril.elf.abi.leaf_arith.sat_add_u32,
    silmaril.elf.abi.leaf_arith.gcd_u32, silmaril.elf.abi.leaf_arith.bswap32_manual,
    silmaril.elf.abi.leaf_arith.arith_h])

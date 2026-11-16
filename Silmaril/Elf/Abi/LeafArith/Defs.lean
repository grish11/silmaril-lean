module

public import Silmaril.Elf.Abi.Defs
public import Silmaril.Elf.Staged.Pinned.LeafArith.Bytes
public import Silmaril.Machine.Abi.Conformance.LeafArith.Defs

/-! # ABI conformance rows: `arith.h` and the pinned `leaf-arith`

The rows of `silmaril.shapes.elf.abi_conforms.sysv_int_open` for the functions of
`examples/elf-ladder/01-leaf-arith/arith.h` in the pinned executable
`examples/elf-ladder/01-leaf-arith/pinned/leaf-arith` (gcc 13.3 `-O2`, static, `.symtab`), and
the header row (`silmaril.shapes.elf.abi_header_sat.sysv_int_open`). The header, code, specs and
coverage are `Silmaril.Machine.Abi.Conformance.LeafArith`; the file is the per-part reader's
`Silmaril.Elf.Staged.Pinned.LeafArith.F` (its `include_bytes`).

| row | function | status |
| --- | --- | --- |
| `silmaril.elf.abi.leaf_arith.clamp_i32` | `int clamp_i32(int, int, int)` | proved |
| `silmaril.elf.abi.leaf_arith.sat_add_u32` | `u32 sat_add_u32(u32, u32)` | proved |
| `silmaril.elf.abi.leaf_arith.gcd_u32` | `u32 gcd_u32(u32, u32)` | open |
| `silmaril.elf.abi.leaf_arith.bswap32_manual` | `u32 bswap32_manual(u32)` | open |
| `silmaril.elf.abi.leaf_arith.arith_h` | the header: the two proved functions claimed, the rest excluded | proved |
-/

@[expose] public section

namespace Silmaril.Elf.Abi.LeafArith

/-- The `.symtab` selector of a name. -/
def sel (f : String) : Silmaril.Elf.Sel := .sym (Silmaril.Elf.nameOf f)

end Silmaril.Elf.Abi.LeafArith

end

silmaril instance silmaril.elf.abi.leaf_arith.clamp_i32
    (title := "leaf-arith clamp_i32 conforms to the System V AMD64 psABI as arith.h declares it") :=
  silmaril.shapes.elf.abi_conforms.sysv_int_open (mode := .total)
    (hdr := Silmaril.Machine.Abi.Conformance.LeafArith.hdr) (f := "clamp_i32")
    (p := Silmaril.Machine.Abi.Conformance.LeafArith.clampProto) (F := Silmaril.Elf.Staged.Pinned.LeafArith.F)
    (sel := Silmaril.Elf.Abi.LeafArith.sel "clamp_i32")
    (c := Silmaril.Machine.Abi.Conformance.LeafArith.clampCode) (frame := 0)
    (S := Silmaril.Machine.Abi.Conformance.LeafArith.clampS)
silmaril instance silmaril.elf.abi.leaf_arith.sat_add_u32
    (title := "leaf-arith sat_add_u32 conforms to the System V AMD64 psABI as arith.h declares it") :=
  silmaril.shapes.elf.abi_conforms.sysv_int_open (mode := .total)
    (hdr := Silmaril.Machine.Abi.Conformance.LeafArith.hdr) (f := "sat_add_u32")
    (p := Silmaril.Machine.Abi.Conformance.LeafArith.satProto) (F := Silmaril.Elf.Staged.Pinned.LeafArith.F)
    (sel := Silmaril.Elf.Abi.LeafArith.sel "sat_add_u32")
    (c := Silmaril.Machine.Abi.Conformance.LeafArith.satCode) (frame := 0)
    (S := Silmaril.Machine.Abi.Conformance.LeafArith.satS)
silmaril instance silmaril.elf.abi.leaf_arith.gcd_u32
    (title := "leaf-arith gcd_u32 conforms to the System V AMD64 psABI as arith.h declares it (open)") :=
  silmaril.shapes.elf.abi_conforms.sysv_int_open (mode := .total)
    (hdr := Silmaril.Machine.Abi.Conformance.LeafArith.hdr) (f := "gcd_u32")
    (p := Silmaril.Machine.Abi.Conformance.LeafArith.satProto) (F := Silmaril.Elf.Staged.Pinned.LeafArith.F)
    (sel := Silmaril.Elf.Abi.LeafArith.sel "gcd_u32")
    (c := Silmaril.Machine.Abi.Conformance.LeafArith.region 0 37) (frame := 0)
    (S := Silmaril.Machine.Abi.Conformance.LeafArith.gcdS)
silmaril instance silmaril.elf.abi.leaf_arith.bswap32_manual
    (title := "leaf-arith bswap32_manual conforms to the System V AMD64 psABI as arith.h declares it (open)") :=
  silmaril.shapes.elf.abi_conforms.sysv_int_open (mode := .total)
    (hdr := Silmaril.Machine.Abi.Conformance.LeafArith.hdr) (f := "bswap32_manual")
    (p := Silmaril.Machine.Abi.Conformance.LeafArith.bswapProto)
    (F := Silmaril.Elf.Staged.Pinned.LeafArith.F)
    (sel := Silmaril.Elf.Abi.LeafArith.sel "bswap32_manual")
    (c := Silmaril.Machine.Abi.Conformance.LeafArith.region 0xb0 5) (frame := 0)
    (S := Silmaril.Machine.Abi.Conformance.LeafArith.bswapS)
silmaril instance silmaril.elf.abi.leaf_arith.arith_h
    (title := "leaf-arith satisfies the claimed part of arith.h under the System V AMD64 psABI") :=
  silmaril.shapes.elf.abi_header_sat.sysv_int_open
    (hdr := Silmaril.Machine.Abi.Conformance.LeafArith.hdr)
    (cov := Silmaril.Machine.Abi.Conformance.LeafArith.coverage)
    (F := Silmaril.Elf.Staged.Pinned.LeafArith.F) (sel := Silmaril.Elf.Abi.LeafArith.sel)
    (impl := Silmaril.Machine.Abi.Conformance.LeafArith.impl)

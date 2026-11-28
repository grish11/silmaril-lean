module

public import Silmaril.Machine.AArch64.Memory.Image.Defs

/-!
# AArch64 memory: example memories

The memories of the worked examples in `Silmaril.Machine.AArch64.Memory.Examples.Thms`.
Each is given by its regions and by an image (`Silmaril.Machine.AArch64.Memory.Image.Defs`),
so that the facts about it are checked by the kernel.

* `memory`: four regions of 16 bytes, one for each of execute only, read only, write only,
  and read and write. Every region holds bytes, and the image has four bytes on each side of
  the executable region that no region maps.
* `tiny`: one region of eight bytes in which only four bytes have a value.
* `top`: one region that reaches the top of the address space, and continues past it as a
  set of natural numbers.
* `adjacent`: three regions of four bytes that touch: read only, read only, write only.

The memories are `abbrev`s, so that the rewriting step of the recipe sees the image.
-/

@[expose] public section

namespace Silmaril.Machine.AArch64.Memory.Examples

open Silmaril.Process (Memory Region)

/-! ## The example memory -/

/-- Four regions of 16 bytes: execute only at `0x1000`, read only at `0x2000`, write only at
`0x3000`, read and write at `0x4000`. Nothing is mapped anywhere else. -/
def regions : List Region :=
  [ { base := 0x1000, size := 16,
      permissions := { read := false, write := false, execute := true } },
    { base := 0x2000, size := 16,
      permissions := { read := true, write := false, execute := false } },
    { base := 0x3000, size := 16,
      permissions := { read := false, write := true, execute := false } },
    { base := 0x4000, size := 16,
      permissions := { read := true, write := true, execute := false } } ]

/-- The bytes of the example memory. Each region holds 16 bytes, and there are four more
bytes on each side of the executable region.

* `0x0FFC`: four bytes directly before the executable region, in no region.
* `0x1000`: four words. `11 22 33 44` is four different bytes, to show the byte order.
  `00 04 00 91` is the word `0x91000400` of `ADD X0, X0, #1`. `00 00 01 2B` is `0x2B010000`
  (`adds w0, w0, w1`) and `C0 03 5F D6` is `0xD65F03C0` (`ret`), both as listed in
  `tools/aarch64-difftest/fixtures/pinned/words.txt`.
* `0x1010`: four bytes directly after the executable region, in no region.
* `0x2000`: `11 22 … 88` and eight more bytes.
* `0x3000`: `30 31 … 3F`.
* `0x4000`: `40 41 … 4F`: the byte at `0x4000 + i` is `0x40 + i`. -/
def image : Image :=
  [ (0x0FFC, [0xD0, 0xD1, 0xD2, 0xD3]),
    (0x1000, [0x11, 0x22, 0x33, 0x44, 0x00, 0x04, 0x00, 0x91,
              0x00, 0x00, 0x01, 0x2B, 0xC0, 0x03, 0x5F, 0xD6]),
    (0x1010, [0xE0, 0xE1, 0xE2, 0xE3]),
    (0x2000, [0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88,
              0x99, 0xAA, 0xBB, 0xCC, 0xDD, 0xEE, 0xFF, 0x00]),
    (0x3000, [0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37,
              0x38, 0x39, 0x3A, 0x3B, 0x3C, 0x3D, 0x3E, 0x3F]),
    (0x4000, [0x40, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47,
              0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x4F]) ]

/-- The example memory. It is an `abbrev`, so that the rewriting step sees the image. -/
abbrev memory : Memory := Image.memory regions image

/-! ## A tiny memory: bytes without a value -/

/-- One region at address 0: eight bytes, readable, writable and executable. -/
def tinyRegions : List Region :=
  [ { base := 0, size := 8, permissions := { read := true, write := true, execute := true } } ]

/-- Four bytes at address 0. The bytes at 4, …, 7 are mapped and have no value. -/
def tinyImage : Image := [(0, [0x11, 0x22, 0x33, 0x44])]

/-- The tiny memory. -/
abbrev tiny : Memory := Image.memory tinyRegions tinyImage

/-! ## The top of the address space -/

/-- One region of 16 bytes with every permission, starting 8 bytes below `2^64`. As a set of
natural numbers it continues 8 bytes past the top of the address space. -/
def topRegions : List Region :=
  [ { base := 0xFFFFFFFFFFFFFFF8, size := 16,
      permissions := { read := true, write := true, execute := true } } ]

/-- Sixteen bytes from `2^64 - 8`: the image has bytes at `2^64` and above. -/
def topImage : Image :=
  [ (0xFFFFFFFFFFFFFFF8, [0xF8, 0xF9, 0xFA, 0xFB, 0xFC, 0xFD, 0xFE, 0xFF,
                          0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07]) ]

/-- The memory at the top of the address space. -/
abbrev top : Memory := Image.memory topRegions topImage

/-! ## Regions that touch -/

/-- Three regions of four bytes, one directly after the other: read only at `0x6000`, read
only at `0x6004`, write only at `0x6008`. -/
def adjacentRegions : List Region :=
  [ { base := 0x6000, size := 4,
      permissions := { read := true, write := false, execute := false } },
    { base := 0x6004, size := 4,
      permissions := { read := true, write := false, execute := false } },
    { base := 0x6008, size := 4,
      permissions := { read := false, write := true, execute := false } } ]

/-- Twelve bytes from `0x6000`: the byte at `0x6000 + i` is `0x60 + i`. All three regions
hold bytes. -/
def adjacentImage : Image :=
  [ (0x6000, [0x60, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x6A, 0x6B]) ]

/-- The memory of the three regions that touch. -/
abbrev adjacent : Memory := Image.memory adjacentRegions adjacentImage

end Silmaril.Machine.AArch64.Memory.Examples

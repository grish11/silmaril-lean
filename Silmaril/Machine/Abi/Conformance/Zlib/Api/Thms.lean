module

public import Silmaril.Machine.Abi.Conformance.Zlib.Api.Defs

/-! # The rest of zlib's checksum API: sanity theorems

Kernel computations that the specs mean what they say:

* `combine_example`: for one-byte strings the operator `x^8` (bit-reflected: `0x00800000`)
  combines `crc32(0, "a")` and `crc32(0, "b")` into `crc32(0, "ab")`, so `crc32CombineGenS`'s
  condition is met by zlib's operator, not vacuous;
* `multmodp_one`: `0x80000000` (the polynomial `1`, reflected) is `multmodp`'s identity on an
  example;
* `crcTableBytes_length`, `crcTable_first`: 1024 bytes, beginning with entries 0 and 1
  (`0x00000000`, `0x77073096`);
* `flagsLow_lp64`, `flagsLow_ilp32`: `zlibCompileFlags`' low byte is `0xa9` under the x86-64
  System V data model and `0x55` under i386's (32-bit `long` and pointers): the spec follows the
  data model.
-/

@[expose] public section

namespace Silmaril.Machine.Abi.Conformance.Zlib.Api

open Silmaril.X86.Ladder.ZlibChecksums (crc32 crcEntry)

theorem combine_example :
    multmodp 0x00800000#32 (crc32 0 [0x61]) ^^^ crc32 0 [0x62] = crc32 0 [0x61, 0x62] := by
  decide +kernel

theorem multmodp_one : multmodp 0x80000000#32 0x12345678#32 = 0x12345678#32 := by decide +kernel

theorem crcTableBytes_length : crcTableBytes.length = 1024 := by decide +kernel

theorem crcTable_first : crcTableBytes.take 8 = [0x00, 0x00, 0x00, 0x00, 0x96, 0x30, 0x07, 0x77] := by
  decide +kernel

theorem flagsLow_lp64 : flagsLow Silmaril.Data.Layout.sysvX86_64 = 0xa9 := by decide +kernel

theorem flagsLow_ilp32 : flagsLow Silmaril.Data.Layout.i386Ilp32 = 0x55 := by decide +kernel

end Silmaril.Machine.Abi.Conformance.Zlib.Api

end

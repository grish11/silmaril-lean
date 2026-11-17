module

public import Silmaril.Machine.Abi.Conformance.Sse.Defs
public import Silmaril.Machine.Abi.Conformance.SysvScalar.Defs

/-!
# `long lrint(double)` as `cvtsd2si %xmm0, %rax; ret`, at any base

**The code** (`code base image`): the six bytes `F2 48 0F 2D C0 C3` (`cvtsd2si %xmm0, %rax;
ret`), glibc's x86-64 `lrint`/`llrint` (`sysdeps/x86_64/fpu/s_llrint.S`; the code of both
symbols of the pinned Debian 12 `libm.so.6`, `Silmaril.Elf.Abi.Libm`), at an arbitrary `base`,
entered at offset 0, extent 6, no data, with the image `image` of the object it belongs to.

**The prototype** (`proto`): one SSE-class `double` in XMM0, the INTEGER-class 64-bit result in
RAX: what `sysvScalar` lowers both `long lrint(double)` and `long long llrint(double)` to. The
row takes the header and the name as parameters with `Declares` as a hypothesis; the libm rows
discharge it from the pinned `math.h` import.

**The ABI**: `sysvScalar.defaultEnv`, by name (the default-environment subset: the entry
MXCSR's control bits are the default; masked exceptions are what makes `cvtsd2si` commit on
every operand).

**The IEEE domain** (`spec`, `toLong`): the result is `X86.Float.Scalar.toInt` of the **entry
MXCSR** on binary64 to a signed 64-bit integer in MXCSR's rounding direction:
`Numeric.Float`'s x86 SSE profile (`Profile.toInt`, IEEE 754-2019 §5.8 `convertToInteger` in
the current direction, DAZ as MXCSR sets it), with the profile's integer overflow result, the
integer indefinite `0x8000000000000000`, for NaN, infinite and out-of-range operands. C leaves
the out-of-range result unspecified (C17 7.12.9.5); the row states the one this code gives.

**The machine**: `Mach.str9L FeatureSet.baseline64 Features.sseExts`. The code has no VEX,
EVEX or BMI form (its first instruction is a `floatExt` lane form, and the run shows no tower form
needs a missing feature: `Str9L.towerMissing_of_listed_lane`), no `%fs` access (no thread-pointer
assumption), no memory access but the return address, and no `rdssp`; `ret` is modelled without
a shadow stack, so the row is about processes without user shadow stacks.
-/

@[expose] public section

namespace Silmaril.Machine.Abi.Conformance.Sse.Lrint

open Silmaril.Machine.SystemV.Abi
open Silmaril.Machine.Abi.Conformance

/-- `long lrint(double)` (and `long long llrint(double)`) in the scalar fragment. -/
def proto : Silmaril.Machine.Abi.SystemV.Scalar.Proto :=
  ⟨[.scalar .double], some (.scalar .int64), by decide⟩

/-- `cvtsd2si %xmm0, %rax; ret`. -/
def bytes : List Silmaril.X86.Byte := [0xF2, 0x48, 0x0F, 0x2D, 0xC0, 0xC3]

/-- The code at `base`, entered at offset 0, six bytes long, no data, the image `image`. -/
def code (base : Silmaril.X86.Word) (image : List (Silmaril.X86.Word × Nat)) : Code :=
  ⟨base, bytes, 0, 6, [], image⟩

/-- The ABI of the row: the default-environment subset of `sysvScalar`. -/
abbrev abi : AbiDef := sysvScalar.defaultEnv

/-- **binary64 to a signed 64-bit integer as `cvtsd2si` computes it under MXCSR `m`**:
`Numeric.Float`'s x86 SSE profile of `m`, rounding by MXCSR.RC. -/
def toLong (m : BitVec 32) (a : BitVec 64) : BitVec 64 :=
  (Silmaril.X86.Float.Scalar.toInt ⟨m⟩ .double .w64 (⟨m⟩ : Silmaril.X86.Float.MXCSR).rounding
    a).value

/-- **The C spec**: every call is admitted, nothing is written, and the result is `toLong` of
the entry MXCSR and the argument. -/
def spec : CallSpec abi.V proto where
  pre _ _ := True
  post a s r _ := r = toLong s.mxcsr a.1

/-- The machine of the row. -/
abbrev mach : Mach :=
  Mach.str9L Silmaril.X86.Features.FeatureSet.baseline64 Silmaril.X86.Features.sseExts

end Silmaril.Machine.Abi.Conformance.Sse.Lrint

end

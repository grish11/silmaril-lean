module

public import Silmaril.Machine.Abi.Conformance.Sse.Lrint.Defs
import Silmaril.Proofs.Machine.Abi.Conformance.Sse.Lrint

/-! # `long lrint(double)` as `cvtsd2si %xmm0, %rax; ret`: theorems

PROVED (standard axioms), proof in `Silmaril.Proofs.Machine.Abi.Conformance.Sse.Lrint`. The
statement is on a machine **model** (`Mach.str9L`), not on real x86: reading it about hardware
needs `Faithful` of a reference machine to `Mach.str9L` (`Conforms.onRef`), which is not proved.

* `conforms`: for any header `hdr` declaring `f` with a prototype `sysvScalar` lowers to
  `proto` (`long (double)`), **the six bytes conform at every `base`** with the code and the
  image below `2^47`, to `sysvScalar.defaultEnv` on `Mach.str9L FeatureSet.baseline64
  Features.sseExts`, in total mode, with no stack frame, no memory written, and the result
  `toLong s.mxcsr a` (which reads only the control bits, `toLong_mask`): binary64 to a signed
  64-bit integer by `Numeric.Float`'s x86 SSE profile of the entry MXCSR (rounding by MXCSR.RC; the integer indefinite for NaN, infinities and
  out-of-range operands). From every completion of every admitted call the call returns, with
  the callee-saved registers, DF clear, the MXCSR control bits and the x87 control word kept,
  the status flags of the conversion ORed in, and the integer in RAX. The libm rows
  (`Silmaril.Elf.Abi.Libm`) apply it to the code of `lrint` and `llrint` of the pinned
  `libm.so.6`.
-/

@[expose] public section

namespace Silmaril.Machine.Abi.Conformance.Sse.Lrint

theorem conforms {hdr : HeaderSrc} {f : String} (hd : Declares abi hdr f proto)
    {base : Silmaril.X86.Word} {image : List (Silmaril.X86.Word × Nat)}
    (hb : base.toNat + 6 ≤ 2 ^ 47) (hi : ∀ r ∈ image, r.1.toNat + r.2 ≤ 2 ^ 47) :
    Conforms abi mach .total hdr f proto (code base image) 0 spec :=
  Silmaril.Proofs.Machine.Abi.Conformance.Sse.Lrint.conforms hd hb hi

/-- **The result reads only the entry MXCSR's control bits**: under `abi` every admitted entry
has the default ones (`mxcsr &&& 0xffc0 = 0x1F80`), so the spec's result is `toLong 0x1F80 a`
whatever status flags the caller has set. -/
theorem toLong_mask (m : BitVec 32) (a : BitVec 64) : toLong m a = toLong (m &&& 0xffc0) a :=
  Silmaril.Proofs.Machine.Abi.Conformance.Sse.Lrint.toLong_mask m a

/-- `lrint(2.5) = 2` under the default MXCSR (round to nearest even). -/
theorem toLong_two_five : toLong 0x1F80 0x4004000000000000 = 2 := by decide +kernel

/-- `lrint(NaN)` is the integer indefinite. -/
theorem toLong_nan : toLong 0x1F80 0x7FF8000000000000 = 0x8000000000000000 := by decide +kernel

end Silmaril.Machine.Abi.Conformance.Sse.Lrint

end

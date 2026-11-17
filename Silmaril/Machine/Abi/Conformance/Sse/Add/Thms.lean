module

public import Silmaril.Machine.Abi.Conformance.Sse.Add.Defs
public import Silmaril.X86.Open.Thms
import Silmaril.Proofs.Machine.Abi.Conformance.Sse.Add

/-! # The first floating-point row: theorems

PROVED (standard axioms), proofs in `Silmaril.Proofs.Machine.Abi.Conformance.Sse.Add`. Every
statement is on a machine **model** (`Mach.str9L`, `Open`), not on real x86: reading the row
about hardware needs `Faithful` of a reference machine to `Mach.str9L` (`Conforms.onRef`), which
is not proved here.

* `conforms`: **`addsd %xmm1, %xmm0; ret` conforms** to `sysvScalar.defaultEnv` (the
  default-environment subset of the System V scalar fragment: entry MXCSR `0x1F80`) as
  `double add(double, double)` of `add.h`, on `Mach.str9L FeatureSet.baseline64
  Features.sseExts`, in total mode, with no stack frame, no memory written, and the result
  `sum s.mxcsr a b`: binary64 addition by `Numeric.Float`'s x86 SSE profile of the entry MXCSR.
  From every completion of every admitted call (any time-stamp stream, CET flag, and hidden
  vector and x87 parts) the call returns, with the callee-saved registers, DF clear, the MXCSR
  control bits and the x87 control word kept, the status flags of the addition ORed in, and
  the sum in the low 64 bits of XMM0. What the machine models and carries is
  `Sse.Thms.str9L_models`/`str9L_carried`: the row proves the MXCSR, x87 control word and
  direction-flag obligations from the run; x87 mode and the FFI thread pointer are carried.
* `sum_one_two`: the spec is the addition: `sum 0x1F80 1.0 2.0 = 3.0` (binary64 bit patterns,
  evaluated by the kernel);
* `open_not`: the same bytes, prototype and spec **do not conform on `Open`**, in either mode:
  the admitted call `add(0, 0)` is stuck at `addsd`, which the integer machine does not decode.
-/

@[expose] public section

namespace Silmaril.Machine.Abi.Conformance.Sse.Add

theorem conforms : Conforms abi mach .total hdr "add" proto code 0 spec :=
  Silmaril.Proofs.Machine.Abi.Conformance.Sse.Add.conforms

/-- `1.0 + 2.0 = 3.0` in binary64 under the default MXCSR. -/
theorem sum_one_two : sum 0x1F80 0x3FF0000000000000 0x4000000000000000 = 0x4008000000000000 := by
  decide +kernel

theorem open_not (mode : Mode) :
    ¬ Conforms abi (Mach.ofInt Silmaril.X86.Open.isa) mode hdr "add" proto code 0 spec :=
  Silmaril.Proofs.Machine.Abi.Conformance.Sse.Add.open_not mode

end Silmaril.Machine.Abi.Conformance.Sse.Add

end

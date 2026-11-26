module

public import Silmaril.Formats.Compression.Brotli.Defs
import Silmaril.Proofs.Formats.Compression.Brotli.Contracts
import Init.Omega

public section

namespace Silmaril.Formats.Compression.Brotli

theorem WindowWire.range {wbits : Nat} {code : List Bool} (wire : WindowWire wbits code) :
    10 ≤ wbits ∧ wbits ≤ 24 := by
  cases wire <;> omega

/-- A raw body begins at a byte boundary after the checked zero fill. -/
theorem bodyStart_aligned (position : Nat) (header : MetaHeader) :
    bodyStart position header % 8 = 0 := by
  simp [bodyStart, padding]
  omega

/-- The step count includes one empty last meta-block. -/
theorem BlocksWire.stepCount {position steps : Nat} {bits : List Bool} {chunks : List (List UInt8)}
    (wire : BlocksWire position bits chunks steps) : steps = chunks.length + 1 := by
  induction wire <;> simp_all

/-- Success accounts for all original bits through the empty terminal,
    concatenates the raw bodies in order, and satisfies all caller limits. -/
theorem decode_sound {limits : Limits} {input output : List UInt8}
    (read : decode limits input = .ok output) :
    ∃ wbits steps, StreamWire input output wbits steps ∧ input.length ≤ limits.input ∧
      output.length ≤ limits.output ∧ windowSize wbits ≤ limits.window ∧ steps ≤ limits.steps :=
  Proofs.Formats.Compression.Brotli.decode_sound read

end Silmaril.Formats.Compression.Brotli

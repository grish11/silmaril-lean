module

public import Silmaril.Wasm.Region.Examples.Defs

@[expose] public section
namespace Silmaril.Wasm.Region.Examples

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

theorem repeated_valid : (ByteMap.validate? repeated repeatedRows).isSome = true := by decide +kernel

theorem structured_valid : (ByteMap.validate? structured structuredRows).isSome = true := by decide +kernel

/-- Fixture coverage: all 3 root instruction positions are represented. -/
theorem repeated_root_coverage : repeated.RootCovered repeatedRows := by decide +kernel

/-- Fixture coverage: both root positions are represented; the inner nop is
outside this denominator and is not silently counted as a validated row. -/
theorem structured_root_coverage : structured.RootCovered structuredRows := by decide +kernel

/-- Matching bytes do not suffice: the second nop cannot borrow the first's
span, because its validated prefix must contain one instruction. -/
theorem repeated_wrong_occurrence :
    (ByteMap.validate? repeated [rootRow 1 3 4 (by decide)]).isSome = false := by decide +kernel

theorem immediate_not_instruction :
    (ByteMap.validate? structured [rootRow 0 2 3 (by decide)]).isSome = false := by decide +kernel

theorem nested_not_guessed :
    (ByteMap.validate? structured [⟨⟨7, [(0, 0)], 0⟩, ⟨3, 4, by decide⟩⟩]).isSome = false := by
  decide +kernel

theorem delimiter_not_instruction :
    (ByteMap.validate? repeated [rootRow 3 6 7 (by decide)]).isSome = false := by decide +kernel

end Silmaril.Wasm.Region.Examples

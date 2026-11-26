module

public import Silmaril.Formats.Compression.Brotli.BlockTypes.Defs
import Silmaril.Proofs.Formats.Compression.Brotli.BlockTypes.Contracts

public section

namespace Silmaril.Formats.Compression.Brotli.BlockTypes

/-- One NBLTYPES field occupies 1–11 bits and declares 1–256 types. -/
theorem CountWire.bounds {bits : List Bool} {types : Nat} (wire : CountWire bits types) :
    1 ≤ types ∧ types ≤ 256 ∧ 1 ≤ bits.length ∧ bits.length ≤ 11 :=
  Proofs.Formats.Compression.Brotli.BlockTypes.CountWire.bounds wire

/-- Section 6 bounds the finite count for a multi-type initial block. -/
theorem ControlWire.bounds {bits : List Bool} {control : Control} (wire : ControlWire bits control) :
    1 ≤ control.typeCount ∧ control.typeCount ≤ 256 ∧
      match control with
      | .single => True
      | .multiple _ _ _ initial => 1 ≤ initial ∧ initial ≤ 16793840 :=
  Proofs.Formats.Compression.Brotli.BlockTypes.ControlWire.bounds wire

/-- The three controls come from the original bits in RFC category order.
    The result preserves the untouched suffix under one caller bit cap. -/
theorem read_sound {bitLimit : Nat} {before after : LSBReader} {input : List Bool} {controls : Controls}
    (rep : before.Rep input) (count : before.count < 8)
    (read : read bitLimit before = .ok (controls, after)) :
    ∃ used suffix, Wire used controls ∧ input = used ++ suffix ∧ after.Rep suffix ∧ after.count < 8 ∧
      after.totalRead = before.totalRead + used.length ∧ used.length ≤ bitLimit :=
  Proofs.Formats.Compression.Brotli.BlockTypes.read_sound rep count read

end Silmaril.Formats.Compression.Brotli.BlockTypes

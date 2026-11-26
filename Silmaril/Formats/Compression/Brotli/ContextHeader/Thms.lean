module

public import Silmaril.Formats.Compression.Brotli.ContextHeader.Defs
import Silmaril.Proofs.Formats.Compression.Brotli.ContextHeader.Contracts

public section

namespace Silmaril.Formats.Compression.Brotli.ContextHeader

/-- The direct count is a multiple of the postfix scale and the standard
    distance-code alphabet stays within its RFC range. -/
theorem Fields.ranges (fields : Fields) :
    fields.postfixBits.val ≤ 3 ∧ fields.directField.val ≤ 15 ∧
    fields.direct ≤ 120 ∧ fields.direct % (2 ^ fields.postfixBits.val) = 0 ∧
    64 ≤ fields.distanceAlphabet ∧ fields.distanceAlphabet ≤ 520 :=
  Proofs.Formats.Compression.Brotli.ContextHeader.Fields.ranges fields

theorem Wire.length {types : Nat} {bits : List Bool} {fields : Fields} (wire : Wire types bits fields) :
    bits.length = 6 + 2 * types :=
  Proofs.Formats.Compression.Brotli.ContextHeader.Wire.length wire

/-- From the post-control cursor, consume precisely the distance fields
    and one mode per literal block type under the caller's cap. -/
theorem readAfter_sound {types bitLimit : Nat} {before after : LSBReader} {input : List Bool}
    {fields : Fields} (rep : before.Rep input) (count : before.count < 8)
    (read : readAfter types bitLimit before = .ok (fields, after)) :
    ∃ used suffix, Wire types used fields ∧ input = used ++ suffix ∧ after.Rep suffix ∧ after.count < 8 ∧
      after.totalRead = before.totalRead + (6 + 2 * types) ∧ used.length ≤ bitLimit :=
  Proofs.Formats.Compression.Brotli.ContextHeader.readAfter_sound rep count read

/-- The combined parser uses the original control witness and continues
    from that exact cursor under a single cap. -/
theorem read_sound {bitLimit : Nat} {before after : LSBReader} {input : List Bool}
    {header : Header} (rep : before.Rep input) (count : before.count < 8)
    (read : read bitLimit before = .ok (header, after)) :
    ∃ used suffix postControls,
      Header.Wire used header ∧ input = used ++ suffix ∧ after.Rep suffix ∧ after.count < 8 ∧
      BlockTypes.read bitLimit before = .ok (header.controls, postControls) ∧
      after.totalRead = postControls.totalRead + (6 + 2 * header.controls.literal.typeCount) ∧
      after.totalRead = before.totalRead + used.length ∧ used.length ≤ bitLimit :=
  Proofs.Formats.Compression.Brotli.ContextHeader.read_sound rep count read

end Silmaril.Formats.Compression.Brotli.ContextHeader

module

public import Silmaril.Formats.Compression.Snappy.Defs
import Silmaril.Proofs.Formats.Compression.Snappy.Sound

/-! # Length, consumption and denotation laws for raw Snappy blocks -/

public section

namespace Silmaril.Formats.Compression.Snappy

/-- Every parsed block accounts for its declared length within the caller's limit. -/
theorem parseMember_bounds {limit : Nat} {input rest : List UInt8} {block : Block}
    (h : parseMember limit input = .ok (block, rest)) :
    tagsSize block.tags = block.length ∧ block.length ≤ limit :=
  Proofs.Formats.Compression.Snappy.parseMember_bounds h

/-- The strict parser accepts a block exactly when the prefix parser consumes all input. -/
theorem parse_eq_ok_iff {limit : Nat} {input : List UInt8} {block : Block} :
    parse limit input = .ok block ↔ parseMember limit input = .ok (block, []) :=
  Proofs.Formats.Compression.Snappy.parse_eq_ok_iff

/-- The denotation appends exactly the sum of the tag sizes to the initial history. -/
theorem denotes_length {history out : List UInt8} {tags : List Tag}
    (h : Denotes history tags out) : out.length = history.length + tagsSize tags :=
  Proofs.Formats.Compression.Snappy.denotes_length h

/-- A successful strict decode consumes the entire input and realizes the tag
    denotation at the declared length, within the caller's limit. -/
theorem decode_sound {limit : Nat} {input out : List UInt8} (h : decode limit input = .ok out) :
    ∃ block, parseMember limit input = .ok (block, []) ∧ Denotes [] block.tags out ∧
      out.length = block.length ∧ block.length ≤ limit :=
  Proofs.Formats.Compression.Snappy.decode_sound h

end Silmaril.Formats.Compression.Snappy

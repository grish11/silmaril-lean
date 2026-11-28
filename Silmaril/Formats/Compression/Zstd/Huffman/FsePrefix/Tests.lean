module

import Silmaril.Formats.Compression.Zstd.Huffman.FsePrefix.Thms
import Batteries.Data.Except
meta import Silmaril.Formats.Compression.Zstd.Huffman.FsePrefix.Defs
meta import Batteries.Data.Except

namespace Silmaril.Formats.Compression.Zstd.Huffman.FsePrefix

/-- The pinned FSE writer produced the log-6 counts [15, 16, 33]. The
    handcrafted reverse stream ends just after two six-bit state fields. -/
private def boundary : List UInt8 := [0x05, 0x01, 0x45, 0x3f, 0x93, 0x13]

#guard match read 6 (boundary ++ [0x00, 0xff]) with
  | .error _ => false
  | .ok result =>
    let setup := result.setup
    result.consumed == 6 && setup.counts.bytes == 3 && setup.table.rows.length == 64 &&
      setup.states.first == 14 && setup.states.second == 19 && setup.cursor.remaining == 0 &&
      result.rest == [0x00, 0xff]

#guard read 5 boundary = .error .byteLimit

#guard read 6 [0x05, 0x01, 0x45, 0x3f, 0x93] = .error .truncated

#guard read 6 [0x04, 0x01, 0x45, 0x3f, 0x00] = .error .badEndMarker

#guard read 6 [0x03, 0x01, 0x45, 0x3f, 0x93, 0x13] = .error .badEndMarker

#guard read 6 [0x04, 0x01, 0x45, 0x3f, 0x40] = .error .truncatedStates

#guard read 6 [0x05, 0x02, 0x45, 0x3f, 0x93, 0x13] = .error (.counts .accuracyLog)

#guard read 7 [0x06, 0x10, 0xe3, 0xef, 0x03, 0x93, 0x13] = .error (.counts .symbolLimit)

end Silmaril.Formats.Compression.Zstd.Huffman.FsePrefix

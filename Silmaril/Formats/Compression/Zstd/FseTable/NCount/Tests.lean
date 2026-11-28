module

import Silmaril.Formats.Compression.Zstd.FseTable.NCount.Thms
import Batteries.Data.Except
meta import Silmaril.Formats.Compression.Zstd.FseTable.NCount.Defs
meta import Batteries.Data.Except

open Silmaril.Formats.Compression.Zstd.FseTable

private def limits : NCount.Limits := ⟨⟨9, 256⟩, 512, none⟩

-- These prefixes were written by the pinned libzstd FSE_writeNCount.
#guard NCount.read limits [0x10, 0x3f, 0xaa, 0] =
  .ok ⟨⟨5, [16, 16]⟩, 14, 2, [0xaa, 0]⟩
#guard NCount.read limits [0x10, 0xff, 0xaa, 0] =
  .ok ⟨⟨5, [16, 16]⟩, 14, 2, [0xaa, 0]⟩
#guard NCount.read limits [0x50, 0xf9, 0xaa] =
  .ok ⟨⟨5, [20, 9, 3]⟩, 16, 2, [0xaa]⟩
#guard NCount.read limits [0xf0, 0x01, 7] =
  .ok ⟨⟨5, [30, -1, -1]⟩, 13, 2, [7]⟩
#guard NCount.read limits [0x10, 0x80, 0x10, 0x7c, 9] =
  .ok ⟨⟨5, [0, 15, -1, 0, 16]⟩, 31, 4, [9]⟩
#guard (NCount.readTable limits [0x24, 0x30, 0x00, 0x7f, 0, 42]).map
    (fun (parsed, table) => (parsed.distribution, parsed.bits, parsed.bytes, parsed.rest, table.rows.length)) =
  .ok (⟨9, [257, 0, 253, -1, -1]⟩, 34, 5, [42], 512)
#guard NCount.read { limits with expectedSymbols := some 2 } [0x10, 0x3f] =
  .ok ⟨⟨5, [16, 16]⟩, 14, 2, []⟩
#guard NCount.read { limits with expectedSymbols := some 3 } [0x10, 0x3f] = .error .wrongSymbolCount
#guard NCount.read { limits with bytes := 1 } [0x10, 0x3f, 0xaa] = .error .byteLimit
#guard NCount.read { limits with table.symbols := 1 } [0x10, 0x3f] = .error .symbolLimit
#guard NCount.read { limits with table.accuracyLog := 8 } [0x24, 0x30, 0, 0x7f, 0] = .error .accuracyLog
#guard NCount.read limits [0x05, 0] = .error .accuracyLog
#guard NCount.read limits [0xf0, 0x03] = .error .tooFewSymbols
#guard NCount.read limits [] = .error .truncated
#guard NCount.read limits [0x10] = .error .truncated
#guard NCount.read limits [0x10, 0x80, 0x10] = .error .truncated

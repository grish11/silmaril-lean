module

import Silmaril.Formats.Compression.Zstd.FseTable.Thms
import Batteries.Data.Except
meta import Silmaril.Formats.Compression.Zstd.FseTable.Defs
meta import Batteries.Data.Except

open Silmaril.Formats.Compression.Zstd.FseTable

private def limits : Limits := ⟨9, 256⟩

#guard (build limits (predefined .literalLength)).map (fun t => (t.rows.length, t.rows[0]?, t.rows[63]?)) =
  .ok (64, some ⟨0, 4, 0⟩, some ⟨32, 6, 0⟩)
#guard (build limits (predefined .offset)).map (fun t => (t.rows.length, t.rows[31]?)) =
  .ok (32, some ⟨24, 5, 0⟩)
#guard (build limits (predefined .matchLength)).map (fun t => (t.rows.length, t.rows[63]?)) =
  .ok (64, some ⟨46, 6, 0⟩)
#guard (selectPredefined limits .offset 0 [1, 2, 3]).map Prod.snd = .ok [1, 2, 3]
#guard selectPredefined limits .offset 2 [1] = .error (.unsupportedMode 2)
#guard (build limits ⟨5, List.replicate 32 (-1)⟩).map (fun t => t.rows.map Row.symbol) =
  .ok (List.range 32).reverse
#guard (build limits ⟨5, [31, -1]⟩).map (fun t => t.rows[31]?) = .ok (some ⟨1, 5, 0⟩)
#guard (build limits ⟨9, [257, 0, 253, -1, -1]⟩).map (·.rows.length) = .ok 512
#guard build limits ⟨4, [8, 8]⟩ = .error .accuracyLog
#guard build ⟨30, 256⟩ ⟨10, [512, 512]⟩ = .error .accuracyLog
#guard build ⟨5, 256⟩ (predefined .literalLength) = .error .accuracyLog
#guard build ⟨9, 1⟩ ⟨5, [16, 16]⟩ = .error .symbolLimit
#guard build ⟨9, 512⟩ ⟨5, List.replicate 257 0⟩ = .error .symbolLimit
#guard build limits ⟨5, [17, -2, 15]⟩ = .error .invalidWeight
#guard build limits ⟨5, [0, 32, 0]⟩ = .error .tooFewSymbols
#guard build limits ⟨5, [16, 15]⟩ = .error .wrongMass
#guard build limits ⟨5, [16, 17]⟩ = .error .wrongMass

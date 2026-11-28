module

import Silmaril.Formats.Compression.Zstd.Huffman.SingleStream.Thms
import Batteries.Data.Except
meta import Silmaril.Formats.Compression.Zstd.Huffman.SingleStream.Defs
meta import Batteries.Data.Except

open Silmaril.Formats.Compression.Zstd.Huffman
open SingleStream

private def limits : Limits := ⟨⟨65, 129, 11⟩, 2, 4⟩
private def tree : DirectWeights.Tree := ⟨4, [4, 3, 2, 0, 1, 1]⟩

-- RFC 8878 Table 25. Equal weights use ascending literal symbols.
#guard build limits.tree tree = .ok ⟨4, [⟨4, 4, 0⟩, ⟨5, 4, 1⟩, ⟨2, 3, 1⟩, ⟨1, 2, 1⟩, ⟨0, 1, 1⟩]⟩
-- RFC erratum 8195 identifies the transposed codes in the printed example.
#guard decode limits tree 4 [0x10, 0x0d] = .ok [0, 1, 5, 4]
#guard decode limits tree 4 [0x01, 0x0d] = .ok [0, 1, 4, 5]
#guard (DirectWeights.read limits.tree [0x84, 0x43, 0x20, 0x1f, 0x01, 0x0d]).toOption.bind
  (fun parsed => (decode limits parsed.tree 4 parsed.rest).toOption) = some [0, 1, 4, 5]

#guard decode limits ⟨1, List.replicate 127 0 ++ [1, 1]⟩ 2 [5] = .ok [127, 128]
#guard decode limits tree 0 [1] = .ok []
#guard decode limits tree 0 [3] = .error .trailingBits
#guard decode limits tree 4 [] = .error .badEndMarker
#guard decode limits tree 4 [0] = .error .badEndMarker
#guard decode limits tree 4 [0x0d] = .error .incompleteCode
#guard decode limits tree 3 [0x01, 0x0d] = .error .trailingBits
#guard decode {limits with outputSymbols := 5} tree 5 [0x01, 0x0d] = .error .incompleteCode
#guard decode {limits with inputBytes := 1} tree 4 [0x01, 0x0d] = .error .inputLimit
#guard decode {limits with outputSymbols := 3} tree 4 [0x01, 0x0d] = .error .outputLimit
#guard build limits.tree ⟨4, [4, 3, 2, 0, 1]⟩ = .error .invalidTree
#guard build limits.tree ⟨4, [129, 1, 1]⟩ = .error .invalidTree
#guard build limits.tree ⟨12, List.replicate 2 1⟩ = .error .invalidTree
#guard build {limits.tree with symbols := 5} tree = .error .invalidTree

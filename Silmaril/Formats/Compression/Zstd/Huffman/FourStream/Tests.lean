module

import Silmaril.Formats.Compression.Zstd.Huffman.FourStream.Thms
import Batteries.Data.Except
meta import Silmaril.Formats.Compression.Zstd.Huffman.FourStream.Defs
meta import Batteries.Data.Except

open Silmaril.Formats.Compression.Zstd.Huffman
open FourStream

private def limits : Limits := ⟨10, 9⟩
private def treeLimits : DirectWeights.Limits := ⟨65, 129, 11⟩
private def tree : DirectWeights.Tree := ⟨1, [1, 1]⟩
private def jump : List UInt8 := [1, 0, 1, 0, 1, 0]
private def group : List UInt8 := jump ++ [5, 6, 7, 1]

#guard split limits 10 6 group = .ok ⟨⟨[5], 2⟩, ⟨[6], 2⟩, ⟨[7], 2⟩, ⟨[1], 0⟩⟩
#guard split limits 10 9 group = .ok ⟨⟨[5], 3⟩, ⟨[6], 3⟩, ⟨[7], 3⟩, ⟨[1], 0⟩⟩
#guard decode limits treeLimits tree 10 6 group = .ok [0, 1, 1, 0, 1, 1]
#guard decode limits treeLimits tree 10 7 (jump ++ [5, 6, 7, 3]) = .ok [0, 1, 1, 0, 1, 1, 1]
#guard (split ⟨265, 9⟩ 265 9 ([0, 1, 1, 0, 1, 0] ++ List.replicate 259 1)).map
    (fun parts => parts.chunks.map (·.bytes.length)) = .ok [256, 1, 1, 1]

#guard split limits 5 6 (jump.take 5) = .error .shortJumpTable
#guard split limits 10 6 ([0, 0, 1, 0, 1, 0] ++ [5, 6, 7, 1]) = .error .emptyStream
#guard split limits 10 6 ([1, 1, 1, 0, 1, 0] ++ [5, 6, 7, 1]) = .error .invalidStreamExtent
#guard split limits 9 6 (jump ++ [5, 6, 7]) = .error .invalidStreamExtent
#guard split limits 9 6 group = .error .sizeMismatch
#guard split ⟨11, 9⟩ 11 6 group = .error .sizeMismatch
#guard split limits 10 5 group = .error .invalidRegeneratedSize
#guard split ⟨9, 9⟩ 10 6 group = .error .inputLimit
#guard split ⟨10, 5⟩ 10 6 group = .error .outputLimit
#guard decode limits treeLimits tree 10 6 (jump ++ [5, 6, 7, 0]) = .error (.stream 4 .badEndMarker)
#guard decode limits treeLimits tree 10 6 (jump ++ [5, 6, 7, 3]) = .error (.stream 4 .trailingBits)
#guard decode limits treeLimits tree 10 6 (jump ++ [1, 6, 7, 1]) = .error (.stream 1 .incompleteCode)
#guard decode limits treeLimits tree 10 7 group = .error (.stream 4 .incompleteCode)
#guard decode limits treeLimits ⟨1, [1]⟩ 10 6 group = .error (.table .invalidTree)

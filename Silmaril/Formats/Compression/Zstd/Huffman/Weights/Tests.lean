module

import Silmaril.Formats.Compression.Zstd.Huffman.Weights.Thms
import Silmaril.Formats.Compression.Zstd.Huffman.SingleStream.Thms

namespace Silmaril.Formats.Compression.Zstd.Huffman.Weights

private def limits : Limits := ⟨256, 11⟩
private def sparse : List Nat := 1 :: List.replicate 254 0
private def completed : Tree := ⟨1, sparse ++ [1]⟩

set_option maxRecDepth 2048 in
example : complete limits sparse = .ok completed := by rfl

example : complete ⟨257, 11⟩ (sparse ++ [0]) = .error .symbolLimit := by rfl

example : complete ⟨255, 11⟩ sparse = .error .symbolLimit := by rfl

example : complete limits [2 ^ 100] = .error .depthLimit := by rfl

example : complete limits [4, 3, 2, 0, 1] = .ok ⟨4, [4, 3, 2, 0, 1, 1]⟩ := by rfl

example : complete limits [3, 1, 1] = .ok ⟨3, [3, 1, 1, 2]⟩ := by rfl

set_option maxRecDepth 2048 in
example : SingleStream.buildGeneral limits completed =
    .ok ⟨1, [⟨0, 1, 0⟩, ⟨255, 1, 1⟩]⟩ := by rfl

example : SingleStream.build ⟨65, 256, 11⟩ completed = .error .invalidTree := by rfl

end Silmaril.Formats.Compression.Zstd.Huffman.Weights

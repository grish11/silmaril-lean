module

import Silmaril.Formats.Compression.Zstd.LiteralBlock.Thms
import Batteries.Data.Except
meta import Silmaril.Formats.Compression.Zstd.LiteralBlock.Defs
meta import Batteries.Data.Except

open Silmaril.Formats.Compression.Zstd (Header)
open Silmaril.Formats.Compression.Zstd.LiteralBlock

private def header : Header := ⟨131072, false, false, 0, none⟩

#guard decode header 0 [0, 0] = .ok []
#guard decode header 3 [0x18, 97, 98, 99, 0] = .ok [97, 98, 99]
#guard decode header 2 [0x11, 97, 0] = .ok [97, 97]
#guard decode header 32 ([4, 2] ++ List.replicate 32 97 ++ [0]) = .ok (List.replicate 32 97)
#guard decode header 4096 [13, 0, 1, 97, 0] = .ok (List.replicate 4096 97)
#guard decode header 1 [28, 0, 0, 97, 0] = .ok [97]
#guard decode header 1 [8, 97, 128, 0] = .ok [97]

#guard parseLiterals 2 [0x11, 97, 7, 0] = .ok (.rle 2 97, [7, 0])
#guard readSequenceCount [127, 9] = .ok (127, [9])
#guard readSequenceCount [128, 0, 9] = .ok (0, [9])
#guard readSequenceCount [254, 255, 9] = .ok (32511, [9])
#guard readSequenceCount [255, 0, 0, 9] = .ok (32512, [9])
#guard readSequenceCount [255, 255, 255, 9] = .ok (98047, [9])
#guard readSequenceCount [255, 0] = .error .truncated

#guard decode header 1 [2, 0, 0, 0] = .error (.unsupported .huffmanLiterals)
#guard decode header 1 [3, 0, 0, 0] = .error (.unsupported .treelessLiterals)
#guard decode header 2 [0x11, 97, 1, 0] = .error (.unsupported .sequences)
#guard decode header 2 [0x11, 97, 0, 1] = .error .trailingSequences
#guard decode header 2 [0x11, 97] = .error .truncated
#guard decode header 2 [0x11] = .error .truncated
#guard decode header 3 [0x18, 97, 98] = .error .truncated
#guard decode header 4096 [13, 0] = .error .truncated
#guard decode header 1 [0x11, 97, 0] = .error .outputLimit
#guard decode ⟨2, false, false, 0, none⟩ 2 [0x11, 97, 0] = .error .blockLimit
#guard decode ⟨4, false, false, 0, none⟩ 32 [5, 2, 97, 0] = .error .outputLimit
#guard (decode header 131072 [13, 0, 32, 97, 0]).map List.length = .ok 131072
#guard decode header 200000 [29, 0, 32, 97, 0] = .error .outputLimit

example : decode ⟨1024, false, false, 0, none⟩ 0 [0, 0] = .ok [] := rfl
example : decode ⟨1024, false, false, 0, none⟩ 0 [0, 0, 1] = .error .trailingSequences := rfl
example : decode ⟨1024, false, false, 0, none⟩ 1 [0x11, 97, 0] = .error .outputLimit := rfl

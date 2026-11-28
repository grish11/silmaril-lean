module

import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Thms
meta import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Defs

open Silmaril.Formats Silmaril.Formats.Parquet.Timestamp.Leaf

private def page (tag : Int) (offset : Nat) : Dictionary.DataPage :=
  ⟨⟨⟨0, 0, none, .dataV1 ⟨0, tag, 3, 3⟩⟩, ⟨offset, offset + 1⟩, ⟨offset + 1, offset + 1⟩⟩,
    ⟨⟨0, 0⟩, ⟨0, 1⟩, 0, 0, tag, .v1 3 3⟩⟩

#guard Fallback.checkSequence [page 8 12, page 8 13, page 0 14, page 0 15] = .ok ()
#guard Fallback.checkSequence [page 8 12] = .error .dictionaryMissingFallback
#guard Fallback.checkSequence [page 0 12, page 8 13] = .error (.dictionaryPage 1 12 (.encoding 0))
#guard Fallback.checkSequence [page 8 12, page 8 13, page 0 14, page 8 15] =
  .error (.dictionaryPage 4 15 .dictionaryAfterFallback)
#guard Fallback.checkSequence [] = .error .dictionaryMissingData

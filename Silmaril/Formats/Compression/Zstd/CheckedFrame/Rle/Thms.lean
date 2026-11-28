module

public import Silmaril.Formats.Compression.Zstd.CheckedFrame.Rle.Defs
import Silmaril.Proofs.Formats.Compression.Zstd.CheckedFrame.Rle.Contracts

public section

namespace Silmaril.Formats.Compression.Zstd.CheckedFrame.Rle

/-- The new history is the exact window suffix with the supplied repeat offsets. -/
theorem advance_sound (history : History) (window : Nat) (bytes : List UInt8)
    (offsets : Sequence.RepeatOffsets) :
    (history.advance window bytes offsets).recent.toList =
      (history.recent.toList ++ bytes).drop ((history.recent.toList ++ bytes).length - window) ∧
    (history.advance window bytes offsets).recent.size ≤ window ∧
    (history.advance window bytes offsets).offsets = offsets :=
  Proofs.Formats.Compression.Zstd.CheckedFrame.Rle.advance_sound history window bytes offsets

/-- Appending a block preserves the window-suffix invariant for the entire
    decoded frame prefix. -/
theorem advance_suffix {history : History} {window : Nat} {previous bytes : List UInt8}
    (holds : history.recent.toList = previous.drop (previous.length - window))
    (offsets : Sequence.RepeatOffsets) :
    (history.advance window bytes offsets).recent.toList =
      (previous ++ bytes).drop ((previous ++ bytes).length - window) :=
  Proofs.Formats.Compression.Zstd.CheckedFrame.Rle.advance_suffix holds offsets

/-- The frame consumes its full input, denotes the returned bytes with rolling
    history and repeats, and respects the frame limits and command cap. -/
theorem decode_sound {limits : Limits} {input out : List UInt8}
    (success : decode limits input = .ok out) :
    ∃ header, FrameWire limits.commandsPerBlock input out header ∧ input.length ≤ limits.frame.input ∧
      out.length ≤ limits.frame.output ∧ header.windowSize ≤ limits.frame.window :=
  Proofs.Formats.Compression.Zstd.CheckedFrame.Rle.decode_sound success

end Silmaril.Formats.Compression.Zstd.CheckedFrame.Rle

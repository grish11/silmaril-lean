module

import Silmaril.Formats.Compression.Zstd.Sequence.Thms
import Batteries.Data.Except
meta import Silmaril.Formats.Compression.Zstd.Sequence.Defs
meta import Batteries.Data.Except

open Silmaril.Formats.Compression.Zstd.Sequence

private def limits : Limits := ⟨1024, 8⟩
private def start := RepeatOffsets.initial
private def commands : List Command := [⟨2, 5, 5⟩]

#guard execute limits #[] [1, 2, 9] start commands =
  .ok ⟨[1, 2, 1, 2, 1, 2, 1, 9], ⟨2, 1, 4⟩⟩
#guard execute limits #[1, 2] [3, 9] start [⟨1, 6, 5⟩] =
  .ok ⟨[3, 1, 2, 3, 1, 2, 9], ⟨3, 1, 4⟩⟩
#guard execute limits #[] [1, 2, 3] start [] = .ok ⟨[1, 2, 3], start⟩
#guard execute ⟨0, 0⟩ #[] [] start [] = .ok ⟨[], start⟩

#guard resolve start 1 1 = some (1, ⟨1, 4, 8⟩)
#guard resolve start 1 2 = some (4, ⟨4, 1, 8⟩)
#guard resolve start 1 3 = some (8, ⟨8, 1, 4⟩)
#guard resolve start 0 1 = some (4, ⟨4, 1, 8⟩)
#guard resolve start 0 2 = some (8, ⟨8, 1, 4⟩)
#guard resolve ⟨8, 4, 1⟩ 0 3 = some (7, ⟨7, 8, 4⟩)
-- The corrected row in RFC 8878 Table 18, verified erratum 6442.
#guard resolve ⟨2222, 1111, 3333⟩ 0 3 = some (2221, ⟨2221, 2222, 1111⟩)

#guard execute ⟨4, 4⟩ #[10, 20, 30, 40] [] start [⟨0, 6, 3⟩] =
  .ok ⟨[20, 30, 40], ⟨3, 1, 4⟩⟩
#guard execute ⟨4, 4⟩ #[10, 20, 30, 40] [] start [⟨0, 7, 3⟩] = .error .offsetOutsideWindow
#guard execute ⟨3, 3⟩ #[10, 20, 30, 40] [] start [⟨0, 5, 3⟩] = .error .historyLimit
#guard execute limits #[10, 20, 30, 40] [] start [⟨0, 3, 3⟩] = .error .invalidOffset
#guard execute limits #[10, 20, 30, 40] [] start [⟨0, 0, 3⟩] = .error .invalidOffset
#guard execute limits #[] [1, 2, 9] ⟨1, 0, 8⟩ commands = .error .invalidRepeats
#guard execute limits #[10, 20, 30] [] start [⟨0, 7, 3⟩] = .error .historyUnderflow
#guard execute limits #[] [1] start commands = .error .literalUnderflow
#guard execute limits #[] [1, 2] start [⟨2, 5, 2⟩] = .error .shortMatch

#guard execute { limits with output := 7 } #[] [1, 2, 9] start commands = .error .outputLimit
#guard execute { limits with output := 6 } #[] [1, 2, 9] start commands = .error .outputLimit
#guard execute limits #[] [1, 2, 3] start [⟨2, 5, 3⟩, ⟨1, 1, 3⟩] = .error .outputLimit
#guard execute ⟨1024, 0⟩ #[] [1] start [] = .error .outputLimit
#guard execute ⟨262144, 262144⟩ #[] [1] start [⟨1, 4, 131072⟩] = .error .outputLimit

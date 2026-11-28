module

import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi.Example.Defs

open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi.Example

#guard interleaved == some {
  projection := [4, 6, 8]
  full := ⟨[0, 1, 2, 3, 4, 5, 6, 7, 8], [9, 6, 1, 3, 2, 5, 4, 11, 1], [9, 6, 1, 3, 2, 5, 4, 11, 1]⟩
  compact := ⟨[4, 6, 8], [2, 4, 1], [2, 4, 1]⟩
  recompacted := ⟨[4, 6, 8], [2, 4, 1], [2, 4, 1]⟩
}

#guard ambientOnly == some (⟨[], ⟨[1], [7], [7]⟩, ⟨[], [], []⟩, ⟨[], [], []⟩⟩, true)

#guard parallel == some (
  ⟨[0], ⟨[0, 1], [7, 9], [7, 9]⟩, ⟨[0], [7], [7]⟩, ⟨[0], [7], [7]⟩⟩,
  ⟨[0], ⟨[1, 0], [9, 7], [9, 7]⟩, ⟨[1], [9], [9]⟩, ⟨[1], [9], [9]⟩⟩,
  [some 7, some 9])

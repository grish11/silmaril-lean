module

public import Silmaril.Machine.Region.X86.SqliteStrLength.Clang.Defs

@[expose] public section
namespace Silmaril.Machine.Region.X86.SqliteStrLength.Clang

open Silmaril.SSA.LambdaRTL

/-- Identify the two outward return labels, preserving the internal load and zero targets. -/
def coalesceReturns : Label → Label
  | .returnZero => .returnLoaded
  | label => label

/-- The Clang CFG after coalescing only its outward return labels. -/
def coalesced : CFG Register Label Operation := graph.relabel coalesceReturns

end Silmaril.Machine.Region.X86.SqliteStrLength.Clang

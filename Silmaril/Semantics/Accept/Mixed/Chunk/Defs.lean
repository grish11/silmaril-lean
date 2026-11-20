module

public import Silmaril.Semantics.Accept.Mixed.Defs

/-!
# Chunk mixed sessions: returns constrained by the chunk buffer

`Silmaril.Accept.Mixed.ReturnsIn` constrains every return from every parsing state, and the
streaming variant (`Silmaril.Accept.Mixed.StreamReturnsIn`) tracks the append buffer only: neither
can constrain `finish(n, h)` by the values it consumes. Here the returns of a mixed trace are read
**along the chunk buffer** the parsing host holds at each return.

* `chunkStep b e`: the chunk buffer after the parsing event `e` from `b`, outside undefined
  behaviour: `feed c` appends `c`; `finish(n, _)` drops `n` values when at least `n` are buffered
  and otherwise (an overrun under `callTrap` or `ignore`) leaves the buffer; `reset` clears it;
  every other event keeps it.
* `chunkFold b t`: the chunk buffer after the parsing events `t`, from `b`.

The assume/guarantee theorems `Thms.mixedRel_subset_of_chunkAG` and
`Thms.mixedFixedRel_subset_of_chunkAG` constrain each return by the chunk buffer
`chunkFold [] (parseEvents u)` of the trace prefix `u` before it.

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Accept.Mixed

open Silmaril.Accept.Parse

universe u

/-- **The chunk buffer after one parsing event**, outside undefined behaviour. -/
def chunkStep {V H : Type u} : List V → PEv V H → List V
  | b, .feed c => b ++ c
  | b, .finish n _ => if n ≤ b.length then b.drop n else b
  | _, .reset => []
  | b, _ => b

/-- The chunk buffer after the parsing events of a trace, from `b`. -/
def chunkFold {V H : Type u} (b : List V) (t : List (PEv V H)) : List V := t.foldl chunkStep b

end Silmaril.Accept.Mixed

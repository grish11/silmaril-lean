module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Defs
public import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Fixture

/-! The shared numbered and typed MemRef fixture for the three-loop boundary. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Fixture

open Memory.Diamond.Institution renaming Model → EntryModel
open Sequential.Fixture (captures initial right)
open Linked.Fixture (combined wiring inputs)

-- The third loop uses the second loop's store capture as its stop word
-- and uses the second return as its own store payload.
def thirdWiring : Boundary.Wiring captures.args captures.args :=
  .forward .head (.forward (.tail .head) (.forward (.tail (.tail (.tail .head)))
    (.word fun p => nomatch p)))

def entryModel : EntryModel combined := ⟨6, inputs⟩

def afterFirst : Heap 6 := (initial.write 0 11).write 2 11
def afterSecond : Heap 6 := (afterFirst.write 3 22).write 5 22
def expected : Result 6 := (3, 3, 22, afterSecond.write (right 0) 3)

def thirdInput := thirdWiring.select (3 : Word) (wiring.select (3 : Word) inputs)

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Fixture

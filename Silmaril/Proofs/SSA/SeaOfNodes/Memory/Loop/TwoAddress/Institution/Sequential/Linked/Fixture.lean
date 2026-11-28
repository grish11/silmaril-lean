module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Defs
public import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Fixture

/-! The disjoint-write fixture at the shared typed boundary of the linked graphs. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Fixture

open CategoryTheory
open RVSDG (Port Tuple)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel
open Sequential.Fixture

abbrev extra := [ValueSort.address, .address, .word]
abbrev combined : EntrySignature := ⟨captures.args ++ extra⟩

def prefixPort {sort : ValueSort} :
    {args : List ValueSort} → Port args sort → Port (args ++ extra) sort
  | _, .head => .head
  | _, .tail port => .tail (prefixPort port)

def first : Graph combined.args := mapGraph (P := captures) (Q := combined) ⟨prefixPort⟩ graph

def firstRight : Port combined.args .address := .tail (.tail (.tail (.tail .head)))
def secondRight : Port combined.args .address := .tail (.tail (.tail (.tail (.tail .head))))
def rightStore : Port combined.args .word := .tail (.tail (.tail (.tail (.tail (.tail .head)))))

def wiring : Boundary.Wiring combined.args captures.args :=
  .forward firstRight (.forward secondRight (.word fun
    | .head => rightStore
    | .tail impossible => nomatch impossible))

abbrev inputs : Tuple (Val 6) combined.args :=
  SeaOfNodes.Loop.appendTuple
    (.cons (right 0) (.cons (right 1) (.cons (22 : Word) .nil)) : Tuple (Val 6) extra)
    (CellEmbedding.input left model.input)

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Fixture

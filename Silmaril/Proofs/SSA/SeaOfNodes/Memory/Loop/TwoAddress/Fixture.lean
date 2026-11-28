module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Backends.Activation.Defs

/-! A shared double-swap fixture for the two emitted backends. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Fixture

open CategoryTheory
open RVSDG (Port Tuple)
open Memory.Diamond.Institution renaming Signature → EntrySignature
open Loop.Institution.Lowering.Backends.Activation (bindAddress)

abbrev args : List ValueSort := [.address, .address, .address, .word]

def copyTo : Port (activationArgs args) .address :=
  .tail (.tail (.tail (.tail .head)))

def zero : Port (activationArgs args) .word :=
  .tail (.tail (.tail (.tail (.tail .head))))

-- Save the first cell for the tail test, clear it, then read the second
-- cell from the new heap. Copy that second load to a third captured cell.
def body : Memory.Graph (activationArgs args) :=
  .load (.latest 0) (.arg .head)
    (.store (.latest 0) (.arg .head) (.arg zero)
      (.load (.latest 1) (.arg (.tail .head))
        (.store (.latest 1) (.arg copyTo) (.output 0 .head)
          (.ret (.latest 2) (.output 1 .head)))))

abbrev captures : EntrySignature := ⟨args⟩
abbrev banks : EntrySignature := ⟨activationArgs args⟩

-- Compose the two bindings into the same source bank.
def swap : banks ⟶ banks :=
  bindAddress (.tail .head) (bindAddress .head (⟨fun p => .tail (.tail p)⟩ : captures ⟶ banks))

def graph : Graph args :=
  ⟨⟨body, rfl, zero⟩, .head, .tail .head,
    EntrySignature.Hom.port swap .head, EntrySignature.Hom.port swap (.tail .head)⟩

def identifyAddresses : captures ⟶ captures :=
  ⟨fun
    | .head => .head
    | .tail .head => .head
    | .tail (.tail p) => .tail (.tail p)⟩

def coincidentGraph : Graph args := { graph with entrySecond := .head }

def input (second : Address 4) : Tuple (Val 4) args :=
  .cons (0 : Address 4) (.cons second (.cons (2 : Address 4) (.cons (0 : Word) .nil)))

def initial : Heap 4 :=
  fun cell => if cell = 0 then 7 else if cell = 1 then 5 else if cell = 2 then 99 else 42

def afterFirst : Heap 4 := (initial.write 0 0).write 2 5
def afterSecond : Heap 4 := (afterFirst.write 1 0).write 2 0
def final : Heap 4 := (afterSecond.write 0 0).write 2 0
def aliasFirst : Heap 4 := (initial.write 0 0).write 2 0
def aliased : Heap 4 := (aliasFirst.write 0 0).write 2 0

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Fixture

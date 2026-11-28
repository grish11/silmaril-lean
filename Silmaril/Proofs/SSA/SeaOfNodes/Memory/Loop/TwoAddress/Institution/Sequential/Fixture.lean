module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Defs

/-! Two disjoint address pairs in one initialized six-cell heap. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Fixture

open RVSDG (Port Tuple)
open CellEmbedding (Embedding DisjointImages extend restrict)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

abbrev captures : EntrySignature := ⟨[.address, .address, .word, .word]⟩

def stop : Port (activationArgs captures.args) .word := .tail (.tail (.tail (.tail .head)))
def storeWord : Port (activationArgs captures.args) .word := .tail (.tail (.tail (.tail (.tail .head))))

-- Read and update the first lane, then swap the live lanes on feedback.
def graph : Graph captures.args :=
  ⟨⟨.load (.latest 0) (.arg .head)
      (.store (.latest 0) (.arg .head) (.arg storeWord)
        (.ret (.latest 1) (.output 0 .head))),
    rfl, stop⟩, .head, .tail .head, .tail .head, .head⟩

def args (stopWord stored : Word) : Tuple (Val 2) captures.args :=
  .cons (0 : Address 2) (.cons (1 : Address 2) (.cons stopWord (.cons stored .nil)))

abbrev model : EntryModel captures := ⟨2, args 3 11⟩
def next (word : Word) := args word 22

def left : Embedding 2 6 where
  toFun a := ⟨2 * a.val, by omega⟩
  inj' := by
    intro a b equal
    apply Fin.ext
    have numbers := congrArg (fun cell : Address 6 => cell.val) equal
    change 2 * a.val = 2 * b.val at numbers
    omega

def right : Embedding 2 6 where
  toFun a := ⟨3 + 2 * a.val, by omega⟩
  inj' := by
    intro a b equal
    apply Fin.ext
    have numbers := congrArg (fun cell : Address 6 => cell.val) equal
    change 3 + 2 * a.val = 3 + 2 * b.val at numbers
    omega

theorem disjoint : DisjointImages left right := by
  intro a b equal
  have numbers := congrArg (fun cell : Address 6 => cell.val) equal
  change 2 * a.val = 3 + 2 * b.val at numbers
  omega

def leftInitial : Heap 2 := fun cell => if cell = 0 then 7 else 3
def rightInitial : Heap 2 := fun cell => if cell = 0 then 9 else 3
def frame : Heap 6 := fun cell => if cell = 1 then 73 else 91
def initial : Heap 6 := extend right (extend left frame leftInitial) rightInitial
def leftFinal : Heap 2 := (leftInitial.write 0 11).write 1 11
def rightFinal : Heap 2 := (rightInitial.write 0 22).write 1 22
def final : Heap 6 := extend right (extend left initial leftFinal) rightFinal

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Fixture

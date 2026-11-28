module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Defs

/-! # An executable unequal-arm quad loop over MLIR words -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Example

open SeaOfNodes.Diamond (dataPorts)
open SeaOfNodes.Loop.MLIR.CF (Op evalOp model)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open Silmaril.MLIR.Arith (Width)
open RVSDG (Port)
open Blocks (Bank)

abbrev width : Width := ⟨8, by decide⟩
abbrev num : SeaOfNodes.Diamond.ValueSort Width := .data width
abbrev regs : List (SeaOfNodes.Diamond.ValueSort Width) :=
  [num, num, num, num, num, num, .predicate]
abbrev ports := dataPorts regs
abbrev Reg := Port ports (.value num)

def count : Reg := .head
def selector : Reg := .tail .head
def result : Reg := .tail (.tail .head)
def stride : Reg := .tail (.tail (.tail .head))
def decrement : Reg := .tail (.tail (.tail (.tail .head)))
def zero : Reg := .tail (.tail (.tail (.tail (.tail .head))))
def test : Port ports (.value .predicate) := .tail (.tail (.tail (.tail (.tail (.tail .head)))))

def constant (dest : Reg) (value : Word width) : Quad Op regs :=
  ⟨_, _, dest, .arithmetic (.constant value), .nil⟩

def add (dest lhs rhs : Reg) : Quad Op regs :=
  ⟨_, _, dest, .arithmetic (.binary .addi), .cons lhs (.cons rhs .nil)⟩

def positive (reg : Reg) : Quad Op regs :=
  ⟨_, _, test, .ult width, .cons zero (.cons reg .nil)⟩

/-- Entry 4, split 2, true arm 5 → 6, false arm 0, merge 3, latch 1. -/
def source : Source Op regs num 7 := fun id =>
  if id = 4 then
    ⟨[constant selector 1, constant decrement 255, constant zero 0], .transfer (.jump 2)⟩
  else if id = 2 then
    ⟨[positive selector], .branch test (.jump 5) (.jump 0)⟩
  else if id = 5 then
    ⟨[add result result stride], .transfer (.jump 6)⟩
  else if id = 6 then
    ⟨[add result result stride, constant selector 0], .transfer (.jump 3)⟩
  else if id = 0 then
    ⟨[add result result result, constant selector 1], .transfer (.jump 3)⟩
  else if id = 3 then
    ⟨[add result result zero], .transfer (.jump 1)⟩
  else
    ⟨[add count count decrement, positive count], .branch test (.jump 2) (.ret result)⟩

def checked : Program source 4 :=
  (check source 4).get (by rfl)

def input : Bank (regs := regs) model :=
  .cons (3 : Word width) (.cons (99 : Word width) (.cons (5 : Word width)
    (.cons (2 : Word width) (.cons (0 : Word width) (.cons (99 : Word width) (.cons ⟨false⟩ .nil))))))

def runSource (fuel : Nat) : Option Nat :=
  (source.runFrom model fuel 4 input).map BitVec.toNat

def runCF (fuel : Nat) : Option Nat :=
  ((lower checked).run evalOp fuel (encodeValues input)).map (fun env => (env.get .here).toNat)

def predecessors (activations : Nat) : List Nat :=
  (checked.trace model activations ((source 4).body.eval model input)).map
    (fun occurrence => (checked.predecessor occurrence).val)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Example

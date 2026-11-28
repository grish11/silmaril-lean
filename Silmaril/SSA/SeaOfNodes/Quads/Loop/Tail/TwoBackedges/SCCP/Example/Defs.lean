module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Thms

/-! A disabled feedback arm carries a different byte from the feasible one. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Example

open Diamond (Model Signature Val ValueSort dataPorts)
open Diamond.SCCP (Fact)
open SeaOfNodes.Loop.SCCP (BankDecidableEq bankTuple)
open RVSDG (Tuple)
open Semantics.Dataflow (Flat)

abbrev Byte := BitVec 8
abbrev word : ValueSort Unit := .data ()
abbrev regs : List (ValueSort Unit) := [.predicate, .predicate, word]

inductive Op : Signature Unit where
  | stop : Op [] .predicate
  | byte (value : Byte) : Op [] word

def model : Model Op where
  value := fun _ => Byte
  run
    | .stop, .nil => ⟨false⟩
    | .byte value, .nil => value

instance bankEq : BankDecidableEq model.value (dataPorts regs) where
  atPort i := Fin.cases (motive := fun j => DecidableEq (Val model.value (dataPorts regs)[j]))
    (inferInstance : DecidableEq (ULift Bool))
    (fun j => Fin.cases (motive := fun k => DecidableEq (Val model.value (dataPorts regs)[k.succ]))
      (inferInstance : DecidableEq (ULift Bool))
      (fun k => Fin.cases (motive := fun l => DecidableEq (Val model.value (dataPorts regs)[l.succ.succ]))
        (inferInstance : DecidableEq Byte) (fun l => l.elim0) k) j) i

def program : Program Op regs word where
  preheader := []
  header := []
  again := .head
  select := .tail .head
  result := .tail (.tail .head)
  feedback side :=
    let stop : Quad Op regs := ⟨[], .predicate, .head, .stop, .nil⟩
    if side then [stop, ⟨[], word, .tail (.tail .head), .byte 99, .nil⟩] else [stop]

def facts (side : Flat (ULift Bool)) : Tuple (Fact model.value) (dataPorts regs) :=
  .cons (.constant ⟨true⟩) (.cons side (.cons (.constant (7 : Byte)) .nil))

def concrete (side : Bool) : Tuple (Val model.value) (dataPorts regs) :=
  .cons ⟨true⟩ (.cons ⟨side⟩ (.cons (7 : Byte) .nil))

/-- Entry, true feedback, false feedback and exit marks, then byte and result. -/
def report (side : Flat (ULift Bool)) : Bool × Bool × Bool × Bool × Flat Nat × Flat Nat :=
  let state := solve model program (facts side)
  (decide (incomingIndex .entry ∈ state.1),
    decide (incomingIndex (.feedback true) ∈ state.1),
    decide (incomingIndex (.feedback false) ∈ state.1),
    decide (exitIndex ∈ state.1), (state.2.1 (2 : Fin 3)).map BitVec.toNat, state.2.2.map BitVec.toNat)

def feedbackBytes : Flat Nat × Flat Nat :=
  let input := facts (.constant ⟨false⟩)
  let state := solve model program input
  let columns := SCCP.columns model program input (blockFacts model program.header (bankTuple state.2.1))
  ((columns (.feedback true) (2 : Fin 3)).map BitVec.toNat,
    (columns (.feedback false) (2 : Fin 3)).map BitVec.toNat)

def firstFeedback (side : Bool) : Option (Bool × Nat) :=
  match program.step model (concrete side) with
  | .inl _ => none
  | .inr (selected, next) => some (selected, (next.get program.result).toNat)

def nativeReturn (side : Bool) (fuel : Nat) : Option Nat :=
  (program.source.runFrom model fuel 0 (concrete side)).map BitVec.toNat

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Example

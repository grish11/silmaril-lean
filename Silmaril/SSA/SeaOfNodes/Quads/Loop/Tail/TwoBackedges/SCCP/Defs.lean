module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Thms

/-! Executable occurrences and typed flat facts for a loop with two backedges. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP

open Diamond (Model Signature Ty ValueSort Val dataPorts sortValue)
open Diamond.SCCP (Fact evalFacts gather tupleFacts)
open SeaOfNodes.Loop.SCCP (BankFacts BankDecidableEq bankTuple)
open Join (Block)
open RVSDG (Tuple)
open Semantics.Dataflow (Flat)
open Semantics.Dataflow.FiniteHeight (HeightBound)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data}

abbrev Marked := Finset (Fin 4)

def incomingIndex : Incoming → Fin 4
  | .entry => 0
  | .feedback true => 1
  | .feedback false => 2

def exitIndex : Fin 4 := 3

abbrev State (value : Data → Type w) (regs : List (ValueSort Data)) (out : ValueSort Data) :=
  Marked × (BankFacts value (dataPorts regs) × Flat (sortValue value out))

/-- Apply the producer interpreter's flat operation rule to a register assignment. -/
def quadFacts (m : Model.{u, v, w} Op) (q : Quad Op regs)
    (bank : Tuple (Fact m.value) (dataPorts regs)) : Tuple (Fact m.value) (dataPorts regs) :=
  write q.dest (Flat.map (m.run q.op) (gather (q.operands.map (fun _ p => bank.get p)))) bank

/-- Interpret the compiled versions of one ordered source block using the
shared abstract producer table. -/
def blockFacts (m : Model.{u, v, w} Op) (block : Block Op regs)
    (args : Tuple (Fact m.value) (dataPorts regs)) : Tuple (Fact m.value) (dataPorts regs) :=
  let compiled := CFG.compileBlock block (Quads.initial regs)
  compiled.outgoing.read args (evalFacts m args compiled.flow PUnit.unit)

/-- Abstract branch selection with the optimistic bottom order. -/
def choose (test : Flat (ULift.{w} Bool)) (onTrue onFalse : Marked) : Marked :=
  match test with
  | .bottom => ∅
  | .constant value => if value.down then onTrue else onFalse
  | .overdefined => onTrue ∪ onFalse

def successors (again side : Flat (ULift.{w} Bool)) : Marked :=
  choose again
    (choose side {incomingIndex (.feedback true)} {incomingIndex (.feedback false)}) {exitIndex}

def gate {α : Type*} (marks : Marked) (mark : Fin 4) (fact : Flat α) : Flat α :=
  if mark ∈ marks then fact else ⊥

/-- Each selected incoming occurrence contributes its entire column,
with a pointwise flat join over just the marked occurrences. -/
def phiFacts {value : Data → Type w} [equal : BankDecidableEq value (dataPorts regs)]
    (marks : Marked) (column : Incoming → BankFacts value (dataPorts regs)) : BankFacts value (dataPorts regs) :=
  fun i =>
    letI := equal.atPort i
    (gate marks (incomingIndex .entry) (column .entry i) ⊔
      gate marks (incomingIndex (.feedback true)) (column (.feedback true) i)) ⊔
      gate marks (incomingIndex (.feedback false)) (column (.feedback false) i)

variable (m : Model.{u, v, w} Op) (p : Program Op regs out) [BankDecidableEq m.value (dataPorts regs)]
variable (input : Tuple (Fact m.value) (dataPorts regs))

def columns (current : Tuple (Fact m.value) (dataPorts regs)) : Incoming → BankFacts m.value (dataPorts regs)
  | .entry => tupleFacts (blockFacts m p.preheader input)
  | .feedback side => tupleFacts (blockFacts m (p.feedback side) current)

/-- Both possible feedback columns start from the same post-header abstract
bank. Control marks, Phi operands and return consume the old assignment. -/
def transfer (old : State m.value regs out) : State m.value regs out :=
  let current := blockFacts m p.header (bankTuple old.2.1)
  (insert (incomingIndex .entry)
      (if incomingIndex .entry ∈ old.1 then successors (current.get p.again) (current.get p.select) else ∅),
    phiFacts old.1 (columns m p input current), gate old.1 exitIndex (current.get p.result))

/-- Four marks, two strict increases per carried field, and two for return. -/
def height (value : Data → Type w) (regs : List (ValueSort Data)) (out : ValueSort Data) :
    HeightBound (State value regs out) :=
  (HeightBound.finset (Fin 4)).prod
    ((HeightBound.pi fun i => Flat.height (Val value (dataPorts regs)[i])).prod (Flat.height (sortValue value out)))

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP

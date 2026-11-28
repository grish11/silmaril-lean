module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.MemRef.Defs

/-! One ordered typed MemRef CFG for the static three-loop Boundary chain. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.MemRef

open RVSDG (Tuple)
open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Edge Terminator)
open Silmaril.MLIR.CF.Ordered (Block Cfg)
open Silmaril.MLIR.MemRef (Buffer)
open Silmaril.MLIR.Pure (Operands)
open Loop.MLIR.MemRef.CF (wordWidth resultTypes)
open Linked.MemRef (pairTypes carryOperands)
open TwoAddress.MemRef (Runtime)

abbrev tripleTypes : List Width := pairTypes ++ resultTypes

inductive Label (cells : Nat) : List Width → Type where
  | pair {ins : List Width} : Linked.MemRef.Label cells ins → Label cells ins
  | thirdEntry : Label cells pairTypes
  | third {ins : List Width} : TwoAddress.MemRef.Label cells ins → Label cells (pairTypes ++ ins)

inductive Body (cells : Nat) (ambient next last : List ValueSort) : List Width → List Width → Type where
  | pair {ins outs : List Width} :
      Linked.MemRef.Body cells ambient next ins outs → Body cells ambient next last ins outs
  | third {ins outs : List Width} :
      TwoAddress.MemRef.Body cells last ins outs → Body cells ambient next last (pairTypes ++ ins) (pairTypes ++ outs)

variable {cells : Nat} {ambient next last : List ValueSort} {scope : List Width}

def pairEdge (edge : Edge (Linked.MemRef.Label cells) scope) : Edge (Label cells) scope :=
  ⟨.pair edge.label, edge.args⟩

/-- Keep both earlier words in front of the third stage's own typed arguments. -/
def keepPair {delta : List Width} (operands : Operands scope delta) :
    Operands (pairTypes ++ scope) (pairTypes ++ delta) :=
  .cons .here (.cons (.there .here) (carryOperands (carryOperands operands)))

def thirdEdge (edge : Edge (TwoAddress.MemRef.Label cells) scope) : Edge (Label cells) (pairTypes ++ scope) :=
  ⟨.third edge.label, keepPair edge.args⟩

def pairTerm : Terminator (Linked.MemRef.Label cells) pairTypes scope →
    Terminator (Label cells) tripleTypes scope
  | .br edge => .br (pairEdge edge)
  | .condBr test yes no => .condBr test (pairEdge yes) (pairEdge no)
  | .ret values => .br ⟨.thirdEntry, values⟩

def thirdTerm : Terminator (TwoAddress.MemRef.Label cells) resultTypes scope →
    Terminator (Label cells) tripleTypes (pairTypes ++ scope)
  | .br edge => .br (thirdEdge edge)
  | .condBr test yes no => .condBr (.there (.there test)) (thirdEdge yes) (thirdEdge no)
  | .ret values => .ret (keepPair values)

def pairBlock (block : Block (Linked.MemRef.Body cells ambient next)
    (Linked.MemRef.Label cells) scope pairTypes) :
    Block (Body cells ambient next last) (Label cells) scope tripleTypes :=
  ⟨.pair block.body, pairTerm block.terminator⟩

def thirdBlock (block : Block (TwoAddress.MemRef.Body cells last)
    (TwoAddress.MemRef.Label cells) scope resultTypes) :
    Block (Body cells ambient next last) (Label cells) (pairTypes ++ scope) tripleTypes :=
  ⟨.third block.body, thirdTerm block.terminator⟩

/-- The last loop reads the second word and the second stage's typed entry captures. -/
def selectThird (firstWiring : Boundary.Wiring ambient next) (secondWiring : Boundary.Wiring next last)
    (input : Tuple (Val cells) ambient) (firstWord secondWord : Word) : Tuple (Val cells) last :=
  secondWiring.select secondWord (firstWiring.select firstWord input)

/-- Interpret the reused blocks in the single shared buffer monad. -/
def evalBody (firstWiring : Boundary.Wiring ambient next) (secondWiring : Boundary.Wiring next last)
    (input : Tuple (Val cells) ambient) :
    {ins outs : List Width} → Body cells ambient next last ins outs → Env ins → Runtime cells (Env outs)
  | _, _, .pair code, env => Linked.MemRef.evalBody firstWiring input code env
  | _, _, .third code, .cons firstWord (.cons secondWord env) => do
    let output ← TwoAddress.MemRef.evalBody (selectThird firstWiring secondWiring input firstWord secondWord) code env
    pure (.cons firstWord (.cons secondWord output))

/-- Redirect the actual pair exit to the actual third entry, leaving all
buffer effects in the original block bodies. -/
def lower (cells : Nat) (first : Graph ambient) (second : Graph next) (third : Graph last) :
    Cfg (Body cells ambient next last) (Label cells) [] tripleTypes where
  entry := pairBlock (Linked.MemRef.lower cells first second).entry
  block
    | .pair label => pairBlock ((Linked.MemRef.lower cells first second).block label)
    | .thirdEntry => thirdBlock (TwoAddress.MemRef.lower cells third).entry
    | .third label => thirdBlock ((TwoAddress.MemRef.lower cells third).block label)

abbrev Result (cells : Nat) := Word × Word × Word × Buffer cells

def runFuel (first : Graph ambient) (second : Graph next) (third : Graph last)
    (firstWiring : Boundary.Wiring ambient next) (secondWiring : Boundary.Wiring next last)
    (input : Tuple (Val cells) ambient) (fuel : Nat) (initial : Buffer cells) : Option (Result cells) := do
  let (returned, final) ← ((lower cells first second third).run (evalBody firstWiring secondWiring input) fuel .nil).run
    initial
  returned.map fun values => (values.get .here, values.get (.there .here), values.get (.there (.there .here)), final)

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.MemRef

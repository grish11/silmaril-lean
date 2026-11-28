module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery.MemRef.CF.Defs
public import Silmaril.SSA.MLIR.SCF.IndexSwitch.Defs
import Mathlib.Data.List.Nodup

/-! Emit a single ordered MemRef CFG with a typed switch over Region occurrences. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF

open RVSDG (Tuple)
open Quads.CFG (Predecessors)
open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Edge Frame)
open Silmaril.MLIR.CF.SwitchAssert (Switch Terminator)
open Silmaril.MLIR.MemRef (Buffer)
open Silmaril.MLIR.SCF.IndexSwitch (indexWidth)
open Discovery.MemRef.CF (Code enter resultTypes runWord)
open SeaOfNodes.Memory.MLIR.MemRef renaming lower → lowerMemory

variable {args : List ValueSort} {cells sites : Nat}

abbrev inputTypes : List Width := [indexWidth]

/-- The exact unsigned occurrence positions fit the existing i64 switch. -/
abbrev Fits (preds : Predecessors sites) : Prop :=
  preds.rest.length + 1 ≤ 2 ^ indexWidth.val

def selectorBits (preds : Predecessors sites) (fits : Fits preds) (arrival : Occurrence preds) :
    BitVec indexWidth.val :=
  BitVec.ofNatLT arrival.val (Nat.lt_of_lt_of_le arrival.isLt fits)

def selectorEnv (preds : Predecessors sites) (fits : Fits preds) (arrival : Occurrence preds) :
    Env inputTypes :=
  .cons (selectorBits preds fits arrival) .nil

inductive Label (preds : Predecessors sites) : List Width → Type where
  | arm (arrival : Occurrence preds) : Label preds []
  | join : Label preds resultTypes

def armEdge (preds : Predecessors sites) (arrival : Occurrence preds) : Edge (Label preds) inputTypes :=
  ⟨.arm arrival, .nil⟩

def switchCase (preds : Predecessors sites) (fits : Fits preds) (arrival : Occurrence preds) :
    BitVec indexWidth.val × Edge (Label preds) inputTypes :=
  (selectorBits preds fits arrival, armEdge preds arrival)

/-- The switch labels are positions in the original predecessor bank. -/
def dispatch (preds : Predecessors sites) (fits : Fits preds) : Switch (Label preds) inputTypes where
  flag := .here
  widthSupported := by decide
  defaultEdge := armEdge preds 0
  cases := (List.finRange (preds.rest.length + 1)).map (switchCase preds fits)
  unique := by
    rw [List.map_map]
    apply List.Nodup.map _ (List.nodup_finRange _)
    intro first second same
    exact Fin.ext (by simpa [switchCase, selectorBits, Function.comp_def] using congrArg BitVec.toNat same)

structure Entry (cells : Nat) (args : List ValueSort) (preds : Predecessors sites) where
  memory : Option (Code cells args)
  switch : Switch (Label preds) inputTypes

inductive Body (cells : Nat) (args : List ValueSort) : List Width → List Width → Type where
  | arm (code : Code cells args) : Body cells args inputTypes resultTypes
  | join (code : Code cells (.word :: args)) : Body cells args (resultTypes ++ inputTypes) resultTypes

abbrev Block (cells : Nat) (args : List ValueSort) (preds : Predecessors sites) (scope : List Width) :=
  Silmaril.MLIR.CF.Ordered.Block (Body cells args) (Label preds) scope resultTypes

/-- One switch entry, the occurrence blocks, and one typed continuation. -/
structure Program (cells : Nat) (args : List ValueSort) (preds : Predecessors sites) where
  fits : Fits preds
  entry : Entry cells args preds
  block : ∀ {ins}, Label preds ins → Block cells args preds (ins ++ inputTypes)

def evalBody (input : Tuple (Val cells) args) :
    {ins outs : List Width} → Body cells args ins outs → Env ins → StateM (Buffer cells) (Env outs)
  | _, _, .arm code, _ => fun initial =>
    let (word, buffer) := runWord code input initial
    (.cons word .nil, buffer)
  | _, _, .join code, env => fun initial =>
    let (word, buffer) := runWord code (.cons (env.get .here) input) initial
    (.cons word .nil, buffer)

inductive Scheduled (cells : Nat) (args : List ValueSort) (preds : Predecessors sites) : List Width → Type where
  | entry (code : Entry cells args preds) : Scheduled cells args preds inputTypes
  | block {scope : List Width} (code : Block cells args preds scope) : Scheduled cells args preds scope

variable {preds : Predecessors sites}

/-- Use the existing switch terminator and ordered block evaluator with
the same buffer state. -/
def eval (input : Tuple (Val cells) args) :
    {scope : List Width} → Scheduled cells args preds scope → Env scope →
      StateM (Buffer cells) (Frame (Label preds) ⊕ Env resultTypes)
  | _, .entry code, env => fun initial =>
    (Terminator.eval env (.switch code.switch), enter code.memory input initial)
  | _, .block code, env => code.eval (evalBody input) env

def run (program : Program cells args preds) (input : Tuple (Val cells) args)
    (arrival : Occurrence preds) (fuel : Nat) (initial : Buffer cells) : Option (Word × Buffer cells) :=
  let env := selectorEnv preds program.fits arrival
  let (result, final) := Silmaril.MLIR.CF.Ordered.runBlock
    (fun label => .block (program.block label)) (eval input) env fuel (.entry program.entry) env initial
  result.map fun words => (words.get .here, final)

def entryTransition (program : Program cells args preds) (input : Tuple (Val cells) args)
    (arrival : Occurrence preds) (initial : Buffer cells) : (Frame (Label preds) ⊕ Env resultTypes) × Buffer cells :=
  eval input (.entry program.entry) (selectorEnv preds program.fits arrival) initial

def armTransition (program : Program cells args preds) (input : Tuple (Val cells) args)
    (arrival : Occurrence preds) (initial : Buffer cells) : (Frame (Label preds) ⊕ Env resultTypes) × Buffer cells :=
  (program.block (.arm arrival)).eval (evalBody input) (selectorEnv preds program.fits arrival) initial

def lowerBank (preds : Predecessors sites) (fits : Fits preds) (cells : Nat)
    (entry : Option (Memory.Graph args)) (arm : Occurrence preds → Memory.Graph args)
    (suffix : Memory.Graph (.word :: args)) : Program cells args preds where
  fits := fits
  entry := ⟨entry.map (lowerMemory cells), dispatch preds fits⟩
  block
    | .arm arrival => ⟨.arm (lowerMemory cells (arm arrival)), .br ⟨.join, .cons .here .nil⟩⟩
    | .join => ⟨.join (lowerMemory cells suffix), .ret (.cons .here .nil)⟩

structure Programs (cells : Nat) (args : List ValueSort) (preds : Predecessors sites) where
  input : Tuple (Val cells) args
  original : Program cells args preds
  optimized : Program cells args preds

/-- Emit both whole CFGs only after checking every incoming occurrence. -/
def lower (preds : Predecessors sites) (fits : Fits preds) (store : PrefixStore args)
    (arm : Occurrence preds → Memory.Graph args) (candidate : Candidate args preds)
    (suffix : Memory.Graph (.word :: args)) (input : Tuple (Val cells) args) : Option (Programs cells args preds) := do
  let edited ← check preds store arm candidate input
  some ⟨input, lowerBank preds fits cells (some store.table) arm suffix,
    lowerBank preds fits cells none (fun i => edited[i.val]) suffix⟩

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF

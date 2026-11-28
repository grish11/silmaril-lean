module

public import Silmaril.SSA.MLIR.CF.Ordered.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.MLIR.MemRef.Defs

/-! Emit the original and checked memory diamonds as ordered MemRef CF. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery.MemRef.CF

open RVSDG (Tuple)
open SeaOfNodes.Diamond (Slot)
open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.MemRef (Block Buffer wordPorts)
open Silmaril.MLIR.Pure (i1)
open SeaOfNodes.Memory.MLIR.MemRef (encodeInput entryPorts)
open SeaOfNodes.Memory.MLIR.MemRef renaming lower → lowerMemory

abbrev resultTypes : List Width := [⟨64, by decide⟩]
abbrev entryTypes : List Width := [i1]

abbrev Code (cells : Nat) (args : List ValueSort) :=
  Block cells [entryPorts cells args] (wordPorts cells)

inductive Label : List Width → Type where
  | arm (arrival : Slot) : Label []
  | join : Label resultTypes

/-- The scalar valuation is invariant in the CF runner. The entry tests
the predicate, and each arm passes its word as the join argument. -/
inductive Body (cells : Nat) (args : List ValueSort) : List Width → List Width → Type where
  | entry (entryBody : Option (Code cells args)) : Body cells args entryTypes entryTypes
  | arm (code : Code cells args) : Body cells args entryTypes resultTypes
  | join (code : Code cells (.word :: args)) : Body cells args (resultTypes ++ entryTypes) resultTypes

abbrev Program (cells : Nat) (args : List ValueSort) :=
  Silmaril.MLIR.CF.Ordered.Cfg (Body cells args) Label entryTypes resultTypes

variable {cells : Nat} {args : List ValueSort}

def runWord (code : Code cells args) (input : Tuple (Val cells) args) (initial : Buffer cells) :
    Word × Buffer cells :=
  let (values, final) := Silmaril.MLIR.MemRef.run code (encodeInput input, PUnit.unit) initial
  (values.get .head, final)

def enter (entryBody : Option (Code cells args)) (input : Tuple (Val cells) args)
    (initial : Buffer cells) : Buffer cells :=
  match entryBody with
  | none => initial
  | some code => (runWord code input initial).2

def evalBody (input : Tuple (Val cells) args) :
    {ins outs : List Width} → Body cells args ins outs → Env ins → StateM (Buffer cells) (Env outs)
  | _, _, .entry entryBody, env => fun initial => (env, enter entryBody input initial)
  | _, _, .arm code, _ => fun initial =>
    let result := runWord code input initial
    (.cons result.1 .nil, result.2)
  | _, _, .join code, env => fun initial =>
    let result := runWord code (.cons (env.get .here) input) initial
    (.cons result.1 .nil, result.2)

/-- Labels retain their Region slot order. The buffer is threaded by the
existing ordered scheduler through entry, the selected arm, and the join. -/
def lowerDiamond (cells : Nat) (graph : Graph args) (entryBody : Option (Memory.Graph args)) :
    Program cells args where
  entry := ⟨.entry (entryBody.map (lowerMemory cells)), .condBr .here
    ⟨.arm (graph.merge.slot .onTrue), .nil⟩ ⟨.arm (graph.merge.slot .onFalse), .nil⟩⟩
  block
    | .arm arrival => ⟨.arm (lowerMemory cells (graph.arm (graph.merge.predecessor arrival))),
        .br ⟨.join, .cons .here .nil⟩⟩
    | .join => ⟨.join (lowerMemory cells graph.suffix), .ret (.cons .here .nil)⟩

def run (program : Program cells args) (input : Tuple (Val cells) args) (guard : Bool) (fuel : Nat)
    (initial : Buffer cells) : Option (Word × Buffer cells) :=
  let (result, final) := program.run (evalBody input) fuel (.cons (BitVec.ofBool guard) .nil) initial
  result.map fun values => (values.get .here, final)

/-- Execute the emitted entry once, exposing its CF outcome and full buffer. -/
def entryTransition (program : Program cells args) (input : Tuple (Val cells) args) (guard : Bool)
    (initial : Buffer cells) : (Silmaril.MLIR.CF.Frame Label ⊕ Env resultTypes) × Buffer cells :=
  program.entry.eval (evalBody input) (.cons (BitVec.ofBool guard) .nil) initial

/-- Read the destination and block arguments produced by the entry terminator. -/
def entryDestination (program : Program cells args) (input : Tuple (Val cells) args) (guard : Bool)
    (initial : Buffer cells) : Silmaril.MLIR.CF.Frame Label ⊕ Env resultTypes :=
  (entryTransition program input guard initial).1

structure Programs (cells : Nat) (args : List ValueSort) where
  input : Tuple (Val cells) args
  original : Program cells args
  optimized : Program cells args

/-- Emit only after both route certificates are accepted at this input. -/
def lower (source : Prefixed args) (input : Tuple (Val cells) args) : Option (Programs cells args) := do
  let result ← Discovery.rewrite source input
  some ⟨input, lowerDiamond cells source.diamond (some source.store.table),
    lowerDiamond cells result.graph none⟩

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery.MemRef.CF

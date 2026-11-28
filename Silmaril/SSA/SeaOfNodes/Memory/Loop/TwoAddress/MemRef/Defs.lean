module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF.Defs

/-! An ordered MemRef CFG whose header has two address block arguments. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.MemRef

open RVSDG (Port Tuple)
open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF.Ordered (Cfg)
open Silmaril.MLIR.MemRef (Buffer)
open Silmaril.MLIR.Pure (i1)
open Loop.MLIR.MemRef (Activation evalActivation lowerActivation)
open Loop.MLIR.MemRef.CF (resultTypes)

variable {cells : Nat} {args : List ValueSort}

/-- A positive signless width that can represent every in-bounds address. -/
abbrev addressWidth (cells : Nat) : Width := ⟨cells.log2 + 1, Nat.zero_lt_succ _⟩

def encodeAddress (address : Address cells) : BitVec (addressWidth cells).val :=
  BitVec.ofNat _ address.val

/-- Reject a bit pattern outside the single initialized buffer. -/
def decodeAddress (value : BitVec (addressWidth cells).val) : Option (Address cells) :=
  if h : value.toNat < cells then some ⟨value.toNat, h⟩ else none

abbrev headerTypes (cells : Nat) : List Width := [addressWidth cells, addressWidth cells]

def encodeAddresses (first second : Address cells) : Env (headerTypes cells) :=
  .cons (encodeAddress first) (.cons (encodeAddress second) .nil)

def decodeAddresses (env : Env (headerTypes cells)) : Option (Address cells × Address cells) := do
  let first ← decodeAddress (env.get .here)
  let second ← decodeAddress (env.get (.there .here))
  pure (first, second)

inductive Label (cells : Nat) : List Width → Type where
  | header : Label cells (headerTypes cells)
  | exit : Label cells resultTypes

abbrev activationTypes (cells : Nat) := i1 :: (resultTypes ++ headerTypes cells)

/-- The body instructions and both address Phi columns are fixed by lowering.
The header passes the effectful activation's selector, word and two routed
addresses to the typed terminator. -/
inductive Body (cells : Nat) (args : List ValueSort) : List Width → List Width → Type where
  | entry (first second : Port args .address) : Body cells args [] (headerTypes cells)
  | activation (code : Activation cells (activationArgs args))
      (first second : Port (activationArgs args) .address) :
      Body cells args (headerTypes cells) (activationTypes cells)
  | exit : Body cells args resultTypes resultTypes

/-- The buffer is the existing MemRef state. An invalid raw header
operand fails before a load or store can run. -/
abbrev Runtime (cells : Nat) := StateT (Buffer cells) Option

def evalBody (input : Tuple (Val cells) args) :
    {ins outs : List Width} → Body cells args ins outs → Env ins → Runtime cells (Env outs)
  | _, _, .entry first second, _ =>
    pure (encodeAddresses (input.get first) (input.get second))
  | _, _, .activation code first second, env => fun buffer => do
    let (oldFirst, oldSecond) ← decodeAddresses env
    let oldBank : Tuple (Val cells) (activationArgs args) := .cons oldFirst (.cons oldSecond input)
    let (.cons selector (.cons word .nil), final) := evalActivation code oldBank buffer
    let routed := encodeAddresses (oldBank.get first) (oldBank.get second)
    pure (.cons (BitVec.ofBool (selector.down != 0)) (.cons word routed), final)
  | _, _, .exit, env => pure env

abbrev Program (cells : Nat) (args : List ValueSort) := Cfg (Body cells args) (Label cells) [] resultTypes

/-- The entry and feedback edges pass both address block arguments. The
exit edge passes the word. All blocks share the one initialized buffer. -/
def lower (cells : Nat) (graph : Graph args) : Program cells args where
  entry := ⟨.entry graph.entryFirst graph.entrySecond, .br ⟨.header, .cons .here (.cons (.there .here) .nil)⟩⟩
  block
    | .header => ⟨.activation (lowerActivation cells graph.activation) graph.feedbackFirst graph.feedbackSecond,
        .condBr .here
          ⟨.header, .cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)⟩
          ⟨.exit, .cons (.there .here) .nil⟩⟩
    | .exit => ⟨.exit, .ret (.cons .here .nil)⟩

/-- Observe a typed CFG at raw block fuel, including its whole final buffer. -/
def runProgram (program : Program cells args) (input : Tuple (Val cells) args)
    (fuel : Nat) (initial : Buffer cells) : Option (Word × Buffer cells) := do
  let (result, final) ← (program.run (evalBody input) fuel .nil).run initial
  result.map fun values => (values.get .here, final)

/-- Execute the emitted CFG at raw block fuel. -/
def runFuel (graph : Graph args) (input : Tuple (Val cells) args)
    (fuel : Nat) (initial : Buffer cells) : Option (Word × Buffer cells) :=
  runProgram (lower cells graph) input fuel initial

/-- Allow the entry block, the initial header, the requested backedges,
and the exit block. -/
def run (graph : Graph args) (input : Tuple (Val cells) args)
    (budget : Nat) (initial : Buffer cells) : Option (Word × Buffer cells) :=
  runFuel graph input (budget + 3) initial

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.MemRef

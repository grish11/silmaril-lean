module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Defs

/-! A nonempty ordered family of feedback columns over one guarded table. -/

@[expose] public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family

open Silmaril.Machine.Lir (Word Memory)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.RTL.SSA (Block Func Prog StepsNWithin step)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy Reg model)
open Silmaril.SSA.RVSDG (extend)
open Silmaril.SSA.SeaOfNodes.Diamond (read)
open Silmaril.SSA.SeaOfNodes.Loop (appendTuple)

variable {captures bank old new tests : Nat} {entrySigs sigs : List (List PortTy)}

/-- One typed column per test, plus a final default. A nonzero test takes its
column, and a zero test continues to the next block. -/
inductive Choices (captures bank : Nat) (sigs : List (List PortTy)) : Nat → Type where
  | last : Feedback captures bank sigs → Choices captures bank sigs 0
  | test {n : Nat} : HeaderWord captures bank sigs → Feedback captures bank sigs → Choices captures bank sigs n →
      Choices captures bank sigs (n + 1)

def Choices.column : {tests : Nat} → Choices captures bank sigs tests → Fin (tests + 1) → Feedback captures bank sigs
  | _, .last column, _ => column
  | _, .test _ column tail, i => Fin.cases column tail.column i

/-- Native dispatch reads the typed selector wires in priority order. -/
def Choices.select (value : HeaderWord captures bank sigs → Word) :
    {tests : Nat} → Choices captures bank sigs tests → Fin (tests + 1)
  | _, .last _ => 0
  | _, .test selector _ tail => if value selector = 0 then (tail.select value).succ else 0

def Choices.mapCaptures (mapping : InputMap old new) :
    {tests : Nat} → Choices old bank sigs tests → Choices new bank sigs tests
  | _, .last column => .last (mapColumn (fun p => Width.headerPort mapping p) column)
  | _, .test selector column tail =>
    .test (mapOrigin (fun p => Width.headerPort mapping p) selector)
      (mapColumn (fun p => Width.headerPort mapping p) column) (tail.mapCaptures mapping)

/-- All tests and columns see the same completed producer table. -/
structure Source (captures bank : Nat) (entrySigs sigs : List (List PortTy)) (tests : Nat) where
  primary : Width.Source captures bank entrySigs sigs
  rows : Choices captures bank sigs tests

variable (p : Source captures bank entrySigs sigs tests)

def Source.row (slot : Fin (tests + 1)) : Width.Source captures bank entrySigs sigs :=
  withFeedback p.primary (p.rows.column slot)

def Source.select (input : WordTuple captures) (carried : WordTuple bank) : Fin (tests + 1) :=
  let args := appendTuple carried input
  let locals := p.primary.header.eval model args PUnit.unit
  p.rows.select (fun origin => read model origin args locals)

def Source.step (input : WordTuple captures) (carried : WordTuple bank) :
    Word ⊕ (Fin (tests + 1) × WordTuple bank) :=
  let slot := p.select input carried
  match (p.row slot).step model input carried with
  | .inl result => .inl result
  | .inr next => .inr (slot, next)

/-- Finite native returns record the chosen slots in chronological order. -/
inductive Source.ReturnsAlong (input : WordTuple captures) :
    List (Fin (tests + 1)) → WordTuple bank → Word → Prop
  | exit {carried value} (taken : p.step input carried = .inl value) :
      ReturnsAlong input [] carried value
  | feedback {slots carried slot next value} (taken : p.step input carried = .inr (slot, next))
      (rest : ReturnsAlong input slots next value) :
      ReturnsAlong input (slot :: slots) carried value

def mapCaptures (mapping : InputMap old new) (p : Source old bank entrySigs sigs tests) :
    Source new bank entrySigs sigs tests :=
  ⟨Width.mapCaptures mapping p.primary, p.rows.mapCaptures mapping⟩

/-- The successful transfers all target block 1. Their source blocks have
consecutive labels and each transfer is successor zero of its source. -/
def Choices.blocks (first : Nat) : {tests : Nat} → Choices captures bank sigs tests → List (Block Reg)
  | _, .last column => [⟨[], [], .jump 1 (emitColumn column)⟩]
  | _, .test selector column tail =>
    ⟨[], [], .cond (register selector.address) 1 (emitColumn column) (first + 1) []⟩ ::
      tail.blocks (first + 1)

def occurrence (slot : Fin (tests + 1)) : Nat × Nat := (3 + slot.val, 0)

def header : Block Reg :=
  { Width.header p.primary with
    term := .cond (register p.primary.predicate.address) 3 [] 2 [register p.primary.result.address] }

def lowerFunc : Func Reg :=
  ⟨⟨captures, 1⟩, 0, [Width.preheader p.primary, header p, exitBlock] ++ Choices.blocks 3 p.rows⟩

def lowerRTL : Prog Reg := ⟨[lowerFunc p]⟩

def admitsRows (p : Source old old entrySigs sigs tests) : Bool :=
  (List.finRange (tests + 1)).all fun i => (Table.lowerChecked (p.row i)).isSome

/-- Each original projection goes through the ordinary guarded-row checker.
Check the actual emitted function at the new capture width. -/
def lowerChecked (mapping : InputMap old new) (p : Source old old entrySigs sigs tests) :
    Option (Prog Reg) :=
  if admitsRows p then
    let mapped := mapCaptures mapping p
    if (lowerFunc mapped).WellFormed then some (lowerRTL mapped) else none
  else none

/-- The last instruction of a returning visit is the return itself. Each
continuing visit pays for the inspected prefix of the dispatch chain. -/
def visitFuel (sigs : List (List PortTy)) : List (Fin (tests + 1)) → Nat
  | [] => sigs.length + 2
  | slot :: rest => (sigs.length + 1 + (slot.val + 1)) + visitFuel sigs rest

def rtlFuel (entrySigs sigs : List (List PortTy)) (slots : List (Fin (tests + 1))) : Nat :=
  entrySigs.length + 1 + visitFuel sigs slots

/-- In the continuing case all inspected tests preserve the pre-transfer
frame. The chosen occurrence then reads the full packet and rebinds the bank. -/
def Activation (prog : Prog Reg) (input : WordTuple captures) (fr : Frame Reg) (mem : Memory)
    (outcome : Word ⊕ (Fin (tests + 1) × WordTuple bank)) : Prop :=
  match outcome with
  | .inl value =>
    ∃ ready, StepsNWithin prog [] (sigs.length + 1) ⟨⟨0, 1, 0⟩, fr, [], mem⟩
      ⟨⟨0, 2, 0⟩, ready, [], mem⟩ ∧
      step prog ⟨⟨0, 2, 0⟩, ready, [], mem⟩ = .returned [value] mem
  | .inr (slot, values) =>
    ∃ ready latched b, StepsNWithin prog [] (sigs.length + 1 + slot.val) ⟨⟨0, 1, 0⟩, fr, [], mem⟩
      ⟨⟨0, (occurrence slot).1, 0⟩, ready, [], mem⟩ ∧
      prog.block? 0 (occurrence slot).1 = some b ∧
      b.term.args[(occurrence slot).2]? = some (1, emitColumn (p.rows.column slot)) ∧
      ready.readAll (emitColumn (p.rows.column slot)) = some (words values) ∧
      step prog ⟨⟨0, (occurrence slot).1, 0⟩, ready, [], mem⟩ =
        .running ⟨⟨0, 1, 0⟩, latched, [], mem⟩ ∧
      ArgsMatch latched (appendTuple values input)

/-- Skipped dispatchers advance by one occurrence without rebinding any word. -/
def Fallthrough (prog : Prog Reg) (first count : Nat) (ready : Frame Reg) (mem : Memory) : Prop :=
  ∀ offset < count, step prog ⟨⟨0, first + offset, 0⟩, ready, [], mem⟩ =
    .running ⟨⟨0, first + offset + 1, 0⟩, ready, [], mem⟩

/-- The false header successor carries one word to block 2. Producer
steps use the old arguments, and the branch rebinds just the exit parameter. -/
structure ExitCut (prog : Prog Reg) (input : WordTuple captures) (carried : WordTuple bank)
    (before ready : Frame Reg) (mem : Memory) (value : Word) : Prop where
  produced : StepsNWithin prog [] sigs.length
    ⟨⟨0, 1, 0⟩, before, [], mem⟩ ⟨⟨0, 1, sigs.length⟩, ready, [], mem⟩
  zero : (read model p.primary.predicate (appendTuple carried input)
    (p.primary.header.eval model (appendTuple carried input) PUnit.unit)).down = false
  result_eq : read model p.primary.result (appendTuple carried input)
    (p.primary.header.eval model (appendTuple carried input) PUnit.unit) = value
  guard : ready.get (register p.primary.predicate.address) = some 0
  operand : (prog.block? 0 1).bind (fun block => block.term.args[1]?) =
    some (2, [register p.primary.result.address])
  packet : ready.readAll [register p.primary.result.address] = some [value]
  rebound : ArgsMatch ready (appendTuple carried input)
  branch : step prog ⟨⟨0, 1, sigs.length⟩, ready, [], mem⟩ =
    .running ⟨⟨0, 2, 0⟩, ready.set .phi value, [], mem⟩
  returned : step prog ⟨⟨0, 2, 0⟩, ready.set .phi value, [], mem⟩ = .returned [value] mem

/-- Evidence from one actual continuing header and its selected feedback edge. -/
structure FeedbackCut (prog : Prog Reg) (input : WordTuple captures) (carried : WordTuple bank)
    (before ready latched : Frame Reg) (mem : Memory) (slot : Fin (tests + 1))
    (values : WordTuple bank) (block : Block Reg) : Prop where
  entered : StepsNWithin prog [] (sigs.length + 1)
    ⟨⟨0, 1, 0⟩, before, [], mem⟩ ⟨⟨0, 3, 0⟩, ready, [], mem⟩
  continuing : (read model p.primary.predicate (appendTuple carried input)
    (p.primary.header.eval model (appendTuple carried input) PUnit.unit)).down = true
  reads : ∀ wire : HeaderWord captures bank sigs,
    ready.get (register wire.address) = some (read model wire (appendTuple carried input)
      (p.primary.header.eval model (appendTuple carried input) PUnit.unit))
  skipped : StepsNWithin prog [] slot.val ⟨⟨0, 3, 0⟩, ready, [], mem⟩
    ⟨⟨0, (occurrence slot).1, 0⟩, ready, [], mem⟩
  fallthrough : Fallthrough prog 3 slot.val ready mem
  found : prog.block? 0 (occurrence slot).1 = some block
  operand : block.term.args[(occurrence slot).2]? = some (1, emitColumn (p.rows.column slot))
  packet : ready.readAll (emitColumn (p.rows.column slot)) = some (words values)
  feedback : step prog ⟨⟨0, (occurrence slot).1, 0⟩, ready, [], mem⟩ =
    .running ⟨⟨0, 1, 0⟩, latched, [], mem⟩
  rebound : ArgsMatch latched (appendTuple values input)

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family

module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible.Defs
public import Mathlib.Data.Fintype.Pi

/-! Finite weak trace comparison for fixed-width Boolean packets. -/

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible.Multi

open Silmaril.Elgot.ITree (Tree ExchangePath)
open Silmaril.Elgot.ITree.Finite (Event)
open Silmaril.Isotope (Value)
open Silmaril.Isotope.Bridge.NamedFlat (treeModel treeExitNumber)

variable {F : Type} {a b n : Nat}

inductive Instruction (F K : Type) (width : Nat) where
  | jump (target : K)
  | branch (field : Fin width) (onTrue onFalse : K)
  | apply (symbol : F) (argument destination : Fin width) (target : K)

/-- A common width fixes the packet type at every entry, private label and
exit. Every branch or primitive operand names an in-range Boolean field. -/
structure Program (F : Type) (inputs outputs width : Nat) where
  locals : Nat
  entry : Fin inputs → Label locals outputs
  block : Fin locals → Instruction F (Label locals outputs) width

abbrev Atom := Visible.Program.Atom
abbrev Register (width : Nat) := ULift.{1} (Option (Fin width))

def cursor : Register n := ⟨none⟩
def fieldReg (i : Fin n) : Register n := ⟨some i⟩

/-- Change exactly the selected slot. The primitive argument is read before
this update, even when the argument and destination coincide. -/
def replace (packet : Packet n) (destination : Fin n) (reply : Bool) : Packet n :=
  fun i => if i = destination then reply else packet i

def encodeFields (packet : Packet n) : List (Fin n) → Value Atom
  | [] => .unit
  | i :: rest => .pair (Visible.Program.bit (packet i)) (encodeFields packet rest)

/-- Right-nested pairs of Boolean values ending in unit. -/
def encode (packet : Packet n) : Value Atom := encodeFields packet (List.finRange n)

def packRegs : List (Fin n) → Val (Register n)
  | [] => .unit
  | i :: rest => .pair (.var (fieldReg i)) (packRegs rest)

/-- The cursor holds the unread tail. Field registers are disjoint from it. -/
def unpack {K : Type 1} : List (Fin n) → Body (Register n) K F → Body (Register n) K F
  | [], body => body
  | i :: rest, body =>
    .let2 (fieldReg i) cursor (.val (.var cursor)) (unpack rest body)

def store (packet : Packet n) : Register n → Value Atom :=
  upd (fun _ => .unit) cursor (encode packet)

namespace Program

variable (program : Program F a b n)

abbrev Address := ULift.{1} (Label program.locals b)
abbrev State := ULift.{1} (Label program.locals b × Packet n)
abbrev Result (b n : Nat) := ULift.{1} (Fin b × Packet n)

/-- Both normalization and product pruning use the complete packet at
each label, including fields not read by the current block. -/
def states : Finset program.State :=
  (Finset.univ : Finset (Label program.locals b × Packet n)).map ⟨ULift.up, ULift.up_injective⟩

theorem mem_states (state : program.State) : state ∈ program.states := by
  cases state
  simp [states]

def start (input : Fin a) (packet : Packet n) : program.State := ⟨program.entry input, packet⟩

def step (state : program.State) :
    Silmaril.Elgot.ITree.Finite.Step (F × Bool) (Result b n) program.State :=
  match state.down with
  | (.inr port, packet) => .inl (.result ⟨port, packet⟩)
  | (.inl index, packet) =>
    match program.block index with
    | .jump target => .inr ⟨target, packet⟩
    | .branch field yes no => .inr ⟨if packet field then yes else no, packet⟩
    | .apply symbol arg dst target =>
      .inl (.request (symbol, packet arg) fun reply => ⟨target, replace packet dst reply⟩)

def compiledBlock (instruction : Instruction F (Label program.locals b) n) :
    Block (Register n) program.Address F :=
  let fields := List.finRange n
  let packet := packRegs fields
  ⟨cursor, match instruction with
  | .jump target => .term (.br ⟨target⟩ (.var cursor))
  | .branch field yes no =>
    unpack fields (.term (.case (.val (.var (fieldReg field)))
      cursor (.br ⟨yes⟩ packet) cursor (.br ⟨no⟩ packet)))
  | .apply symbol arg dst target =>
    unpack fields (.let1 (fieldReg dst) (.app symbol (.var (fieldReg arg))) (.term (.br ⟨target⟩ packet)))⟩

def compile (input : Fin a) : CFG (Register n) program.Address F :=
  ⟨.term (.br ⟨program.entry input⟩ (.var cursor)),
    (List.finRange program.locals).map fun i => (⟨.inl i⟩, program.compiledBlock (program.block i))⟩

def exits : List program.Address := (List.finRange b).map fun i => ⟨.inr i⟩

def renderResult (result : Result b n) : Nat × Value Atom :=
  (result.down.1.val, encode result.down.2)

noncomputable def observe (input : Fin a) (packet : Packet n) :
    Tree (Event (F × Bool)) (Nat × Value Atom) :=
  CFG.Cyclic.runSSA (treeModel.{0, 0} Visible.Program.primitive) (program.compile input) (store packet) >>=
    fun result => pure (treeExitNumber program.exits result)

def refinementAt? [DecidableEq F] (right : Program F a b n) (input : Fin a) (packet : Packet n) : Bool :=
  Silmaril.Elgot.ITree.Finite.compare program.states right.states program.step right.step
    (program.start input packet) (right.start input packet)

def refinement? [DecidableEq F] (right : Program F a b n) : Bool :=
  (List.finRange a).all fun input =>
    (packets n).all fun packet => program.refinementAt? right input packet

def silentAfter? [DecidableEq F] (input : Fin a) (packet : Packet n)
    (path : ExchangePath (Event (F × Bool))) : Bool :=
  Silmaril.Elgot.ITree.Finite.silentAfter? program.step program.states (program.start input packet) path

def refinementAtWithSilence? [DecidableEq F] (right : Program F a b n) (input : Fin a) (packet : Packet n) : Bool :=
  program.refinementAt? right input packet && right.refinementAt? program input packet

end Program

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible.Multi

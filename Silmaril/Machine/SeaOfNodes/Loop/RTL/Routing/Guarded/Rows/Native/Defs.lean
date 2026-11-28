module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Defs

/-! Recover a checked row from a typed native signed-guard loop. -/

@[expose] public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native

open Silmaril.Machine.Lir (Word)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy WordOp)
open Silmaril.SSA.SeaOfNodes.Diamond (Dataflow ValueSort)
open Silmaril.SSA.RVSDG (Address)

/-- An opcode determines its operand and result sorts. Constants keep their
word payload so the schedule check can distinguish them. -/
inductive Opcode where
  | const (value : Word)
  | add
  | sub
  | eq
  | ne
  | slt
  deriving DecidableEq

def opcode {ins : List (ValueSort Unit)} {out : ValueSort Unit} : WordOp ins out → Opcode
  | .const value => .const value
  | .add => .add
  | .sub => .sub
  | .eq => .eq
  | .ne => .ne
  | .slt => .slt

def tableCode {args : List PortTy} :
    {past sigs : List (List PortTy)} → Dataflow WordOp args past sigs → List (Opcode × List Address)
  | _, _, .nil => []
  | _, _, .cons op operands rest => (opcode op, operands.addresses) :: tableCode rest

structure GraphCode where
  header : List (Opcode × List Address)
  entry : List Address
  feedback : List Address
  predicate : Address
  result : Address
  deriving DecidableEq

def graphCode {arity : Nat} {sigs : List (List PortTy)} (g : BankGraph arity sigs) : GraphCode :=
  ⟨tableCode g.header, (g.phiInputs .entry).addresses, (g.phiInputs .backedge).addresses,
    g.predicate.address, g.result.address⟩

namespace Decode

def argument : Address → Option Nat
  | .arg i => some i
  | .output _ _ => none

def oldSlot (arity : Nat) (wire : Address) : Option Nat := do
  let i ← argument wire
  if arity ≤ i then some (i - arity) else none

def arithmetic : Opcode → Option FeedbackOp
  | .add => some .add
  | .sub => some .sub
  | _ => none

def decodeUpdate (arity : Nat) (feedback : List Address) (producer : Nat)
    (node : Opcode × List Address) : Option FeedbackSpec := do
  let (op, [lhs, rhs]) := node | none
  let operation ← arithmetic op
  let destination ← feedback.idxOf? (.output producer 0)
  let left ← oldSlot arity lhs
  let right ← oldSlot arity rhs
  some ⟨operation, destination, left, right⟩

def copySlot (arity : Nat) (slot : Nat) (wire : Address) : Option Nat :=
  match wire with
  | .arg _ => oldSlot arity wire
  | .output _ _ => some slot -- The checked row replaces this copy with a producer.

def decodeExit (arity : Nat) (updates : List FeedbackSpec) (wire : Address) :
    Option (Nat × Option Address) :=
  match wire with
  | .arg _ => (oldSlot arity wire).map (fun slot => (slot, none))
  | .output producer 0 => updates[producer]?.map (fun update => (update.destination, some wire))
  | .output _ (_ + 1) => none

/-- Convert a header argument address to bank-local numbering. A producer
address keeps its absolute index for the existing row checker. -/
def guardRhs (arity : Nat) (wire : Address) : Option Address :=
  match wire with
  | .arg _ => (oldSlot arity wire).map Address.arg
  | .output _ _ => some wire

/-- Recover a row from the two incoming columns and a final signed comparison
of a computed result with an old bank field or a distinct row result. -/
def spec (arity : Nat) (code : GraphCode) : Option Spec := do
  let (.slt, [lhs@(.output left 0), rhs]) :: revRow := code.header.reverse | none
  let updates ← revRow.reverse.zipIdx.mapM (fun (node, producer) =>
    decodeUpdate arity code.feedback producer node)
  let guard ← updates[left]?
  let rhs ← guardRhs arity rhs
  let entry ← code.entry.mapM argument
  let copies ← code.feedback.zipIdx.mapM (fun (wire, slot) => copySlot arity slot wire)
  let (exitSlot, exitOrigin) ← decodeExit arity updates code.result
  some ⟨entry, copies, updates, lhs, guard.destination, .slt, 0, exitSlot, exitOrigin, some rhs⟩

end Decode

/-- Recheck the candidate and verify the complete reconstructed graph code.
This also checks the predicate wire and rejects duplicate uses of a row
producer in the feedback column. -/
def recognize {arity : Nat} {sigs : List (List PortTy)} (g : BankGraph arity sigs) : Option Spec :=
  let code := graphCode g
  (Decode.spec arity code).bind fun spec =>
    (Rows.checkPlan arity spec).bind fun plan =>
      if code = graphCode plan.graph then some spec else none

/-- Use the existing guarded-row checker and both emitters. -/
def lowerChecked {arity : Nat} {sigs : List (List PortTy)} (g : BankGraph arity sigs) :
    Option Checked.Phi.Targets :=
  (recognize g).bind (Rows.lowerChecked arity)

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native

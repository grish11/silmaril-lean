module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Defs
public import Silmaril.Logic.ITree.Institution.Trace.Defs

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible

open Silmaril.Elgot.ITree (TraceSignature HasTrace)
open Silmaril.Elgot.ITree.Finite (Event replyHandler compareUnder statefulReplyHandler compareWithHandler)
open Silmaril.Logic.ITree
open Silmaril.Isotope.LambdaSSA

/-- Use the checker and runner's opcode, typed argument, and exact reply
index as the event family of the existing trace institution. -/
def PrimitiveSignature.traceSignature {F : Type} (signature : PrimitiveSignature F) : TraceSignature :=
  ⟨⟨Event signature.Request signature.Reply⟩⟩

/-- The model admits every actual typed reply in its single initial state. -/
def PrimitiveSignature.traceModel {F : Type} (signature : PrimitiveSignature F) :
    Silmaril.Logic.ITree.Model.{0, 0} signature.traceSignature.toSignature where
  State := Unit
  initial _ := True
  step _ _ _ _ := True

/-- Every completed exchange must pass the shared stateless predicate.
Pending requests remain visible even when every reply is denied. -/
def PrimitiveSignature.traceModelUnder {F : Type} (signature : PrimitiveSignature F)
    (admits : ∀ key, signature.Reply key → Bool) :
    Silmaril.Logic.ITree.Model.{0, 0} signature.traceSignature.toSignature where
  State := Unit
  initial _ := True
  step := replyHandler admits

/-- A shared handler with a Boolean initial-state predicate and one
optional successor for each key and typed reply at the current state. -/
def PrimitiveSignature.traceModelWithHandler {F H : Type} (signature : PrimitiveSignature F)
    (advance : H → ∀ key, signature.Reply key → Option H) (initial : H → Bool) :
    Silmaril.Logic.ITree.Model.{0, 0} signature.traceSignature.toSignature where
  State := H
  initial h := initial h = true
  step := statefulReplyHandler advance

namespace Program

variable {F : Type} {signature : PrimitiveSignature F} {a b : Nat}
  {inputs : Fin a → PacketType} {outputs : Fin b → PacketType}
  {left right : Program signature inputs outputs} {input : Fin a}

/-- Run the existing product pruner with only admitted reply successors. -/
def refinementAtUnder? [DecidableEq F] (admits : ∀ key, signature.Reply key → Bool)
    (left right : Program signature inputs outputs) (input : Fin a) (packet : Denote (inputs input)) : Bool :=
  compareUnder admits left.states right.states left.step right.step
    (left.start input packet) (right.start input packet)

/-- Decide the same directed comparison at every public entry and typed packet. -/
def refinementUnder? [DecidableEq F] (admits : ∀ key, signature.Reply key → Bool)
    (left right : Program signature inputs outputs) : Bool :=
  decide (∀ input packet, left.refinementAtUnder? admits right input packet = true)

/-- Decide refinement at the selected packet and handler state. -/
def refinementAtWithHandler? [DecidableEq F] {H : Type} [DecidableEq H] [Fintype H]
    (advance : H → ∀ key, signature.Reply key → Option H)
    (left right : Program signature inputs outputs) (input : Fin a) (packet : Denote (inputs input))
    (h : H) : Bool :=
  compareWithHandler advance left.states right.states Finset.univ left.step right.step
    (left.start input packet) (right.start input packet) h

/-- Decide the sentence for the selected packet at all designated initial
handler states. An empty initial set satisfies the sentence vacuously. -/
def refinementWithHandler? [DecidableEq F] {H : Type} [DecidableEq H] [Fintype H]
    (advance : H → ∀ key, signature.Reply key → Option H) (initial : H → Bool)
    (left right : Program signature inputs outputs) (input : Fin a) (packet : Denote (inputs input)) : Bool :=
  decide (∀ h, initial h = true → left.refinementAtWithHandler? advance right input packet h = true)

/-- An ordinary trace-predicate sentence over the actual packed trees.
It requires every admitted source trace to occur in the target tree. -/
noncomputable def PackedEntry.refinementSentence
    {c : Nat} {rightInputs : Fin c → PacketType} {right : Program signature rightInputs outputs}
    {rightInput : Fin c} (leftEntry : PackedEntry left input) (rightEntry : PackedEntry right rightInput)
    (direction : MismatchDirection)
    (leftAmbient rightAmbient leftRecord rightRecord : Semantics.Env Atom) :
    TraceInstitution.Sentence.{0, 1} signature.traceSignature :=
  let l := leftEntry.observe leftAmbient leftRecord
  let r := rightEntry.observe rightAmbient rightRecord
  match direction with
  | .leftToRight => ⟨_, l, HasTrace r⟩
  | .rightToLeft => ⟨_, r, HasTrace l⟩

end Program

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible

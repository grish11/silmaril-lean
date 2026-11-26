module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Defs
public import Silmaril.Logic.ITree.Institution.Trace.Defs

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible

open Silmaril.Elgot.ITree (TraceSignature HasTrace)
open Silmaril.Elgot.ITree.Finite (Event)
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

namespace Program

variable {F : Type} {signature : PrimitiveSignature F} {a b : Nat}
  {inputs : Fin a → PacketType} {outputs : Fin b → PacketType}
  {left right : Program signature inputs outputs} {input : Fin a}

/-- An ordinary trace-predicate sentence over the actual packed trees.
It requires every admitted source trace to occur in the target tree. -/
noncomputable def PackedEntry.refinementSentence
    (leftEntry : PackedEntry left input) (rightEntry : PackedEntry right input)
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

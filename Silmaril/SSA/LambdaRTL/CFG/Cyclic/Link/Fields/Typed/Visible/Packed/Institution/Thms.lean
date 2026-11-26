module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Thms
public import Silmaril.Logic.ITree.Institution.Trace.Thms
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Program

open Silmaril.Elgot.ITree (TraceLE)
open Silmaril.Logic.ITree
open Silmaril.Isotope.LambdaSSA

variable {F : Type} {signature : PrimitiveSignature F} {a b : Nat}
  {inputs : Fin a → PacketType} {outputs : Fin b → PacketType}
  {left right : Program signature inputs outputs} {input : Fin a}

/-- In the model admitting every typed reply, satisfaction of this sentence
is exactly inclusion of the directed packed weak traces. -/
theorem PackedEntry.sat_refinementSentence_iff
    (leftEntry : PackedEntry left input) (rightEntry : PackedEntry right input)
    (direction : MismatchDirection) (leftAmbient rightAmbient leftRecord rightRecord : Semantics.Env Atom) :
    TraceInstitution.institution.{0, 1, 0}.Sat signature.traceSignature ⟨signature.traceModel⟩
      (leftEntry.refinementSentence rightEntry direction leftAmbient rightAmbient leftRecord rightRecord) ↔
    let l := leftEntry.observe leftAmbient leftRecord
    let r := rightEntry.observe rightAmbient rightRecord
    match direction with
    | .leftToRight => TraceLE l r
    | .rightToLeft => TraceLE r l :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution.sat_refinementSentence_iff
    leftEntry rightEntry direction leftAmbient rightAmbient leftRecord rightRecord

/-- A mismatch refutes the directed sentence at its packet in the existing
trace institution, with the same ordered packed exits and typed replies. -/
theorem explainMismatch?_refutes_traceSat [DecidableEq F]
    {w : Mismatch signature inputs} (found : left.explainMismatch? right = some w)
    (leftEntry : PackedEntry left w.packet.1) (rightEntry : PackedEntry right w.packet.1)
    (leftAmbient rightAmbient leftRecord rightRecord : Semantics.Env Atom)
    (leftAgrees : leftEntry.recordAgrees w.packet.2 leftRecord)
    (rightAgrees : rightEntry.recordAgrees w.packet.2 rightRecord) :
    ¬ TraceInstitution.institution.{0, 1, 0}.Sat signature.traceSignature ⟨signature.traceModel⟩
      (leftEntry.refinementSentence rightEntry w.direction leftAmbient rightAmbient leftRecord rightRecord) := by
  have witness := left.explainMismatch?_sound_packed found leftEntry rightEntry
    leftAmbient rightAmbient leftRecord rightRecord leftAgrees rightAgrees
  rw [leftEntry.sat_refinementSentence_iff]
  cases direction : w.direction <;>
    simp only [direction, MismatchDirection.distinguishes] at witness <;>
    exact fun included => witness.2 (included _ witness.1)

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Program

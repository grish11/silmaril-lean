module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Thms
public import Silmaril.Logic.ITree.Institution.Trace.Thms
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible

open Silmaril.Elgot.ITree (Tree Trace HandledTrace HasTrace TraceLE)
open Silmaril.Elgot.ITree.Finite (Event)
open Silmaril.Logic.ITree
open Silmaril.Isotope.LambdaSSA

/-- The single-state model preserves precisely the ordinary weak finite
traces. These include prefixes, pending requests and ordered returns. After
a completed exchange, the observation may end in a prefix. A silently
diverging tree has only the empty prefix as an observation. -/
theorem PrimitiveSignature.handledTrace_iff {F : Type} (signature : PrimitiveSignature F) {R : Type 1}
    (tree : Tree (Event signature.Request signature.Reply) R)
    (trace : Trace (Event signature.Request signature.Reply) R) :
    HandledTrace signature.traceModel.step () tree trace ↔ HasTrace tree trace :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution.handledTrace_iff tree trace

namespace Program

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

/-- The one-way finite simulation decides the institutional sentence at a
chosen packet, using the actual ordered packed exit tags on both sides. -/
theorem refinementAt?_iff_traceSat [DecidableEq F] (packet : Denote (inputs input))
    (leftEntry : PackedEntry left input) (rightEntry : PackedEntry right input)
    (leftAmbient rightAmbient leftRecord rightRecord : Semantics.Env Atom)
    (leftAgrees : leftEntry.recordAgrees packet leftRecord)
    (rightAgrees : rightEntry.recordAgrees packet rightRecord) :
    left.refinementAt? right input packet = true ↔
      TraceInstitution.institution.{0, 1, 0}.Sat signature.traceSignature ⟨signature.traceModel⟩
        (leftEntry.refinementSentence rightEntry .leftToRight leftAmbient rightAmbient leftRecord rightRecord) := by
  simpa only [leftEntry.sat_refinementSentence_iff, leftEntry.observe_eq _ _ _ leftAgrees,
    rightEntry.observe_eq _ _ _ rightAgrees] using left.refinementAt?_iff_packedOutput right input packet

/-- The same decision over every public entry and exact packet, with checked
packed entries and matching capture records supplied on both sides. -/
theorem refinement?_iff_traceSat [DecidableEq F]
    (leftEntry : ∀ input, PackedEntry left input) (rightEntry : ∀ input, PackedEntry right input)
    (leftAmbient rightAmbient : Semantics.Env Atom)
    (leftRecord rightRecord : ∀ input, Denote (inputs input) → Semantics.Env Atom)
    (leftAgrees : ∀ input packet, (leftEntry input).recordAgrees packet (leftRecord input packet))
    (rightAgrees : ∀ input packet, (rightEntry input).recordAgrees packet (rightRecord input packet)) :
    left.refinement? right = true ↔ ∀ input packet,
      TraceInstitution.institution.{0, 1, 0}.Sat signature.traceSignature ⟨signature.traceModel⟩
        ((leftEntry input).refinementSentence (rightEntry input) .leftToRight leftAmbient rightAmbient
          (leftRecord input packet) (rightRecord input packet)) := by
  rw [Program.refinement?, decide_eq_true_eq]
  exact forall_congr' fun input => forall_congr' fun packet => refinementAt?_iff_traceSat packet
    (leftEntry input) (rightEntry input) _ _ _ _ (leftAgrees input packet) (rightAgrees input packet)

/-- Decide the actual packed sentence under a shared stateless typed reply
predicate. Packing retains the ordered exit tag and the original replay path. -/
theorem refinementAtUnder?_iff_traceSat [DecidableEq F] (admits : ∀ key, signature.Reply key → Bool)
    (packet : Denote (inputs input)) (leftEntry : PackedEntry left input) (rightEntry : PackedEntry right input)
    (leftAmbient rightAmbient leftRecord rightRecord : Semantics.Env Atom)
    (leftAgrees : leftEntry.recordAgrees packet leftRecord)
    (rightAgrees : rightEntry.recordAgrees packet rightRecord) :
    left.refinementAtUnder? admits right input packet = true ↔
      TraceInstitution.institution.{0, 1, 0}.Sat signature.traceSignature ⟨signature.traceModelUnder admits⟩
        (leftEntry.refinementSentence rightEntry .leftToRight leftAmbient rightAmbient leftRecord rightRecord) :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution.refinementAtUnder_traceSat
    admits packet leftEntry rightEntry leftAmbient rightAmbient leftRecord rightRecord leftAgrees rightAgrees

theorem refinementUnder?_iff_traceSat [DecidableEq F] (admits : ∀ key, signature.Reply key → Bool)
    (leftEntry : ∀ input, PackedEntry left input) (rightEntry : ∀ input, PackedEntry right input)
    (leftAmbient rightAmbient : Semantics.Env Atom)
    (leftRecord rightRecord : ∀ input, Denote (inputs input) → Semantics.Env Atom)
    (leftAgrees : ∀ input packet, (leftEntry input).recordAgrees packet (leftRecord input packet))
    (rightAgrees : ∀ input packet, (rightEntry input).recordAgrees packet (rightRecord input packet)) :
    left.refinementUnder? admits right = true ↔ ∀ input packet,
      TraceInstitution.institution.{0, 1, 0}.Sat signature.traceSignature ⟨signature.traceModelUnder admits⟩
        ((leftEntry input).refinementSentence (rightEntry input) .leftToRight leftAmbient rightAmbient
          (leftRecord input packet) (rightRecord input packet)) := by
  rw [Program.refinementUnder?, decide_eq_true_eq]
  exact forall_congr' fun input => forall_congr' fun packet => refinementAtUnder?_iff_traceSat admits packet
    (leftEntry input) (rightEntry input) _ _ _ _ (leftAgrees input packet) (rightAgrees input packet)

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

end Program

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible

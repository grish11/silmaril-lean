module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution.Thms
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution.Conservativity

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Program

open Silmaril.Logic.ITree
open Silmaril.Isotope.LambdaSSA

variable {F : Type} {signature : PrimitiveSignature F} {a b : Nat}
  {inputs : Fin a → PacketType} {outputs : Fin b → PacketType}
  {left right : Program signature inputs outputs} {input : Fin a}

/-- The unrestricted model detects exactly validity of an ordered packed
refinement sentence over shared handlers for its fixed event signature.
Each handler uses its own initial predicate for both trees. -/
theorem PackedEntry.sat_refinementSentence_all_iff
    (leftEntry : PackedEntry left input) (rightEntry : PackedEntry right input)
    (direction : MismatchDirection) (leftAmbient rightAmbient leftRecord rightRecord : Semantics.Env Atom) :
    let sentence := leftEntry.refinementSentence rightEntry direction leftAmbient rightAmbient leftRecord rightRecord
    TraceInstitution.Sat signature.traceModel sentence ↔
      ∀ policy : Silmaril.Logic.ITree.Model.{0, 0} signature.traceSignature.toSignature,
        TraceInstitution.Sat policy sentence :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution.sat_all_iff
    leftEntry rightEntry direction leftAmbient rightAmbient leftRecord rightRecord

/-- The two directed sentences are valid in every shared model exactly when
the packed weak trees agree. Each visible head is deterministic, its pending
request exposes the full typed key even with no replies, and each exact typed
reply selects one continuation. Silent divergence has only the empty prefix
at that point. Mutual inclusion therefore also distinguishes a silent
endpoint from a pending request or return. -/
theorem PackedEntry.observe_eq_iff_mutual_valid
    (leftEntry : PackedEntry left input) (rightEntry : PackedEntry right input)
    (leftAmbient rightAmbient leftRecord rightRecord : Semantics.Env Atom) :
    leftEntry.observe leftAmbient leftRecord = rightEntry.observe rightAmbient rightRecord ↔
      ∀ policy : Silmaril.Logic.ITree.Model.{0, 0} signature.traceSignature.toSignature,
        TraceInstitution.Sat policy
          (leftEntry.refinementSentence rightEntry .leftToRight leftAmbient rightAmbient leftRecord rightRecord) ∧
        TraceInstitution.Sat policy
          (leftEntry.refinementSentence rightEntry .rightToLeft leftAmbient rightAmbient leftRecord rightRecord) :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution.observe_eq_iff_mutual_valid
    leftEntry rightEntry leftAmbient rightAmbient leftRecord rightRecord

/-- The existing weak-equality checker decides mutual validity at every public
entry and exact typed packet. Both directions use the same checked packed
entries, matching capture records, and ordered exit observations. -/
theorem weakEq?_iff_mutual_valid_traceSat [DecidableEq F] (left right : Program signature inputs outputs)
    (leftEntry : ∀ input, PackedEntry left input) (rightEntry : ∀ input, PackedEntry right input)
    (leftAmbient rightAmbient : Semantics.Env Atom)
    (leftRecord rightRecord : ∀ input, Denote (inputs input) → Semantics.Env Atom)
    (leftAgrees : ∀ input packet, (leftEntry input).recordAgrees packet (leftRecord input packet))
    (rightAgrees : ∀ input packet, (rightEntry input).recordAgrees packet (rightRecord input packet)) :
    left.weakEq? right = true ↔
      ∀ input packet (policy : Silmaril.Logic.ITree.Model.{0, 0} signature.traceSignature.toSignature),
        TraceInstitution.Sat policy ((leftEntry input).refinementSentence (rightEntry input) .leftToRight
          leftAmbient rightAmbient (leftRecord input packet) (rightRecord input packet)) ∧
        TraceInstitution.Sat policy ((leftEntry input).refinementSentence (rightEntry input) .rightToLeft
          leftAmbient rightAmbient (leftRecord input packet) (rightRecord input packet)) :=
  (left.weakEq?_iff_packed right leftEntry rightEntry leftAmbient rightAmbient
    leftRecord rightRecord leftAgrees rightAgrees).trans <| forall_congr' fun input => forall_congr' fun packet =>
      (leftEntry input).observe_eq_iff_mutual_valid (rightEntry input) leftAmbient rightAmbient
        (leftRecord input packet) (rightRecord input packet)

/-- At matching captures, one all-replies comparison decides validity
over every shared handled-trace model of the fixed event signature. -/
theorem refinementAt?_iff_valid_traceSat [DecidableEq F] (packet : Denote (inputs input))
    (leftEntry : PackedEntry left input) (rightEntry : PackedEntry right input)
    (leftAmbient rightAmbient leftRecord rightRecord : Semantics.Env Atom)
    (leftAgrees : leftEntry.recordAgrees packet leftRecord) (rightAgrees : rightEntry.recordAgrees packet rightRecord) :
    left.refinementAt? right input packet = true ↔
      ∀ policy : Silmaril.Logic.ITree.Model.{0, 0} signature.traceSignature.toSignature,
        TraceInstitution.Sat policy
          (leftEntry.refinementSentence rightEntry .leftToRight leftAmbient rightAmbient leftRecord rightRecord) :=
  (refinementAt?_iff_traceSat packet leftEntry rightEntry leftAmbient rightAmbient leftRecord rightRecord
    leftAgrees rightAgrees).trans
      (leftEntry.sat_refinementSentence_all_iff rightEntry .leftToRight leftAmbient rightAmbient leftRecord rightRecord)

/-- The all-replies decision agrees with requiring acceptance by every
deterministic finite-state checker at the same packet and captures. Each
policy is checked over every state selected by its initial predicate. -/
theorem refinementAt?_iff_allFiniteHandlers [DecidableEq F] (packet : Denote (inputs input))
    (leftEntry : PackedEntry left input) (rightEntry : PackedEntry right input)
    (leftAmbient rightAmbient leftRecord rightRecord : Semantics.Env Atom)
    (leftAgrees : leftEntry.recordAgrees packet leftRecord) (rightAgrees : rightEntry.recordAgrees packet rightRecord) :
    left.refinementAt? right input packet = true ↔
      ∀ (H : Type) [DecidableEq H] [Fintype H] (advance : H → ∀ key, signature.Reply key → Option H)
        (initial : H → Bool), left.refinementWithHandler? advance initial right input packet = true :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution.all_finite_checkers_iff
    packet leftEntry rightEntry leftAmbient rightAmbient leftRecord rightRecord leftAgrees rightAgrees

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Program

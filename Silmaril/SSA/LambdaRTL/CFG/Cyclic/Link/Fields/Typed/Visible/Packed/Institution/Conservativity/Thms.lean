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

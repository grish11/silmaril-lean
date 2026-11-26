module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.Recognize.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.Recognize

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.Recognize

open Silmaril.SSA.LambdaRTL (CFG)
open LambdaSSA.Semantics.Interaction (Primitive)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration

attribute [local instance] requestTypes

variable {κ V K α : Type 1} [DecidableEq V] [DecidableEq K]
  {P : FlatInstitution.Signature.{0, 0} κ} {E : Type → Type}
  {seed : V} {names : Fin 5 ≃ K} {source : CFG V K P.Instr}
  {a : Admission P (interface seed names) (fun _ => []) source} {opcode : P.Instr}

/-- Exact readback suffices for the existing guarded correspondence. The
only semantic inputs are agreement of the typed query evaluator and the
version-zero entry value. All row equalities follow from the readback. -/
def Checked.corresponds (checked : Checked a opcode) (atom : Unit → α)
    (query : Query (signature P.Instr) E) (instr : Primitive E P.Instr α)
    (input : V × Nat → Value α) (agrees : QueryAgreement opcode atom query instr)
    (caller : Syntax.Payload Bit) (seedValue : input (seed, 0) = encodeValue atom caller.val) :
    Corresponds a (guardedTable opcode checked.routes) caller query instr input :=
  ⟨encodeCursor names atom,
    Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.Recognize.entry
      checked atom instr input caller seedValue,
    Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.Recognize.localStep
      checked atom query instr input agrees caller⟩

/-- Extract the reply routes from the admission's scoped code and return the
correspondence for the resulting guarded table after checking exact readback. -/
@[expose] def recognizeAdapter [DecidableEq P.Instr] (a : Admission P (interface seed names) (fun _ => []) source)
    (opcode : P.Instr) (atom : Unit → α) (query : Query (signature P.Instr) E)
    (instr : Primitive E P.Instr α) (input : V × Nat → Value α)
    (agrees : QueryAgreement opcode atom query instr) (caller : Syntax.Payload Bit)
    (seedValue : input (seed, 0) = encodeValue atom caller.val) :
    Option (Σ routes : Routes, Corresponds a (guardedTable opcode routes) caller query instr input) :=
  (recognize a opcode).map fun checked =>
    ⟨checked.routes, checked.corresponds atom query instr input agrees caller seedValue⟩

end Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.Recognize

module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.Recognize.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.Recognize

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.Recognize

open Silmaril.SSA.LambdaRTL (CFG)
open Silmaril.Elgot (mapReturn liftPure)
open LambdaSSA (FiniteCFG)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (Primitive region)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open LambdaSSA.UB.Overlay.Shape
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration

attribute [local instance] requestTypes

variable {κ V K α : Type 1} [DecidableEq V] [DecidableEq K]
  {P : FlatInstitution.Signature.{0, 0} κ} {E : Type → Type}
  {seed : V} {names : Fin 5 ≃ K} {source : CFG V K P.Instr}
  {fields : K → List (V × Ty κ)} {a : Admission P (interface seed names) fields source}
  {opcode : P.Instr} {profile : LiveProfile P.Instr}

/-- Exact readback gives the guarded correspondence with the supplied
version-zero bit, agreement on typed requests, and pure agreement for
the checked terminal assignments. -/
def Checked.correspondsWith (checked : Checked a opcode (liveOpcodes profile)) (atom : Unit → α)
    (query : Query (signature P.Instr) E) (instr : Primitive E P.Instr α)
    (input : V × Nat → Value α) (agrees : QueryAgreement opcode atom query instr)
    (liveAgrees : LiveAgreement profile instr)
    (caller : Syntax.Payload Bit) (seedValue : input (seed, 0) = encodeValue atom caller.val) :
    Corresponds a (guardedTable opcode checked.routes) caller query instr input (exitResult (liveValues profile)) :=
  ⟨encodeCursorWith (liveValues profile) names atom,
    Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.Recognize.entry
      checked atom instr input caller seedValue,
    Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.Recognize.localStep
      checked atom query instr input agrees liveAgrees caller⟩

/-- The ordinary adapter has no terminal constructor assignments. -/
def Checked.corresponds (checked : Checked a opcode) (atom : Unit → α)
    (query : Query (signature P.Instr) E) (instr : Primitive E P.Instr α)
    (input : V × Nat → Value α) (agrees : QueryAgreement opcode atom query instr)
    (caller : Syntax.Payload Bit) (seedValue : input (seed, 0) = encodeValue atom caller.val) :
    Corresponds a (guardedTable opcode checked.routes) caller query instr input :=
  checked.correspondsWith (profile := fun _ => none) atom query instr input agrees
    (fun _ _ _ h => nomatch h) caller seedValue

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

/-- The recognized request row forwards the whole typed reply payload to its
written destination. The result is independent of the ambient environment. -/
theorem eval_request (atom : Unit → α) (query : Query (signature P.Instr) E)
    (instr : Primitive E P.Instr α) (destination : Fin 3 → Fin 3)
    (agrees : QueryAgreement opcode atom query instr) (env : Env α) (packet : Syntax.Payload Bit) :
    region instr (extend env (.pair (encodeValue atom packet.val) .unit))
      (requestRow opcode destination).erase =
      (query opcode packet >>= fun r => pure ((destination r.down.1).val,
        .pair (encodeValue atom r.down.2.val) .unit)) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.Recognize.eval_request
    atom query instr destination agrees env packet

variable {code : FiniteCFG P.Instr 3 2 1}

/-- Recover the named entry transfer from evaluation of its exact numbered readback. -/
theorem Readback.entry_eval (readback : Readback a code) (instr : Primitive E P.Instr α)
    (input : V × Nat → Value α) (env : Env α)
    (agrees : ∀ i, env i.val = input ((interface (κ := κ) seed names).version.names i)) :
    a.versioned.source.entry.evalJump (treeModel instr) input =
      (region instr env code.entry.erase >>= fun p => pure (restore names p)) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.Recognize.entry_eval
    instr input readback env agrees

/-- Recover a packet-local named step from its exact numbered row. -/
theorem Readback.block_eval (readback : Readback a code) (instr : Primitive E P.Instr α)
    (input : V × Nat → Value α) (env : Env α) (p : Value α) (i : Fin 3) :
    CFG.Cyclic.stepSSA (treeModel instr) a.versioned.source.blocks input (names (i.castAdd 2), p) =
      (region instr (extend env p) (code.block i).erase >>= fun q => pure (.inr (restore names q))) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.Recognize.block_eval
    instr input readback env p i

/-- A checked public exit returns its payload at the original ordered tag. -/
theorem Readback.exit_eval (readback : Readback a code) (instr : Primitive E P.Instr α)
    (input : V × Nat → Value α) (p : Value α) (i : TwoRequest.Tag) :
    mapReturn (CFG.Cyclic.stepSSA (treeModel instr) a.versioned.source.blocks input)
      (liftPure fun t => FiniteCFG.packedTreeOutput (treeExitNumber (interface (κ := κ) seed names).exits t)) (names (i.natAdd 3), p) =
      pure (.inl (FiniteCFG.packedTreeOutput (i.val, p))) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.Recognize.exit_eval
    instr input readback p i

end Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.Recognize

module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution.Lift.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution.Reindex.Thms
public import Silmaril.Logic.ITree.Institution.Trace.Category.Thms
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution.Lift

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible

open CategoryTheory
open Silmaril.Elgot.ITree (TraceSignature HasTrace)
open Silmaril.Elgot.ITree.Finite (Event)
open Silmaril.Logic.ITree
open Silmaril.Isotope.LambdaSSA

theorem PrimitiveSignature.replyImageMask_iff {F : Type} (signature : PrimitiveSignature F)
    {target : Silmaril.Elgot.ITree.Signature.{0}} (f : signature.traceSignature.toSignature ⟶ target)
    [∀ key : signature.Request, Fintype (f.request ⟨_, Event.ask key⟩).1]
    (key : signature.Request) (reply : signature.Reply key) :
    signature.replyImageMask f key reply = true ↔ signature.ReplyRealizable f key reply := by
  simp [PrimitiveSignature.replyImageMask, PrimitiveSignature.ReplyRealizable]

namespace Program

variable {F : Type} {signature : PrimitiveSignature F} {a b : Nat}
  {inputs : Fin a → PacketType} {outputs : Fin b → PacketType}
  {left right : Program signature inputs outputs} {input : Fin a}
  {Target : Silmaril.Elgot.ITree.Signature.InjectiveRequests.{0}}

/-- The translated packed sentence compares the two actual mapped dispatchers. -/
theorem PackedEntry.refinementSentence_lifted
    (leftEntry : PackedEntry left input) (rightEntry : PackedEntry right input)
    (f : TraceSignature.includeInjectiveRequests.obj signature.traceSignature ⟶ Target)
    (direction : MismatchDirection) (leftAmbient rightAmbient leftRecord rightRecord : Semantics.Env Atom) :
    TraceInstitution.liftInstitution.{0,1,0}.Sen.map f
      (leftEntry.refinementSentence rightEntry direction leftAmbient rightAmbient leftRecord rightRecord) =
    let l := leftEntry.observeMapped f.hom leftAmbient leftRecord
    let r := rightEntry.observeMapped f.hom rightAmbient rightRecord
    match direction with
    | .leftToRight => ⟨_, l, HasTrace r⟩
    | .rightToLeft => ⟨_, r, HasTrace l⟩ :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution.refinementSentence_lifted
    leftEntry rightEntry f direction leftAmbient rightAmbient leftRecord rightRecord

/-- With an exact reply-image mask, the existing filtered verdict decides
validity in the wider institution at this checked packet. Pending requests
remain observable even when none of their replies have a preimage. -/
theorem refinementAtUnder?_iff_valid_liftSat [DecidableEq F]
    (f : TraceSignature.includeInjectiveRequests.obj signature.traceSignature ⟶ Target)
    (admits : ∀ key, signature.Reply key → Bool)
    (exactMask : ∀ key reply, admits key reply = true ↔ signature.ReplyRealizable f.hom key reply)
    (packet : Denote (inputs input)) (leftEntry : PackedEntry left input) (rightEntry : PackedEntry right input)
    (leftAmbient rightAmbient leftRecord rightRecord : Semantics.Env Atom)
    (leftAgrees : leftEntry.recordAgrees packet leftRecord) (rightAgrees : rightEntry.recordAgrees packet rightRecord) :
    left.refinementAtUnder? admits right input packet = true ↔
      ∀ policy : TraceInstitution.liftInstitution.{0,1,0}.Mod.obj (Opposite.op Target),
        TraceInstitution.liftInstitution.{0,1,0}.Sat Target policy
          (TraceInstitution.liftInstitution.{0,1,0}.Sen.map f
            (leftEntry.refinementSentence rightEntry .leftToRight leftAmbient rightAmbient leftRecord rightRecord)) :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution.refinementAtUnder_valid_liftSat
    f admits exactMask packet leftEntry rightEntry leftAmbient rightAmbient leftRecord rightRecord leftAgrees rightAgrees

/-- A surjective backward reply map preserves the existing all-replies
verdict, even when multiple target replies project to one source reply. -/
theorem refinementAt?_iff_valid_liftSat [DecidableEq F]
    (f : TraceSignature.includeInjectiveRequests.obj signature.traceSignature ⟶ Target)
    (onto : ∀ q, Function.Surjective (f.hom.reply q))
    (packet : Denote (inputs input)) (leftEntry : PackedEntry left input) (rightEntry : PackedEntry right input)
    (leftAmbient rightAmbient leftRecord rightRecord : Semantics.Env Atom)
    (leftAgrees : leftEntry.recordAgrees packet leftRecord) (rightAgrees : rightEntry.recordAgrees packet rightRecord) :
    left.refinementAt? right input packet = true ↔
      ∀ policy : TraceInstitution.liftInstitution.{0,1,0}.Mod.obj (Opposite.op Target),
        TraceInstitution.liftInstitution.{0,1,0}.Sat Target policy
          (TraceInstitution.liftInstitution.{0,1,0}.Sen.map f
            (leftEntry.refinementSentence rightEntry .leftToRight leftAmbient rightAmbient leftRecord rightRecord)) :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution.refinementAt_valid_liftSat
    f onto packet leftEntry rightEntry leftAmbient rightAmbient leftRecord rightRecord leftAgrees rightAgrees

theorem refinementUnder?_iff_valid_liftSat [DecidableEq F]
    (f : TraceSignature.includeInjectiveRequests.obj signature.traceSignature ⟶ Target)
    (admits : ∀ key, signature.Reply key → Bool)
    (exactMask : ∀ key reply, admits key reply = true ↔ signature.ReplyRealizable f.hom key reply)
    (leftEntry : ∀ input, PackedEntry left input) (rightEntry : ∀ input, PackedEntry right input)
    (leftAmbient rightAmbient : Semantics.Env Atom)
    (leftRecord rightRecord : ∀ input, Denote (inputs input) → Semantics.Env Atom)
    (leftAgrees : ∀ input packet, (leftEntry input).recordAgrees packet (leftRecord input packet))
    (rightAgrees : ∀ input packet, (rightEntry input).recordAgrees packet (rightRecord input packet)) :
    left.refinementUnder? admits right = true ↔
      ∀ input packet (policy : TraceInstitution.liftInstitution.{0,1,0}.Mod.obj (Opposite.op Target)),
        TraceInstitution.liftInstitution.{0,1,0}.Sat Target policy
          (TraceInstitution.liftInstitution.{0,1,0}.Sen.map f
            ((leftEntry input).refinementSentence (rightEntry input) .leftToRight leftAmbient rightAmbient
              (leftRecord input packet) (rightRecord input packet))) := by
  rw [Program.refinementUnder?, decide_eq_true_eq]
  exact forall_congr' fun input => forall_congr' fun packet => refinementAtUnder?_iff_valid_liftSat f admits exactMask
    packet (leftEntry input) (rightEntry input) _ _ _ _ (leftAgrees input packet) (rightAgrees input packet)

theorem refinement?_iff_valid_liftSat [DecidableEq F]
    (f : TraceSignature.includeInjectiveRequests.obj signature.traceSignature ⟶ Target)
    (onto : ∀ q, Function.Surjective (f.hom.reply q))
    (leftEntry : ∀ input, PackedEntry left input) (rightEntry : ∀ input, PackedEntry right input)
    (leftAmbient rightAmbient : Semantics.Env Atom)
    (leftRecord rightRecord : ∀ input, Denote (inputs input) → Semantics.Env Atom)
    (leftAgrees : ∀ input packet, (leftEntry input).recordAgrees packet (leftRecord input packet))
    (rightAgrees : ∀ input packet, (rightEntry input).recordAgrees packet (rightRecord input packet)) :
    left.refinement? right = true ↔
      ∀ input packet (policy : TraceInstitution.liftInstitution.{0,1,0}.Mod.obj (Opposite.op Target)),
        TraceInstitution.liftInstitution.{0,1,0}.Sat Target policy
          (TraceInstitution.liftInstitution.{0,1,0}.Sen.map f
            ((leftEntry input).refinementSentence (rightEntry input) .leftToRight leftAmbient rightAmbient
              (leftRecord input packet) (rightRecord input packet))) := by
  rw [Program.refinement?, decide_eq_true_eq]
  exact forall_congr' fun input => forall_congr' fun packet => refinementAt?_iff_valid_liftSat f onto
    packet (leftEntry input) (rightEntry input) _ _ _ _ (leftAgrees input packet) (rightAgrees input packet)

end Program
end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible

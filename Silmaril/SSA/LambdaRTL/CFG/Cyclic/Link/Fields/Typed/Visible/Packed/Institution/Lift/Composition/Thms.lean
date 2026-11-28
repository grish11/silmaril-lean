module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution.Lift.Thms
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution.Lift

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible

open CategoryTheory
open Silmaril.Elgot.ITree (TraceSignature)
open Silmaril.Elgot.ITree.Finite (Event)
open Silmaril.Logic.ITree
open Silmaril.Isotope.LambdaSSA

variable {F : Type} {signature : PrimitiveSignature F}

/-- Projecting the exact second-stage filter keeps precisely the source
replies that have a preimage under the composite. -/
theorem PrimitiveSignature.projectReplyMask_exact
    {Mid Target : Silmaril.Elgot.ITree.Signature.{0}}
    (f : signature.traceSignature.toSignature ⟶ Mid) (g : Mid ⟶ Target)
    [∀ key : signature.Request, Fintype (f.request ⟨_, Event.ask key⟩).1]
    (admits : ∀ key : signature.Request, (f.request ⟨_, Event.ask key⟩).1 → Bool)
    (exactSecond : ∀ key r, admits key r = true ↔
      ∃ targetReply, g.reply (f.request ⟨_, Event.ask key⟩) targetReply = r)
    (key : signature.Request) (reply : signature.Reply key) :
    signature.projectReplyMask f admits key reply = true ↔ signature.ReplyRealizable (f ≫ g) key reply :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution.projectReplyMask_exact
    f g admits exactSecond key reply

/-- Both executable masks give the same Boolean at every source reply.
Substitution gives equality of the pointwise and whole-interface verdicts. -/
theorem PrimitiveSignature.projectReplyMask_eq_comp
    {Mid Target : Silmaril.Elgot.ITree.Signature.{0}}
    (f : signature.traceSignature.toSignature ⟶ Mid) (g : Mid ⟶ Target)
    [∀ key : signature.Request, Fintype (f.request ⟨_, Event.ask key⟩).1]
    [∀ key : signature.Request, Fintype ((f ≫ g).request ⟨_, Event.ask key⟩).1]
    (admits : ∀ key : signature.Request, (f.request ⟨_, Event.ask key⟩).1 → Bool)
    (exactSecond : ∀ key r, admits key r = true ↔
      ∃ targetReply, g.reply (f.request ⟨_, Event.ask key⟩) targetReply = r) :
    signature.projectReplyMask f admits = signature.replyImageMask (f ≫ g) :=
  funext fun key => funext fun reply => Bool.eq_iff_iff.mpr <|
    (PrimitiveSignature.projectReplyMask_exact f g admits exactSecond key reply).trans
      (signature.replyImageMask_iff (f ≫ g) key reply).symm

namespace Program

variable {a b : Nat} {inputs : Fin a → PacketType} {outputs : Fin b → PacketType}
  {left right : Program signature inputs outputs} {input : Fin a}
  {Mid Target : Silmaril.Elgot.ITree.Signature.InjectiveRequests.{0}}

/-- The staged executable comparison decides satisfaction of the lifted
packed pair under the intermediate reduct of the final all-replies model. -/
theorem refinementAtUnder?_iff_staged_liftSat [DecidableEq F]
    (f : TraceSignature.includeInjectiveRequests.obj signature.traceSignature ⟶ Mid) (g : Mid ⟶ Target)
    [finiteMid : ∀ key : signature.Request, Fintype (f.hom.request ⟨_, Event.ask key⟩).1]
    (admits : ∀ key : signature.Request, (f.hom.request ⟨_, Event.ask key⟩).1 → Bool)
    (exactSecond : ∀ key r, admits key r = true ↔
      ∃ targetReply, g.hom.reply (f.hom.request ⟨_, Event.ask key⟩) targetReply = r)
    (packet : Denote (inputs input)) (leftEntry : PackedEntry left input) (rightEntry : PackedEntry right input)
    (leftAmbient rightAmbient leftRecord rightRecord : Semantics.Env Atom)
    (leftAgrees : leftEntry.recordAgrees packet leftRecord) (rightAgrees : rightEntry.recordAgrees packet rightRecord) :
    left.refinementAtUnder? (signature.projectReplyMask f.hom (finite := finiteMid) admits) right input packet = true ↔
      TraceInstitution.liftInstitution.{0,1,0}.Sat Mid
        ⟨(TraceInstitution.allRepliesModel ⟨Target.obj⟩).reduct g.hom⟩
        (TraceInstitution.liftInstitution.{0,1,0}.Sen.map f
          (leftEntry.refinementSentence rightEntry .leftToRight leftAmbient rightAmbient leftRecord rightRecord)) :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution.refinementAtUnder_staged_liftSat
    f g (finiteMid := finiteMid) admits exactSecond packet leftEntry rightEntry leftAmbient rightAmbient leftRecord rightRecord leftAgrees rightAgrees

theorem refinementUnder?_iff_staged_liftSat [DecidableEq F]
    (f : TraceSignature.includeInjectiveRequests.obj signature.traceSignature ⟶ Mid) (g : Mid ⟶ Target)
    [finiteMid : ∀ key : signature.Request, Fintype (f.hom.request ⟨_, Event.ask key⟩).1]
    (admits : ∀ key : signature.Request, (f.hom.request ⟨_, Event.ask key⟩).1 → Bool)
    (exactSecond : ∀ key r, admits key r = true ↔
      ∃ targetReply, g.hom.reply (f.hom.request ⟨_, Event.ask key⟩) targetReply = r)
    (leftEntry : ∀ input, PackedEntry left input) (rightEntry : ∀ input, PackedEntry right input)
    (leftAmbient rightAmbient : Semantics.Env Atom)
    (leftRecord rightRecord : ∀ input, Denote (inputs input) → Semantics.Env Atom)
    (leftAgrees : ∀ input packet, (leftEntry input).recordAgrees packet (leftRecord input packet))
    (rightAgrees : ∀ input packet, (rightEntry input).recordAgrees packet (rightRecord input packet)) :
    left.refinementUnder? (signature.projectReplyMask f.hom (finite := finiteMid) admits) right = true ↔
      ∀ input packet, TraceInstitution.liftInstitution.{0,1,0}.Sat Mid
        ⟨(TraceInstitution.allRepliesModel ⟨Target.obj⟩).reduct g.hom⟩
        (TraceInstitution.liftInstitution.{0,1,0}.Sen.map f
          ((leftEntry input).refinementSentence (rightEntry input) .leftToRight leftAmbient rightAmbient
            (leftRecord input packet) (rightRecord input packet))) := by
  rw [Program.refinementUnder?, decide_eq_true_eq]
  exact forall_congr' fun input => forall_congr' fun packet => refinementAtUnder?_iff_staged_liftSat f g (finiteMid := finiteMid) admits
    exactSecond packet (leftEntry input) (rightEntry input) _ _ _ _ (leftAgrees input packet) (rightAgrees input packet)

end Program
end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible

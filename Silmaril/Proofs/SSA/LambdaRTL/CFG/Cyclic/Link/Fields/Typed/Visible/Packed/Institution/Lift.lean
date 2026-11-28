module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution.Lift.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution.Reindex.Thms
public import Silmaril.Logic.ITree.Institution.Trace.Category.Thms

public section

namespace Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution

open CategoryTheory Silmaril.Elgot.ITree
open Silmaril.Elgot.ITree.Finite (Event)
open Silmaril.Logic.ITree
open Silmaril.Isotope.LambdaSSA
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Program (PackedEntry MismatchDirection)

variable {F : Type} {signature : PrimitiveSignature F} {a b : Nat}
  {inputs : Fin a → PacketType} {outputs : Fin b → PacketType}
  {left right : Program signature inputs outputs} {input : Fin a} {Target : Silmaril.Elgot.ITree.Signature.InjectiveRequests.{0}}

theorem refinementSentence_lifted
    (leftEntry : PackedEntry left input) (rightEntry : PackedEntry right input)
    (f : TraceSignature.includeInjectiveRequests.obj signature.traceSignature ⟶ Target)
    (direction : MismatchDirection) (leftAmbient rightAmbient leftRecord rightRecord : Semantics.Env Atom) :
    TraceInstitution.liftInstitution.{0,1,0}.Sen.map f
      (leftEntry.refinementSentence rightEntry direction leftAmbient rightAmbient leftRecord rightRecord) =
    let l := leftEntry.observeMapped f.hom leftAmbient leftRecord
    let r := rightEntry.observeMapped f.hom rightAmbient rightRecord
    match direction with
    | .leftToRight => ⟨_, l, HasTrace r⟩
    | .rightToLeft => ⟨_, r, HasTrace l⟩ := by
  cases direction <;>
    dsimp only <;>
    erw [leftEntry.observe_mapped, rightEntry.observe_mapped] <;>
    exact TraceInstitution.translateLift_hasTrace (S := signature.traceSignature) (T := ⟨Target.obj⟩) f.hom _ _

private theorem reduct_allReplies_eq
    (f : signature.traceSignature.toSignature ⟶ Target.obj)
    (admits : ∀ key, signature.Reply key → Bool)
    (exactMask : ∀ key reply, admits key reply = true ↔ signature.ReplyRealizable f key reply) :
    (TraceInstitution.allRepliesModel ⟨Target.obj⟩).reduct f = signature.traceModelUnder admits := by
  apply congrArg (fun step => (⟨Unit, fun _ => True, step⟩ : Model signature.traceSignature.toSignature))
  funext q x reply y
  rcases q with ⟨_, event⟩
  cases event with
  | ask key =>
    change (∃ r, f.reply ⟨_, Event.ask key⟩ r = reply ∧ True) = (admits key reply = true)
    exact propext ((exists_congr fun _ => ⟨And.left, fun h => ⟨h, trivial⟩⟩).trans (exactMask key reply).symm)

theorem refinementAtUnder_valid_liftSat [DecidableEq F]
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
            (leftEntry.refinementSentence rightEntry .leftToRight leftAmbient rightAmbient leftRecord rightRecord)) := by
  let sentence := leftEntry.refinementSentence rightEntry .leftToRight leftAmbient rightAmbient leftRecord rightRecord
  have reduced := TraceInstitution.satisfaction_lift (S := signature.traceSignature) (T := ⟨Target.obj⟩)
    f.hom f.property (TraceInstitution.allRepliesModel ⟨Target.obj⟩) sentence
  rw [reduct_allReplies_eq f.hom admits exactMask] at reduced
  exact (Program.refinementAtUnder?_iff_traceSat admits packet leftEntry rightEntry leftAmbient rightAmbient
    leftRecord rightRecord leftAgrees rightAgrees).trans
      (reduced.symm.trans (TraceInstitution.liftInstitution_valid_iff Target _).symm)

theorem refinementAt_valid_liftSat [DecidableEq F]
    (f : TraceSignature.includeInjectiveRequests.obj signature.traceSignature ⟶ Target)
    (onto : ∀ q, Function.Surjective (f.hom.reply q))
    (packet : Denote (inputs input)) (leftEntry : PackedEntry left input) (rightEntry : PackedEntry right input)
    (leftAmbient rightAmbient leftRecord rightRecord : Semantics.Env Atom)
    (leftAgrees : leftEntry.recordAgrees packet leftRecord) (rightAgrees : rightEntry.recordAgrees packet rightRecord) :
    left.refinementAt? right input packet = true ↔
      ∀ policy : TraceInstitution.liftInstitution.{0,1,0}.Mod.obj (Opposite.op Target),
        TraceInstitution.liftInstitution.{0,1,0}.Sat Target policy
          (TraceInstitution.liftInstitution.{0,1,0}.Sen.map f
            (leftEntry.refinementSentence rightEntry .leftToRight leftAmbient rightAmbient leftRecord rightRecord)) := by
  rw [Program.refinementAt?_iff_traceSat packet leftEntry rightEntry leftAmbient rightAmbient leftRecord rightRecord
      leftAgrees rightAgrees, leftEntry.sat_refinementSentence_iff, TraceInstitution.liftInstitution_valid_iff,
    refinementSentence_lifted]
  change TraceLE (leftEntry.observe leftAmbient leftRecord) (rightEntry.observe rightAmbient rightRecord) ↔
    TraceInstitution.Sat (TraceInstitution.allRepliesModel ⟨Target.obj⟩)
      ⟨_, leftEntry.observeMapped f.hom leftAmbient leftRecord,
        HasTrace (rightEntry.observeMapped f.hom rightAmbient rightRecord)⟩
  rw [TraceInstitution.sat_allReplies_hasTrace_iff]
  erw [leftEntry.observe_mapped, rightEntry.observe_mapped]
  exact (f.hom.traceLE_iff_of_surjective f.property onto).symm

theorem projectReplyMask_exact {Mid Out : Silmaril.Elgot.ITree.Signature.{0}}
    (f : signature.traceSignature.toSignature ⟶ Mid) (g : Mid ⟶ Out)
    [finite : ∀ key : signature.Request, Fintype (f.request ⟨_, Event.ask key⟩).1]
    (admits : ∀ key : signature.Request, (f.request ⟨_, Event.ask key⟩).1 → Bool)
    (exactSecond : ∀ key r, admits key r = true ↔
      ∃ targetReply, g.reply (f.request ⟨_, Event.ask key⟩) targetReply = r)
    (key : signature.Request) (reply : signature.Reply key) :
    signature.projectReplyMask f admits key reply = true ↔ signature.ReplyRealizable (f ≫ g) key reply := by
  simp only [PrimitiveSignature.projectReplyMask, decide_eq_true_eq, exactSecond, PrimitiveSignature.ReplyRealizable]
  constructor
  · rintro ⟨r, ⟨targetReply, rfl⟩, equal⟩
    exact ⟨targetReply, equal⟩
  · rintro ⟨targetReply, equal⟩
    exact ⟨g.reply (f.request ⟨_, Event.ask key⟩) targetReply, ⟨targetReply, rfl⟩, equal⟩

theorem refinementAtUnder_staged_liftSat [DecidableEq F]
    {Mid : Silmaril.Elgot.ITree.Signature.InjectiveRequests.{0}}
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
          (leftEntry.refinementSentence rightEntry .leftToRight leftAmbient rightAmbient leftRecord rightRecord)) := by
  let sentence := leftEntry.refinementSentence rightEntry .leftToRight leftAmbient rightAmbient leftRecord rightRecord
  let all := TraceInstitution.allRepliesModel ⟨Target.obj⟩
  have reduct := reduct_allReplies_eq (Target := Target) (f.hom ≫ g.hom)
    (signature.projectReplyMask f.hom (finite := finiteMid) admits) (projectReplyMask_exact f.hom g.hom (finite := finiteMid) admits exactSecond)
  change all.reduct (f.hom ≫ g.hom) = _ at reduct
  erw [Model.reduct_comp] at reduct
  have sat := TraceInstitution.satisfaction_lift (S := signature.traceSignature) (T := ⟨Mid.obj⟩)
    f.hom f.property (all.reduct g.hom) sentence
  erw [reduct] at sat
  exact (Program.refinementAtUnder?_iff_traceSat (signature.projectReplyMask f.hom (finite := finiteMid) admits) packet leftEntry rightEntry
    leftAmbient rightAmbient leftRecord rightRecord leftAgrees rightAgrees).trans sat.symm

end Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution

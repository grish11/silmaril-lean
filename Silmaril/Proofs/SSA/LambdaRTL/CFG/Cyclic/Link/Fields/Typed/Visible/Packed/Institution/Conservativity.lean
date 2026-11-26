module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution.Thms

@[expose] public section

namespace Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution

open Silmaril.Elgot.ITree (Tree HasTrace TraceLE)
open Silmaril.Elgot.ITree.Finite (Event)
open Silmaril.Logic.ITree
open Silmaril.Isotope.LambdaSSA
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Program (PackedEntry MismatchDirection)

variable {F : Type} {signature : PrimitiveSignature F}

private theorem sat_of_inclusion {R : Type 1}
    {source target : Tree (Event signature.Request signature.Reply) R} (included : TraceLE source target)
    (policy : Silmaril.Logic.ITree.Model.{0, 0} signature.traceSignature.toSignature) :
    TraceInstitution.Sat policy ⟨R, source, HasTrace target⟩ :=
  fun _ _ _ seen => (included.handledTrace seen).1

variable {a b : Nat} {inputs : Fin a → PacketType} {outputs : Fin b → PacketType}
  {left right : Program signature inputs outputs} {input : Fin a}

theorem sat_all_iff (leftEntry : PackedEntry left input) (rightEntry : PackedEntry right input)
    (direction : MismatchDirection) (leftAmbient rightAmbient leftRecord rightRecord : Semantics.Env Atom) :
    let sentence := leftEntry.refinementSentence rightEntry direction leftAmbient rightAmbient leftRecord rightRecord
    TraceInstitution.Sat signature.traceModel sentence ↔
      ∀ policy : Silmaril.Logic.ITree.Model.{0, 0} signature.traceSignature.toSignature, TraceInstitution.Sat policy sentence := by
  dsimp only
  constructor
  · intro unrestricted policy
    have included := (leftEntry.sat_refinementSentence_iff rightEntry direction
      leftAmbient rightAmbient leftRecord rightRecord).mp unrestricted
    cases direction <;> exact sat_of_inclusion included policy
  · exact fun valid => valid signature.traceModel

private theorem unrestricted_model :
    signature.traceModelWithHandler (fun (_ : Unit) _ _ => some ()) (fun _ => true) = signature.traceModel := by
  have initial : (fun _ : Unit => true = true) = fun _ => True := by
    funext _
    simp
  have step : Silmaril.Elgot.ITree.Finite.statefulReplyHandler (Q := signature.Request) (Reply := signature.Reply)
      (fun (_ : Unit) _ _ => some ()) = fun _ _ _ _ => True := by
    funext request state reply next
    rcases request with ⟨_, request⟩
    cases request
    cases next
    simp [Silmaril.Elgot.ITree.Finite.statefulReplyHandler]
  unfold PrimitiveSignature.traceModelWithHandler PrimitiveSignature.traceModel
  rw [initial, step]
  rfl

theorem all_finite_checkers_iff [DecidableEq F] (packet : Denote (inputs input))
    (leftEntry : PackedEntry left input) (rightEntry : PackedEntry right input)
    (leftAmbient rightAmbient leftRecord rightRecord : Semantics.Env Atom)
    (leftAgrees : leftEntry.recordAgrees packet leftRecord) (rightAgrees : rightEntry.recordAgrees packet rightRecord) :
    left.refinementAt? right input packet = true ↔
      ∀ (H : Type) [DecidableEq H] [Fintype H] (advance : H → ∀ key, signature.Reply key → Option H)
        (initial : H → Bool), left.refinementWithHandler? advance initial right input packet = true := by
  let decision := Program.refinementAt?_iff_traceSat packet leftEntry rightEntry
    leftAmbient rightAmbient leftRecord rightRecord leftAgrees rightAgrees
  let all := sat_all_iff leftEntry rightEntry .leftToRight leftAmbient rightAmbient leftRecord rightRecord
  constructor
  · intro accepted H _ _ advance initial
    exact (Program.refinementWithHandler?_iff_traceSat advance initial packet leftEntry rightEntry
      leftAmbient rightAmbient leftRecord rightRecord leftAgrees rightAgrees).mpr
      (all.mp (decision.mp accepted) (signature.traceModelWithHandler advance initial))
  · intro accepted
    apply decision.mpr
    have sat := (Program.refinementWithHandler?_iff_traceSat (fun (_ : Unit) _ _ => some ()) (fun _ => true)
      packet leftEntry rightEntry leftAmbient rightAmbient leftRecord rightRecord leftAgrees rightAgrees).mp
      (accepted Unit (fun _ _ _ => some ()) (fun _ => true))
    change TraceInstitution.Sat (signature.traceModelWithHandler (fun (_ : Unit) _ _ => some ()) (fun _ => true)) _ at sat
    rwa [unrestricted_model] at sat

end Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution

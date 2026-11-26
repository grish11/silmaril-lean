module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution.Defs
public import Silmaril.Logic.ITree.Institution.Trace.Thms

@[expose] public section

namespace Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution

open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
open Silmaril.Elgot.ITree
open Silmaril.Elgot.ITree.Finite (Event)
open Silmaril.Logic.ITree
open Silmaril.Isotope.LambdaSSA
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Program (PackedEntry MismatchDirection)

variable {F : Type} {signature : PrimitiveSignature F}

private theorem replay_all {R : Type 1} (trace : Trace (Event signature.Request signature.Reply) R) :
    Replay signature.traceModel.step () trace := by
  induction trace with
  | «prefix» | request _ | result _ => trivial
  | exchange _ _ _ ih => exact ⟨(), trivial, ih⟩

theorem handledTrace_iff {R : Type 1} (tree : Tree (Event signature.Request signature.Reply) R)
    (trace : Trace (Event signature.Request signature.Reply) R) :
    HandledTrace signature.traceModel.step () tree trace ↔ HasTrace tree trace :=
  ⟨And.left, fun seen => ⟨seen, replay_all trace⟩⟩

private theorem sat_iff {R : Type 1} (source target : Tree (Event signature.Request signature.Reply) R) :
    TraceInstitution.Sat signature.traceModel ⟨R, source, HasTrace target⟩ ↔ TraceLE source target :=
  ⟨fun sat trace seen => sat () trivial trace ((handledTrace_iff source trace).mpr seen),
    fun included _ _ trace seen => included trace seen.1⟩

variable {a b : Nat} {inputs : Fin a → PacketType} {outputs : Fin b → PacketType}
  {left right : Program signature inputs outputs} {input : Fin a}

theorem sat_refinementSentence_iff
    (leftEntry : PackedEntry left input) (rightEntry : PackedEntry right input)
    (direction : MismatchDirection) (leftAmbient rightAmbient leftRecord rightRecord : Semantics.Env Atom) :
    TraceInstitution.institution.{0, 1, 0}.Sat signature.traceSignature ⟨signature.traceModel⟩
      (leftEntry.refinementSentence rightEntry direction leftAmbient rightAmbient leftRecord rightRecord) ↔
    let l := leftEntry.observe leftAmbient leftRecord
    let r := rightEntry.observe rightAmbient rightRecord
    match direction with
    | .leftToRight => TraceLE l r
    | .rightToLeft => TraceLE r l := by
  cases direction <;> exact sat_iff _ _

end Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution

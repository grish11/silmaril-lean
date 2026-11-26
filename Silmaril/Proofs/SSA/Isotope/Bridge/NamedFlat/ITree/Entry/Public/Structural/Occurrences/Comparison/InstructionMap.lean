module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Occurrences.Comparison.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Signature.Thms

@[expose] public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.Occurrences.Comparison

open CategoryTheory Silmaril.Isotope
open Silmaril.Isotope.Bridge.NamedFlat.Entry.Public
open Silmaril.SSA.LambdaRTL (CFG)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction (Transfer region_mapInstr region_reindex)
open LambdaSSA.FiniteCFG (packedTreeOutput)
open Silmaril.Logic.ITree

variable {V K : Type 1} [DecidableEq V] [DecidableEq K] {F G : Type}
  {s : PrimitiveSignature F} {t : PrimitiveSignature G} {source target : CFG V K F}
  {exits : List K} {fields : K → List V} {inputType rightType : PacketType}
  {outputs : Fin exits.length → PacketType} {opcode : F → G}
  {left : StructuralEntry s source exits fields inputType outputs}
  {right : StructuralEntry s target exits fields rightType outputs}
  {mappedLeft : StructuralEntry t (source.mapOp opcode) exits fields inputType outputs}
  {mappedRight : StructuralEntry t (target.mapOp opcode) exits fields rightType outputs}

theorem observe_map (old : OccurrenceAdmission left) (new : OccurrenceAdmission mappedLeft)
    (f : s.traceSignature ⟶ t.traceSignature)
    (primitives : ∀ op arg, t.primitive (opcode op) arg = f.hom.tree id (s.primitive op arg))
    (packet : Denote inputType)
    (code : new.code.erase = old.code.erase.mapInstr opcode)
    (slots : mappedLeft.occurrenceStore packet = left.occurrenceStore packet) :
    mappedLeft.observeOccurrences packet = f.hom.tree id (left.observeOccurrences packet) := by
  rw [new.observe_eq_elaborated, old.observe_eq_elaborated, code, region_mapInstr, slots]
  have pureMapped : (fun out : Transfer Atom => f.hom.tree id (pure (packedTreeOutput out))) =
      (fun out => pure (packedTreeOutput out)) := funext fun out => f.hom.tree_pure (packedTreeOutput out)
  erw [f.hom.tree_bind, region_reindex f.hom, funext (fun op => funext (primitives op)), pureMapped]
  rfl

theorem sentence_map (old : OccurrenceComparison left right) (new : OccurrenceComparison mappedLeft mappedRight)
    (f : s.traceSignature ⟶ t.traceSignature)
    (primitives : ∀ op arg, t.primitive (opcode op) arg = f.hom.tree id (s.primitive op arg))
    (a : Denote inputType) (b : Denote rightType)
    (leftCode : new.leftAdmission.code.erase = old.leftAdmission.code.erase.mapInstr opcode)
    (rightCode : new.rightAdmission.code.erase = old.rightAdmission.code.erase.mapInstr opcode)
    (leftSlots : mappedLeft.occurrenceStore a = left.occurrenceStore a)
    (rightSlots : mappedRight.occurrenceStore b = right.occurrenceStore b) :
    new.sentence a b = (old.sentence a b).translate f := by
  change (⟨_, mappedLeft.observeOccurrences a, Silmaril.Elgot.ITree.HasTrace (mappedRight.observeOccurrences b)⟩ :
    TraceInstitution.Sentence t.traceSignature) = (old.sentence a b).translate f
  rw [observe_map old.leftAdmission new.leftAdmission f primitives a leftCode leftSlots,
    observe_map old.rightAdmission new.rightAdmission f primitives b rightCode rightSlots]
  exact (TraceInstitution.translate_hasTrace f _ _).symm

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.Occurrences.Comparison

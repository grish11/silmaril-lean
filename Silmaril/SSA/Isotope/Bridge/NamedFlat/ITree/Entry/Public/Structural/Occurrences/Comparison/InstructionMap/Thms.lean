module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Occurrences.Comparison.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Occurrences.Comparison.InstructionMap

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Public

open CategoryTheory Silmaril.Logic.ITree
open Silmaril.SSA.LambdaRTL (CFG)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible

universe u

variable {V K : Type 1} [DecidableEq V] [DecidableEq K] {F G : Type}
  {s : PrimitiveSignature F} {t : PrimitiveSignature G} {source target : CFG V K F}
  {exits : List K} {fields : K → List V} {inputType rightType : PacketType}
  {outputs : Fin exits.length → PacketType} {opcode : F → G}
  {left : StructuralEntry s source exits fields inputType outputs}
  {right : StructuralEntry s target exits fields rightType outputs}
  {mappedLeft : StructuralEntry t (source.mapOp opcode) exits fields inputType outputs}
  {mappedRight : StructuralEntry t (target.mapOp opcode) exits fields rightType outputs}
  (old : OccurrenceComparison left right) (new : OccurrenceComparison mappedLeft mappedRight)
  (f : s.traceSignature ⟶ t.traceSignature)
  (primitives : ∀ op arg, t.primitive (opcode op) arg = f.hom.tree id (s.primitive op arg))
  (a : Denote inputType) (b : Denote rightType)
  (leftCode : new.leftAdmission.code.erase = old.leftAdmission.code.erase.mapInstr opcode)
  (rightCode : new.rightAdmission.code.erase = old.rightAdmission.code.erase.mapInstr opcode)
  (leftSlots : mappedLeft.occurrenceStore a = left.occurrenceStore a)
  (rightSlots : mappedRight.occurrenceStore b = right.occurrenceStore b)

include primitives leftCode rightCode leftSlots rightSlots

/-- At matching independently typed packets, translate the sentence of
the actual admitted runners to the sentence of the opcode-mapped admissions.
The positional readbacks and slot stores identify the exact endpoints.
The ordered exit and selected live-outs keep their original encoding. -/
theorem OccurrenceComparison.sentence_mapInstr :
    new.sentence a b = (old.sentence a b).translate f :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.Occurrences.Comparison.sentence_map
    old new f primitives a b leftCode rightCode leftSlots rightSlots

/-- The checked opcode-mapped sentence in any target reply policy agrees
with the original checked sentence in the existing reduct. -/
theorem OccurrenceComparison.sat_mapInstr_iff (policy : Model.{0, u} t.traceSignature.toSignature) :
    TraceInstitution.Sat policy (new.sentence a b) ↔
      TraceInstitution.Sat (policy.reduct f.hom) (old.sentence a b) := by
  rw [old.sentence_mapInstr new f primitives a b leftCode rightCode leftSlots rightSlots]
  exact TraceInstitution.satisfaction f policy _

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Public

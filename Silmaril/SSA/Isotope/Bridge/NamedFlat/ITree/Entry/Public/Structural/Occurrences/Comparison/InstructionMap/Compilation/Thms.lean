module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Occurrences.Comparison.InstructionMap.Compilation.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Occurrences.Comparison.Compilation

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Public

open CategoryTheory Silmaril.Logic.ITree
open Silmaril.SSA.LambdaRTL (CFG)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
open Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.Occurrences.Compilation
  (accepted_map typed_map)
open OpcodeCompilation (castBlocks)
open LambdaSSA (FiniteCFG)

universe u

variable {V K : Type 1} [DecidableEq V] [DecidableEq K] {F G : Type}
  {s : PrimitiveSignature F} {t : PrimitiveSignature G} {source target : CFG V K F}
  {exits : List K} {fields : K → List V} {inputType rightType : PacketType}
  {outputs : Fin exits.length → PacketType}
  (left : StructuralEntry s source exits fields inputType outputs)
  (right : StructuralEntry s target exits fields rightType outputs)
  (rename : s.Renaming t)

theorem StructuralEntry.occurrenceGraph_mapOpcode :
    (left.mapOpcode rename).occurrenceGraph = left.occurrenceGraph.mapOp rename.opcode :=
  congrArg (fun g : CFG Register left.program.Address G =>
    { g with entry := .term (.br (⟨left.program.entry 0⟩ : left.program.Address) left.occurrenceOperand) })
    (left.program.compile_mapOpcode rename 0)

theorem StructuralEntry.occurrenceStore_mapOpcode (packet : Denote inputType) :
    (left.mapOpcode rename).occurrenceStore packet = left.occurrenceStore packet := rfl

theorem StructuralEntry.seed?_mapOpcode (initial : V → Value Atom) :
    (left.mapOpcode rename).seed? initial = left.seed? initial := rfl

theorem StructuralEntry.checkOccurrenceComparison?_isSome_mapOpcode :
    ((left.mapOpcode rename).checkOccurrenceComparison? (right.mapOpcode rename)).isSome =
      (left.checkOccurrenceComparison? right).isSome := by
  rw [Bool.eq_iff_iff, (left.mapOpcode rename).checkOccurrenceComparison?_isSome_iff,
    left.checkOccurrenceComparison?_isSome_iff]
  rfl

variable {left right}

/-- Transport the exact named elaboration and typing of a generated entry.
The positional table is mapped at the existing capture and exit positions. -/
def OccurrenceAdmission.mapOpcode (old : OccurrenceAdmission left) :
    OccurrenceAdmission (left.mapOpcode rename) :=
  have length : left.occurrenceGraph.blocks.length = (left.mapOpcode rename).occurrenceGraph.blocks.length := by
    rw [left.occurrenceGraph_mapOpcode rename]
    exact (List.length_map ..).symm
  ⟨castBlocks length (old.code.mapInstr rename.opcode),
    by
      exact accepted_map rename.opcode left.occurrenceGraph (left.mapOpcode rename).occurrenceGraph
        (left.occurrenceGraph_mapOpcode rename).symm _ left.occurrenceNames length old.accepted,
    by exact typed_map rename length old.typed⟩

private theorem erase_cast {m n e c : Nat} (length : m = n) (code : FiniteCFG G m e c) :
    (castBlocks length code).erase = code.erase := by
  subst n
  rfl

/-- Every successful recheck of the renamed generated entry has exactly the
mapped positional code after erasure of the block-count index. -/
theorem OccurrenceAdmission.erase_mapOpcode (old : OccurrenceAdmission left)
    (new : OccurrenceAdmission (left.mapOpcode rename)) :
    new.code.erase = old.code.erase.mapInstr rename.opcode := by
  have equal := Option.some.inj (new.accepted.symm.trans (old.mapOpcode rename).accepted)
  rw [equal]
  exact (erase_cast _ _).trans (FiniteCFG.erase_mapInstr _ _)

/-- Map both exact occurrences. The same result is available by rechecking
the renamed structural entries when the original packet check succeeds. -/
def OccurrenceComparison.mapOpcode (old : OccurrenceComparison left right) :
    OccurrenceComparison (left.mapOpcode rename) (right.mapOpcode rename) :=
  ⟨old.leftAdmission.mapOpcode rename, old.rightAdmission.mapOpcode rename⟩

/-- At the two typed packets, the existing reduct square needs only the
primitive law for the given trace arrow. Compilation and slot alignment
follow for any exact admissions of the mapped structural entries. -/
theorem OccurrenceComparison.sat_mapOpcode_iff (old : OccurrenceComparison left right)
    (new : OccurrenceComparison (left.mapOpcode rename) (right.mapOpcode rename))
    (f : s.traceSignature ⟶ t.traceSignature)
    (primitives : ∀ op arg, t.primitive (rename.opcode op) arg = f.hom.tree id (s.primitive op arg))
    (a : Denote inputType) (b : Denote rightType)
    (policy : Model.{0, u} t.traceSignature.toSignature) :
    TraceInstitution.Sat policy (new.sentence a b) ↔
      TraceInstitution.Sat (policy.reduct f.hom) (old.sentence a b) :=
  old.sat_mapInstr_iff new f primitives a b (old.leftAdmission.erase_mapOpcode rename new.leftAdmission)
    (old.rightAdmission.erase_mapOpcode rename new.rightAdmission)
    (left.occurrenceStore_mapOpcode rename a) (right.occurrenceStore_mapOpcode rename b) policy

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Public

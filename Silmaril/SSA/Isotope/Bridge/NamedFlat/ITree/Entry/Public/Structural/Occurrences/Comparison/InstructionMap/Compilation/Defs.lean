module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Occurrences.Comparison.InstructionMap.Thms
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.InstructionMap.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Occurrences.Comparison.Compilation

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Public

open Silmaril.SSA.LambdaRTL (CFG)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic
open Phi.Certified.Entry.OrderedExits.Readback (Provenance packetTerm)
open LambdaSSA (FiniteCFG Flat)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible

namespace OpcodeCompilation

open Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.Occurrences.Compilation
  (accepted_map typed_map packet_closed_map)

variable {F G : Type} {s : PrimitiveSignature F} {t : PrimitiveSignature G}

def castBlocks {b b' e n : Nat} (length : b = b') (code : FiniteCFG G b e n) :
    FiniteCFG G b' e n :=
  length ▸ code

private theorem packetTerm_map {n : Nat} (opcode : F → G) (seed : Silmaril.SSA.LambdaRTL.Val (Fin n)) :
    (packetTerm seed).mapInstr opcode = packetTerm seed := by
  induction seed <;> simp_all [packetTerm, LambdaSSA.Tm.mapInstr]

/-- Move exact positional readback along the two unchanged block tables.
The original seed and selected public slot are retained by construction. -/
def mapProvenance {b b' p p' e q n m : Nat} {source : FiniteCFG F b e n} {target : FiniteCFG F p q m}
    (old : Provenance source target) (opcode : F → G) (sourceLength : b = b') (targetLength : p = p') :
    Provenance (castBlocks sourceLength (source.mapInstr opcode)) (castBlocks targetLength (target.mapInstr opcode)) where
  count := sourceLength.symm.trans (old.count.trans targetLength)
  exitCount := old.exitCount
  start := old.start.cast sourceLength
  seed := old.seed
  slot := old.slot
  sourceEntry := by
    cases sourceLength
    simp [castBlocks, FiniteCFG.mapInstr, old.sourceEntry, LambdaSSA.Region.mapInstr, packetTerm_map]
  publicEntry := by
    cases targetLength
    simp [castBlocks, FiniteCFG.mapInstr, old.publicEntry, LambdaSSA.Region.mapInstr, LambdaSSA.Tm.mapInstr]
  row i := cast (congrArg (fun x => Flat G (x + e) 1) sourceLength)
    ((old.row (i.cast sourceLength.symm)).mapInstr opcode)
  sourceRow i := by
    cases sourceLength
    simpa [castBlocks, FiniteCFG.mapInstr] using congrArg (LambdaSSA.Region.mapInstr opcode) (old.sourceRow i)
  publicRow i := by
    cases sourceLength
    cases targetLength
    simpa [castBlocks, FiniteCFG.mapInstr] using congrArg (LambdaSSA.Region.mapInstr opcode) (old.publicRow i)

end OpcodeCompilation

open OpcodeCompilation
open Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.Occurrences.Compilation
  (accepted_map typed_map packet_closed_map)

variable {V K : Type 1} [DecidableEq V] [DecidableEq K] {F G : Type}
  {s : PrimitiveSignature F} {t : PrimitiveSignature G} {source target : CFG V K F}
  {exits : List K} {fields : K → List V} {inputType rightType : PacketType}
  {outputs : Fin exits.length → PacketType}

def OpcodeCompilation.mapPacked {a b : Nat} {inputs : Fin a → PacketType} {outputs : Fin b → PacketType}
    {program : Program s inputs outputs} {i : Fin a} (entry : Program.PackedEntry program i)
    (rename : s.Renaming t) : Program.PackedEntry (program.mapOpcode rename) i :=
  let graph := program.compile i
  let mapped := (program.mapOpcode rename).compile i
  have written : graph.mapOp rename.opcode = mapped := (program.compile_mapOpcode rename i).symm
  have length : graph.blocks.length = mapped.blocks.length := by
    rw [← written]
    exact (List.length_map ..).symm
  ⟨entry.count, entry.captures, entry.context, (fun j => entry.blocks (j.cast length.symm)), entry.exits,
    castBlocks length (entry.target.mapInstr rename.opcode),
    by exact accepted_map rename.opcode graph mapped written _ entry.captures length entry.accepted,
    by exact typed_map rename length entry.typed⟩

/-- Rename a structural entry while retaining its typed seed, capture order,
checked dispatcher and attached live-out profile. -/
def StructuralEntry.mapOpcode (entry : StructuralEntry s source exits fields inputType outputs)
    (rename : s.Renaming t) :
    StructuralEntry t (source.mapOp rename.opcode) exits fields inputType outputs :=
  let graph := LiveOut.attach fields source
  let mapped := LiveOut.attach fields (source.mapOp rename.opcode)
  have written : graph.mapOp rename.opcode = mapped := by
    exact (LiveOut.attach_mapOp rename.opcode fields source).symm
  have length : graph.blocks.length = mapped.blocks.length := by
    rw [← written]
    exact (List.length_map ..).symm
  let packed := mapPacked entry.entry rename
  have publicLength : (entry.program.compile 0).blocks.length =
      ((entry.program.mapOpcode rename).compile 0).blocks.length := by
    rw [Program.compile_mapOpcode]
    exact (List.length_map ..).symm
  ⟨entry.names, entry.program.mapOpcode rename, packed,
    by exact (show RoundTrip.PacketClosed mapped from written ▸ packet_closed_map rename.opcode entry.closed),
    castBlocks length (entry.flat.mapInstr rename.opcode),
    by exact accepted_map rename.opcode graph mapped written exits (fun i => entry.names[i.val]) length entry.accepted,
    mapProvenance entry.provenance rename.opcode length publicLength, entry.typedSeed, entry.publicCaptures⟩

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Public

module

public import Silmaril.Wasm.Region.ByteMap.Produce.Defs
public import Silmaril.Wasm.Region.ByteMap.Module.Thms
import Silmaril.Proofs.Wasm.Region.ByteMapProduce

@[expose] public section
namespace Silmaril.Wasm.Region.ByteMap.Produce

theorem MappedModule.absolute_slice {raw : List UInt8} (m : MappedModule raw)
    (i : Fin m.source.layout.bodies.length) (entry : ByteMapEntry)
    (member : entry ∈ (m.maps i).certified.map.entries) :
    (raw.drop (m.source.layout.bodyStart i.val + entry.bytes.start)).take
      (entry.bytes.stop - entry.bytes.start) =
      (m.source.layout.bodies[i]).input.spanBytes entry.bytes := Proofs.absolute_slice m i entry member

/-- Every instruction in every reused extracted block's sequence has a
validated byte row. The existing lookup premise stays explicit. -/
theorem FullMap.cfg_coverage {input : Input} (map : FullMap input)
    {b : Cfg.BlockId} {sg : Cfg.Segment} {body : Silmaril.Wasm.Expr}
    (member : (b, sg) ∈ Cfg.blocks input.body)
    (lookup : Cfg.Machine.seqAt input.body b.seq = some body) (k : Fin body.length) :
    ∃ entry ∈ map.certified.map.entries,
      entry.decoded = ⟨input.functionIndex, b.seq, k.val⟩ ∧ Nested.DecodesAt input entry.decoded entry.bytes := by
  obtain ⟨entry, hm, eq, sound⟩ := Nested.cfg_coverage_sound map.validated map.coverage member lookup k
  exact ⟨entry, hm, eq, eq ▸ sound⟩

theorem MappedModule.body_count {raw : List UInt8} (m : MappedModule raw) :
    m.source.layout.bodies.length = m.source.decoded.funcs.length := m.source.checked.2.2.2.2.2.1

/-- Instruction grammar on the original module/file bytes, retaining the
decoded sequence path and the import-adjusted function identity. -/
theorem MappedModule.instruction_source {raw : List UInt8} (m : MappedModule raw)
    (i : Fin m.source.layout.bodies.length) (entry : ByteMapEntry)
    (member : entry ∈ (m.maps i).certified.map.entries) :
    ∃ seq, Nested.Located (m.source.layout.bodies[i]).input seq ∧
      entry.decoded.functionIndex = m.source.decoded.importedFunctions.length + i.val ∧
      entry.decoded.sequencePath = seq.path ∧
      ∃ instr, seq.body[entry.decoded.instructionOffset]? = some instr ∧
        Silmaril.Wasm.Binary.Core.Instr Silmaril.Wasm.Binary.Core.Forms.all
          ((raw.drop (m.source.layout.bodyStart i.val + entry.bytes.start)).take
            (entry.bytes.stop - entry.bytes.start)) instr := by
  obtain ⟨seq, located, fn, path, _, _, _, _, instr, pos, encoded⟩ :=
    (m.maps i).certified.map.correct entry member
  exact ⟨seq, located, fn.trans (m.source.function_index i), path, instr, pos,
    m.absolute_slice i entry member ▸ encoded⟩

end Silmaril.Wasm.Region.ByteMap.Produce

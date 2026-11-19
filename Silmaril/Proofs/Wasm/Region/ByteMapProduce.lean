module

public import Silmaril.Wasm.Region.ByteMap.Produce.Defs
public import Silmaril.Wasm.Region.ByteMap.Module.Thms

@[expose] public section
namespace Silmaril.Wasm.Region.ByteMap.Produce.Proofs

/-- Compose a bounded body-relative byte slice with its checked module slice. -/
theorem absolute_slice {raw : List UInt8} (m : MappedModule raw)
    (i : Fin m.source.layout.bodies.length) (entry : ByteMapEntry)
    (member : entry ∈ (m.maps i).certified.map.entries) :
    (raw.drop (m.source.layout.bodyStart i.val + entry.bytes.start)).take
      (entry.bytes.stop - entry.bytes.start) =
      (m.source.layout.bodies[i]).input.spanBytes entry.bytes := by
  have bounded := ((m.maps i).certified.map.bounds entry member).2
  have width := Nat.sub_le_sub_right bounded entry.bytes.start
  unfold Input.spanBytes
  rw [← m.source.body_bytes i, List.drop_take, List.drop_drop, List.take_take]
  rw [Nat.min_eq_left width]

end Silmaril.Wasm.Region.ByteMap.Produce.Proofs

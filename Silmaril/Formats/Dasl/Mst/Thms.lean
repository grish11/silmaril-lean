module

public import Silmaril.Formats.Dasl.Mst.Defs
public import Silmaril.Semantics.Naming.Thms
import Silmaril.Proofs.Formats.Dasl.Mst

public section

namespace Silmaril.Formats.Dasl.Mst

variable {Name : Type}

theorem prefixLength_le (previous key : Key) : prefixLength previous key ≤ previous.length :=
  Proofs.Formats.Dasl.Mst.prefixLength_le previous key

theorem take_prefix (previous key : Key) : previous.take (prefixLength previous key) = key.take (prefixLength previous key) :=
  Proofs.Formats.Dasl.Mst.take_prefix previous key

theorem common_prefix_le (left right : Key) (count : Nat) (leftBound : count ≤ left.length)
    (rightBound : count ≤ right.length) (same : left.take count = right.take count) : count ≤ prefixLength left right :=
  Proofs.Formats.Dasl.Mst.common_prefix_le left right count leftBound rightBound same

theorem WireNode.expand_compress (node : Node Name) : node.compress.expand? = some node := by
  cases node
  simp [WireNode.expand?, Node.compress, Proofs.Formats.Dasl.Mst.expand_compress]

theorem Node.compress_of_expand {encoded : WireNode Name} {node : Node Name}
    (hit : encoded.expand? = some node) : node.compress = encoded := by
  obtain ⟨_, decoded, rfl⟩ := Option.map_eq_some_iff.mp hit
  cases encoded
  simp [Node.compress, Proofs.Formats.Dasl.Mst.compress_expand _ _ decoded]

theorem wire_roundtrip {node : WireNode Name} {value : Shallow Name}
    (hit : encodeWireNode? node = some value) : decodeWireNode? value = some node :=
  Proofs.Formats.Dasl.Mst.wire_roundtrip hit

theorem node_roundtrip {node : Node Name} {value : Shallow Name}
    (hit : encodeNode? node = some value) : decodeNode? value = some node := by
  have wire := wire_roundtrip hit
  simp [decodeNode?, wire, WireNode.expand_compress]

@[expose] def nodeCodec : Encode.PartialCodec (Node Name) (Shallow Name) :=
  ⟨encodeNode?, decodeNode?, fun _ _ => node_roundtrip⟩

open Silmaril.Semantics.Naming in
theorem nodes_binding {objects : Relation Name (Shallow Name)} (bound : Binding objects) : Binding (nodes objects) :=
  bound.push (graph_binding _)

end Silmaril.Formats.Dasl.Mst

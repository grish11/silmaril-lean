module

public import Silmaril.Formats.Arrow.BinaryView.Column.Defs
import Silmaril.Proofs.Formats.Arrow.BinaryView.Column

@[expose] public section

namespace Silmaril.Formats.Arrow.BinaryView.Column

/-- Buffer admission checks the declared shape and all supplied byte extents. -/
theorem checkBuffers_iff (limits : Limits) (node : FieldNode) (nullable : Bool) (input : Buffers) :
    checkBuffers limits node nullable input = .ok () ↔ BuffersFit limits node nullable input :=
  Proofs.Formats.Arrow.BinaryView.Column.checkBuffers_iff limits node nullable input

/-- The column observes exactly the checked slots in bitmap order. -/
theorem readBinary_iff (limits : Limits) (node : FieldNode) (nullable : Bool) (input : Buffers)
    (values : List (Option KBytes)) :
    readBinary limits node nullable input = .ok values ↔ Wire limits node nullable input values :=
  Proofs.Formats.Arrow.BinaryView.Column.readBinary_iff limits node nullable input values

/-- The observation preserves the declared counts and meets the byte budgets. -/
theorem readBinary_bounds {limits : Limits} {node : FieldNode} {nullable : Bool} {input : Buffers}
    {values : List (Option KBytes)} (read : readBinary limits node nullable input = .ok values) :
    BuffersFit limits node nullable input ∧ values.length = node.length ∧
      values.countP Option.isNone = node.nullCount ∧ valueByteCount values ≤ limits.outputBytes :=
  Proofs.Formats.Arrow.BinaryView.Column.readBinary_bounds read

/-- UTF-8 observes the same checked byte windows, decoded in order. -/
theorem readUtf8_iff (limits : Limits) (node : FieldNode) (nullable : Bool) (input : Buffers)
    (values : List (Option String)) :
    readUtf8 limits node nullable input = .ok values ↔
      ∃ slots, Wire limits node nullable input slots ∧
        slots.mapM (·.mapM decodeUtf8) = .ok values :=
  Proofs.Formats.Arrow.BinaryView.Column.readUtf8_iff limits node nullable input values

/-- UTF-8 decoding preserves the number of slots and nulls. -/
theorem readUtf8_counts {limits : Limits} {node : FieldNode} {nullable : Bool} {input : Buffers}
    {values : List (Option String)} (read : readUtf8 limits node nullable input = .ok values) :
    values.length = node.length ∧ values.countP Option.isNone = node.nullCount :=
  Proofs.Formats.Arrow.BinaryView.Column.readUtf8_counts read

end Silmaril.Formats.Arrow.BinaryView.Column

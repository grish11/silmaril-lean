module

public import Silmaril.Formats.Compression.Zstd.Huffman.LiteralState.Defs
import Silmaril.Proofs.Formats.Compression.Zstd.Huffman.LiteralState.Contracts

public section

namespace Silmaril.Formats.Compression.Zstd.Huffman.LiteralState

open LiteralSection (Limits Envelope)

theorem table_checked {profile : TreeDescription.Limits} {state : State profile} {table : SingleStream.Table}
    (available : state.table = some table) :
    ∃ (input : List UInt8) (description : TreeDescription.Prefix), description.Valid profile input ∧ SingleStream.TableWire description.tree table :=
  Proofs.Formats.Compression.Zstd.Huffman.LiteralState.table_checked available

/-- Every accepted section has the exact mode-specific transition, output
    count and extent, within both caller limits. -/
theorem read_sound {limits : Limits} {prior : State limits.tree} {input : List UInt8}
    {result : Result limits.tree} (success : read limits prior input = .ok result) :
    Wire limits prior input result ∧ result.consumed ≤ limits.inputCap ∧
      result.literals.expand.length = result.literals.size ∧ result.literals.size ≤ limits.outputCap :=
  Proofs.Formats.Compression.Zstd.Huffman.LiteralState.read_sound success

theorem consumption_exact {limits : Limits} {prior : State limits.tree} {input : List UInt8}
    {result : Result limits.tree} (wire : Wire limits prior input result) :
    ∃ bytes, input = bytes ++ result.rest ∧ bytes.length = result.consumed :=
  Proofs.Formats.Compression.Zstd.Huffman.LiteralState.consumption_exact wire

theorem suffix_exact {limits : Limits} {prior : State limits.tree} {input : List UInt8}
    {result : Result limits.tree} (wire : Wire limits prior input result) :
    input.drop result.consumed = result.rest := by
  obtain ⟨bytes, shape, count⟩ := consumption_exact wire
  rw [shape, ← count]
  exact List.drop_left

/-- A correctly bounded treeless envelope cannot use an empty dictionary-free state. -/
theorem unavailable_after_reset {limits : Limits} {first : UInt8} {rest : List UInt8} {part : Envelope}
    (kind : first.toNat % 4 = 3) (bounded : Internal.readEnvelope limits first rest = .ok part) :
    read limits (State.empty limits.tree) (first :: rest) = .error .unavailableTable :=
  Proofs.Formats.Compression.Zstd.Huffman.LiteralState.unavailable_after_reset kind bounded

end Silmaril.Formats.Compression.Zstd.Huffman.LiteralState

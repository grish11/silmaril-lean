module

public import Silmaril.Formats.Compression.Brotli.Command.Defs
import Silmaril.Proofs.Formats.Compression.Brotli.Command.Contracts

public section

namespace Silmaril.Formats.Compression.Brotli.Command

open Huffman.Description (Table)

theorem spec_bounds (symbol : Fin 704) :
    (spec symbol).insert.extraBits ≤ 24 ∧ (spec symbol).copy.extraBits ≤ 24 ∧
    (spec symbol).insert.last ≤ 16799809 ∧ 2 ≤ (spec symbol).copy.base ∧
    (spec symbol).copy.last ≤ 16779333 :=
  Proofs.Formats.Compression.Brotli.Command.spec_bounds symbol

theorem spec_implicit_iff (symbol : Fin 704) :
    (spec symbol).distance = .implicitZero ↔ symbol.val < 128 :=
  Proofs.Formats.Compression.Brotli.Command.spec_implicit_iff symbol

theorem ExtrasWire.bounds {symbol : Fin 704} {bits : List Bool} {command : Value}
    (wire : ExtrasWire symbol bits command) :
    command.symbol = symbol ∧ command.distance = (spec symbol).distance ∧
    (spec symbol).insert.base ≤ command.insertLength ∧ command.insertLength ≤ (spec symbol).insert.last ∧
    (spec symbol).copy.base ≤ command.copyLength ∧ command.copyLength ≤ (spec symbol).copy.last ∧
    bits.length = (spec symbol).insert.extraBits + (spec symbol).copy.extraBits :=
  Proofs.Formats.Compression.Brotli.Command.ExtrasWire.bounds wire

theorem Wire.bounds {table : Table} {bits : List Bool} {command : Value} (wire : Wire table bits command) :
    bits.length ≤ 63 ∧ command.insertLength ≤ 16799809 ∧
    2 ≤ command.copyLength ∧ command.copyLength ≤ 16779333 ∧
    (command.distance = .implicitZero ↔ command.symbol.val < 128) :=
  Proofs.Formats.Compression.Brotli.Command.Wire.bounds wire

/-- After a known symbol, commit just the two original extra fields. -/
theorem readExtras_sound {symbol : Fin 704} {bitLimit : Nat}
    {before after : LSBReader} {input : List Bool} {command : Value}
    (rep : before.Rep input) (count : before.count < 8)
    (read : readExtras symbol bitLimit before = .ok (command, after)) :
    ∃ used suffix, ExtrasWire symbol used command ∧ input = used ++ suffix ∧ after.Rep suffix ∧
      after.count < 8 ∧ after.totalRead = before.totalRead + used.length ∧ used.length ≤ bitLimit :=
  Proofs.Formats.Compression.Brotli.Command.readExtras_sound rep count read

theorem readExtras_insert_truncated {symbol : Fin 704} {bitLimit : Nat} {before : LSBReader}
    (cap : (spec symbol).insert.extraBits ≤ bitLimit)
    (missing : before.readBits (spec symbol).insert.extraBits = none) :
    readExtras symbol bitLimit before = .error (.truncated .insertExtra) :=
  Proofs.Formats.Compression.Brotli.Command.readExtras_insert_truncated cap missing

theorem readExtras_copy_truncated {symbol : Fin 704} {bitLimit insert : Nat} {before cursor : LSBReader}
    (insertCap : (spec symbol).insert.extraBits ≤ bitLimit)
    (copyCap : (spec symbol).copy.extraBits ≤ bitLimit - (spec symbol).insert.extraBits)
    (first : before.readBits (spec symbol).insert.extraBits = some (insert, cursor))
    (missing : cursor.readBits (spec symbol).copy.extraBits = none) :
    readExtras symbol bitLimit before = .error (.truncated .copyExtra) :=
  Proofs.Formats.Compression.Brotli.Command.readExtras_copy_truncated insertCap copyCap first missing

/-- Account for the Huffman code and both fields under the shared cap. -/
theorem read_sound {table : Table} {bitLimit : Nat} {before after : LSBReader}
    {input : List Bool} {command : Value} (rep : before.Rep input) (count : before.count < 8)
    (read : read table bitLimit before = .ok (command, after)) :
    ∃ used suffix, Wire table used command ∧ input = used ++ suffix ∧ after.Rep suffix ∧
      after.count < 8 ∧ after.totalRead = before.totalRead + used.length ∧ used.length ≤ bitLimit :=
  Proofs.Formats.Compression.Brotli.Command.read_sound rep count read

/-- The one-type adapter reads using the exact tree from that header. -/
theorem readSingle_sound {header : CompressedHeader.Header} {bitLimit : Nat}
    {before after : LSBReader} {input : List Bool} {command : Value}
    (rep : before.Rep input) (count : before.count < 8)
    (read : readSingle header bitLimit before = .ok (command, after)) :
    header.initial.controls.insertCopy = .single ∧
    ∃ table used suffix, header.insertCopyTrees = [table] ∧ Wire table used command ∧
      input = used ++ suffix ∧ after.Rep suffix ∧ after.count < 8 ∧
      after.totalRead = before.totalRead + used.length ∧ used.length ≤ bitLimit :=
  Proofs.Formats.Compression.Brotli.Command.readSingle_sound rep count read

end Silmaril.Formats.Compression.Brotli.Command

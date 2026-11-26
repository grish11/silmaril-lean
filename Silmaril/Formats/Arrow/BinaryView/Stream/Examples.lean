module

import Silmaril.Formats.Arrow.BinaryView.Stream.Defs
meta import Silmaril.Formats.Arrow.BinaryView.Stream.Defs
import Silmaril.Formats.Arrow.BinaryView.Stream.Fixture
meta import Silmaril.Formats.Arrow.BinaryView.Stream.Fixture
import Silmaril.Formats.Arrow.BinaryView.Schema.Fixture
meta import Silmaril.Formats.Arrow.BinaryView.Schema.Fixture

open Silmaril Silmaril.Formats.Arrow
open BinaryView.Stream BinaryView.Stream.Fixture

#guard match read {} {} binary with
  | .ok ⟨⟨name, nullable, .binary⟩, batches⟩ =>
    name == "blob" && nullable &&
      batches.map (·.map (·.map KBytes.toList)) ==
        [[none, some [255], some "0123456789abcdef".toUTF8.data.toList], [],
          [some [], some "tail".toUTF8.data.toList]]
  | _ => false

#guard match read {} {} utf8 with
  | .ok ⟨⟨name, nullable, .utf8⟩, batches⟩ =>
    name == "text" && nullable &&
      (show List (List (Option String)) from batches) ==
        [[some "α", none, some "雪雪雪雪雪雪"], [], [some "", some "tail", some "🧪🧪🧪🧪"]]
  | _ => false

#guard match read { batches := 0 } {} schemaOnly with
  | .ok ⟨⟨name, nullable, .utf8⟩, batches⟩ => name == "text" && nullable && batches.isEmpty
  | _ => false

private def rejects (result : Except BinaryView.Stream.Error Observed) (expected : BinaryView.Stream.Error) : Bool :=
  match result with
  | .error actual => decide (actual = expected)
  | .ok _ => false

private def eos : KBytes := .leaf 8 0xffffffff

private def schemaOnlyWith (metadata : KBytes) : KBytes :=
  .leaf 4 0xffffffff ++ .leaf 4 metadata.len ++ metadata ++ eos

#guard rejects (read {} {} (binary ++ .leaf 1 0)) (.batch 3 .trailingBytes)
#guard rejects (read {} {} (binary.slice 0 binaryEos)) (.batch 3 (.envelope (.malformed .truncated)))
#guard rejects (read {} {} (binary.slice 0 (binaryLastBody + 1))) (.batch 2 (.body (.malformed .truncated)))
#guard rejects (read {} {} (binary.slice 0 (binaryLastRecord + 9)))
  (.batch 2 (.envelope (.malformed .truncated)))
#guard rejects (read {} {} (binary.slice 0 binarySchemaEnd ++ eos ++ .leaf 1 0)) (.batch 0 .trailingBytes)
#guard rejects (read {} {} (binary.slice 0 binarySecondRecord ++ binary.slice 0 binarySchemaEnd))
  (.batch 1 (.metadata (.metadata (.unsupported (.messageKind 1)))))
#guard rejects (read { batches := 2 } {} binary) (.batch 2 .batchLimit)
#guard rejects (read { bodyBytes := 1 } {} binary) (.batch 0 (.body (.limit .bodyBytes)))
#guard rejects (read {} { rows := 1 } binary) (.batch 0 (.decode (.column .rowLimit)))
#guard rejects (read {} {} (.node binary.len .empty .empty)) .source
#guard rejects (read {} {} eos) .expectedSchema
#guard rejects (read {} {} (schemaOnlyWith BinaryView.Schema.Fixture.primitiveSchema))
  (.schemaMetadata (.metadata (.unsupported (.fieldType 2))))
#guard rejects (read {} {} (schemaOnlyWith BinaryView.Schema.Fixture.bigEndianSchema))
  (.schemaMetadata (.metadata (.unsupported (.endianness 1))))

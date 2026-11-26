module

import Silmaril.Formats.Arrow.BinaryView.Schema.Defs
meta import Silmaril.Formats.Arrow.BinaryView.Schema.Defs
import Silmaril.Formats.Arrow.BinaryView.Schema.Fixture
meta import Silmaril.Formats.Arrow.BinaryView.Schema.Fixture
import Silmaril.Formats.Arrow.BinaryView.Batch.Fixture
meta import Silmaril.Formats.Arrow.BinaryView.Batch.Fixture
import Silmaril.Formats.Arrow.BinaryView.Fixture
meta import Silmaril.Formats.Arrow.BinaryView.Fixture

open Silmaril Silmaril.Formats
open Arrow.BinaryView.Schema Arrow.BinaryView.Schema.Fixture Arrow.BinaryView.Batch.Fixture

#guard match readBatch {} {} binarySchema binaryMetadata binaryBody with
  | .ok ⟨⟨name, nullable, .binary⟩, values⟩ =>
    name == "value" && nullable &&
      values.map (·.map KBytes.toList) == [none, some [255], some "0123456789abcdef".toUTF8.data.toList]
  | _ => false

#guard match readBatch {} {} mixedSchema mixedMetadata mixedBody with
  | .ok ⟨⟨name, nullable, .utf8⟩, values⟩ =>
    name == "value" && nullable &&
      (show List (Option String) from values) == Arrow.BinaryView.Fixture.expected.map some ++ [none]
  | _ => false

#guard match readBatch {} {} requiredSchema requiredMetadata requiredBody with
  | .ok ⟨⟨name, nullable, .utf8⟩, values⟩ =>
    name == "vé" && !nullable && (show List (Option String) from values) == [some "", some "雪雪雪雪雪雪"]
  | _ => false

#guard match readBatch {} {} emptySchema emptyMetadata emptyBody with
  | .ok ⟨⟨name, nullable, .binary⟩, values⟩ => name == "value" && nullable && values.isEmpty
  | _ => false

private def rejectsSchema (bytes : KBytes) (expected : MetadataError) : Bool :=
  match readMessage {} bytes with
  | .error actual => decide (actual = expected)
  | .ok _ => false

#guard rejectsSchema primitiveSchema (.metadata (.unsupported (.fieldType 2)))
#guard rejectsSchema wrongPayloadSchema (.metadata (.unsupported .unknownMetadataSlots))
#guard rejectsSchema bigEndianSchema (.metadata (.unsupported (.endianness 1)))
#guard rejectsSchema badNameSchema (.metadata (.malformed .invalidUtf8))
#guard rejectsSchema noFieldsSchema (.fieldCount 0)
#guard rejectsSchema twoFieldsSchema (.fieldCount 2)
#guard rejectsSchema binaryMetadata (.metadata (.unsupported (.messageKind 3)))
#guard match readMessage { fields := 0 } binarySchema with
  | .error (.metadata (.limit .fields)) => true
  | _ => false

#guard match readBatch {} {} requiredSchema mixedMetadata mixedBody with
  | .error (.record .invalidNode) => true
  | _ => false

#guard match readBatch {} {} mixedSchema binaryMetadata binaryBody with
  | .error (.record (.column .invalidUtf8)) => true
  | _ => false

private def otherReadersReject (schema : KBytes) (tag : Nat) : Bool :=
  match Arrow.readMessage {} schema, Arrow.SchemaReader.readMessage {} schema with
  | .error (.unsupported (.fieldType primitiveTag)), .error (.unsupported (.fieldType normalizedTag)) =>
    primitiveTag == tag && normalizedTag == tag
  | _, _ => false

#guard otherReadersReject binarySchema 23
#guard otherReadersReject mixedSchema 24

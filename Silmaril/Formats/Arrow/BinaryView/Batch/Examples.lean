module

import Silmaril.Formats.Arrow.BinaryView.Batch.Defs
meta import Silmaril.Formats.Arrow.BinaryView.Batch.Defs
import Silmaril.Formats.Arrow.BinaryView.Batch.Fixture
meta import Silmaril.Formats.Arrow.BinaryView.Batch.Fixture
import Silmaril.Formats.Arrow.BinaryView.Fixture
meta import Silmaril.Formats.Arrow.BinaryView.Fixture

open Silmaril Silmaril.Formats
open Silmaril.Formats.Arrow.BinaryView.Batch
open Silmaril.Formats.Arrow.BinaryView.Batch.Fixture

private def expectedMixed : List (Option String) :=
  Arrow.BinaryView.Fixture.expected.map some ++ [none]

#guard (readUtf8 {} {} true mixedMetadata mixedBody).toOption = some expectedMixed
#guard ((readBinary {} {} true binaryMetadata binaryBody).map (·.map (·.map KBytes.toList))).toOption =
  some [none, some [255], some "0123456789abcdef".toUTF8.data.toList]
#guard (readUtf8 {} {} true inlineMetadata inlineBody).toOption =
  some [some "", none, some "α", some "abcdefghijkl"]
#guard ((readBinary {} {} false emptyMetadata emptyBody).map List.length).toOption = some 0
#guard ((Arrow.BinaryView.readBatchMetadata {} 0 emptyMetadata).map (·.dataCount)).toOption = some 0

private def patch (bytes : KBytes) (start width word : Nat) : KBytes :=
  bytes.slice 0 start ++ .leaf width word ++
    bytes.slice (start + width) (bytes.len - (start + width))

private def rejects (result : Except Error (List (Option String))) (expected : Error) : Bool :=
  match result with
  | .error actual => decide (actual = expected)
  | .ok _ => false

#guard rejects (readUtf8 {} {} true (patch mixedMetadata mixedCountSlot 2 0) mixedBody)
  (.metadata (.countCardinality 0))
#guard rejects (readUtf8 {} {} true (patch mixedMetadata mixedCountVector 4 0) mixedBody)
  (.metadata (.countCardinality 0))
#guard rejects (readUtf8 {} {} true (patch mixedMetadata mixedCountVector 4 2) mixedBody)
  (.metadata (.countCardinality 2))
#guard rejects (readUtf8 {} {} true (patch mixedMetadata mixedCountWord 8 (2^63)) mixedBody)
  (.metadata .negativeCount)
#guard rejects (readUtf8 {} { dataBuffers := 1 } true mixedMetadata mixedBody)
  (.metadata .dataBufferLimit)
#guard rejects (readUtf8 {} {} true (patch mixedMetadata mixedCountWord 8 1) mixedBody)
  (.metadata (.descriptorCount 3 4))
#guard rejects (readUtf8 {} {} true (patch mixedMetadata mixedCountWord 8 3) mixedBody)
  (.metadata (.descriptorCount 5 4))
#guard rejects (readUtf8 {} {} true (patch mixedMetadata mixedFirstNode 8 7) mixedBody) .invalidNode
#guard rejects (readUtf8 {} {} false mixedMetadata mixedBody) .invalidNode
#guard rejects (readUtf8 {} {} true mixedMetadata .empty) (.bodyLength mixedBody.len 0)
#guard rejects (readUtf8 { bodyBytes := 1 } {} true mixedMetadata mixedBody) .bodyLimit
#guard rejects (readUtf8 {} {} true mixedMetadata (.node mixedBody.len .empty .empty)) .malformedSource
#guard rejects (readUtf8 {} {} true (patch mixedMetadata mixedViewsDescriptor 8 0) mixedBody)
  .invalidBuffers
#guard rejects (readUtf8 {} {} true (patch mixedMetadata mixedViewsDescriptor 8 9) mixedBody)
  .invalidBuffers
#guard rejects (readUtf8 {} {} true (patch mixedMetadata mixedViewsDescriptor 8 mixedBody.len) mixedBody)
  .invalidBuffers
#guard rejects (readUtf8 {} {} true mixedMetadata (patch mixedBody 60 4 0))
  (.column (.slot 3 .prefixMismatch))

private def rejectsVariadic (metadata : KBytes) : Bool :=
  match Arrow.readMessage {} metadata with
  | .error (.unsupported .variadicBuffers) => true
  | _ => false

#guard [mixedMetadata, binaryMetadata, inlineMetadata, emptyMetadata].all rejectsVariadic
#guard match Arrow.readMessage { fields := 1 } mixedMetadata with
  | .error (.limit .fields) => true
  | _ => false
#guard match Arrow.readMessage {} primitiveMetadata with
  | .ok ⟨.recordBatch _, _⟩ => true
  | _ => false

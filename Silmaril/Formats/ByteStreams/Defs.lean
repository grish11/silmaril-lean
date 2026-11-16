module

public import Silmaril.Formats.Accept.Defs
public import Silmaril.Semantics.Acceptors.Defs

/-!
# Byte chunk streams: the bridge from byte values to incremental acceptors

`Silmaril.Formats.Accept` says which byte values a byte language accepts
(`ByteLang.Accepts`, `b ∈ᴮ L`, through `BytesLike.toBytes`). `Silmaril.Semantics.Acceptors`
says when an incremental acceptor reading chunks through `ChunkView` is correct for a
language. This module connects the two:

* `ChunkView` instances for the remaining byte representations, `KBytes` and
  `Formats.Bytes`, both read through `toBytes`. The `List UInt8`, `Array UInt8` and
  `ByteArray` instances already exist and agree with `toBytes` definitionally
  (`Silmaril.Formats.ByteStreams.Thms`).
* The theorems show that a correct acceptor fed a single value `b` as one chunk answers
  `b ∈ᴮ L`. Fed any chunking, it answers membership of the concatenated bytes.

Nothing here is about Wasm execution. A component bridge must still show that its
`process`/`accepted()` exports implement an `Acceptor`.
-/

@[expose] public section

namespace Silmaril.Formats.ByteStreams

open Silmaril.Formats.Accept

instance instChunkViewKBytes : ChunkView KBytes UInt8 := ⟨toBytes⟩

instance instChunkViewBytes : ChunkView Formats.Bytes UInt8 := ⟨toBytes⟩

end Silmaril.Formats.ByteStreams

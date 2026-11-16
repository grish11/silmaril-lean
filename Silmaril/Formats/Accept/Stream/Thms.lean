module

public import Silmaril.Formats.Accept.Thms
public import Silmaril.Semantics.Streams.Thms
public import Silmaril.Semantics.Acceptors.Defs

/-! # Byte languages as stream languages and chunk views

* **Chunk views** (`Silmaril.ChunkView` of `Silmaril.Semantics.Acceptors`) for the bytes-like
  types that lack one, `KBytes` and `Formats.Bytes`. On every bytes-like type with a chunk
  view, the chunk's symbols are its bytes (`chunkView_toList_*`), so incremental acceptors
  can read chunks of any of these representations.
* **Byte languages as stream languages** (`Silmaril.Streams.Lang UInt8`): a byte language is
  the finite part of `ByteLang.toStream L`, whose infinite part is empty (`finPart_toStream`,
  `not_mem_ωPart_toStream`). The acceptors of `Silmaril.Wasm.Game.Accept` and
  `Silmaril.Wasi.Component.Accept` read finite inputs: a WIT `list<u8>` is finite. So their
  stream languages have no infinite words. Infinite inputs need an incremental interface
  (`Silmaril.Wasi.Accept.StreamCorrect`).
-/

@[expose] public section

namespace Silmaril.Formats.Accept

instance : Silmaril.ChunkView KBytes UInt8 := ⟨KBytes.toList⟩

instance : Silmaril.ChunkView Formats.Bytes UInt8 := ⟨Formats.Bytes.toList⟩

theorem chunkView_toList_list (b : List UInt8) : Silmaril.ChunkView.toList b = toBytes b := rfl

theorem chunkView_toList_array (b : Array UInt8) : Silmaril.ChunkView.toList b = toBytes b := rfl

theorem chunkView_toList_byteArray (b : ByteArray) : Silmaril.ChunkView.toList b = toBytes b :=
  rfl

theorem chunkView_toList_kbytes (b : KBytes) : Silmaril.ChunkView.toList b = toBytes b := rfl

theorem chunkView_toList_bytes (b : Formats.Bytes) : Silmaril.ChunkView.toList b = toBytes b :=
  rfl

namespace ByteLang

/-- A byte language as a stream language of finite words only. -/
def toStream (L : ByteLang) : Silmaril.Streams.Lang UInt8 := Silmaril.Streams.Lang.ofLanguage L

@[simp] theorem finPart_toStream (L : ByteLang) : (toStream L).finPart = L := by
  ext w
  simp [toStream, Silmaril.Streams.Lang.ofLanguage]

/-- No infinite word is in the stream language of a byte language. -/
theorem not_mem_ωPart_toStream (L : ByteLang) (s : Cslib.ωSequence UInt8) :
    s ∉ (toStream L).ωPart := by
  simp [toStream, Silmaril.Streams.Lang.ofLanguage]

theorem toStream_injective : Function.Injective toStream := fun L M h => by
  rw [← finPart_toStream L, ← finPart_toStream M, h]

theorem toStream_mono {L M : ByteLang} (h : L ≤ M) : toStream L ⊆ toStream M := by
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨w, h hw, rfl⟩

end ByteLang

end Silmaril.Formats.Accept

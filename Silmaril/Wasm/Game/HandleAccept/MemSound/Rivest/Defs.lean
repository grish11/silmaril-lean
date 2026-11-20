module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.Pair.Defs
public import Silmaril.Formats.SExp.Rivest
public import Silmaril.Formats.SExp.Family.Defs

/-!
# Byte trees and Rivest canonical trees through linear memory

`Silmaril.Wasm.Game.HandleAccept.MemSound.Pair` proves a module building the list `(a b)` of two
**symbols**. Byte-string trees use the same shape with `blob(ptr, len)`:

* `bpairMod` is `pairMod` with its first import renamed to `sexp.blob : [i32 i32] → [i32]`
  (import `0`; `sexp.sexp` is import `1`, `sexp.accept` import `2`). Its export `run` stores
  `61` at `16`, calls `blob(16, 1)`, stores `62` at `16`, calls `blob(16, 1)`, stores the two
  handles at `0` and `4`, and accepts the handle of `sexp(0, 2)`: the list of the byte strings
  `61` and `62`.
* `bpairTree` is that list over `MemAtom`.

**Families.** Byte strings embed into the memory atoms (`MemAtom`, kind `bytes`):

* `bytesMem'`: `List UInt8` (the atoms of `ByteSExp`);
* `rivestMem`: `Silmaril.Formats.Bytes` (the octet strings of `RivestSExp`, the hint-free data
  model of draft-rivest-sexp-04).

`bytesPair : ByteSExp` and `rivestPair : RivestSExp` are the list of the octet strings `61` and
`62` in the two families; their images under the embeddings are `bpairTree` (`Thms`). The
dotted form of `rivestPair` (`SExp.toSExp2`, the cons-cell model) reads back to it
(`SExp2.toSExp?`), as for every proper tree.

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.Rivest

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Formats
  Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Wasm.Game.HandleAccept.MemSound.Hi
  Silmaril.Wasm.Game.HandleAccept.MemSound.Pair

/-- **The module**: `pairMod` with `blob` for `symbol`. -/
def bpairMod : Module :=
  { pairMod with
    imports := [⟨"sexp", "blob", .func ⟨0⟩⟩, ⟨"sexp", "sexp", .func ⟨0⟩⟩,
      ⟨"sexp", "accept", .func ⟨1⟩⟩] }

/-- The byte string `61`. -/
def blobA : MemAtom := ⟨.bytes, by decide, [0x61]⟩

/-- The byte string `62`. -/
def blobB : MemAtom := ⟨.bytes, by decide, [0x62]⟩

/-- The list of the byte strings `61` and `62`. -/
def bpairTree : SymStrBytesSExp := SExp.ofList [.atom blobA, .atom blobB]

/-- Byte strings (`ByteSExp` atoms) as memory atoms. -/
def bytesMem' (b : List UInt8) : MemAtom := ⟨.bytes, by decide, b⟩

/-- Octet strings (`RivestSExp` atoms) as memory atoms. -/
def rivestMem (b : Bytes) : MemAtom := ⟨.bytes, by decide, b.toList⟩

/-- The list of the octet strings `61` and `62` as a byte tree. -/
def bytesPair : ByteSExp := SExp.ofList [.atom [0x61], .atom [0x62]]

/-- The list of the octet strings `61` and `62` as a Rivest canonical tree. -/
def rivestPair : RivestSExp :=
  SExp.ofList [.atom (Bytes.ofList [0x61]), .atom (Bytes.ofList [0x62])]

end Silmaril.Wasm.Game.HandleAccept.MemSound.Rivest

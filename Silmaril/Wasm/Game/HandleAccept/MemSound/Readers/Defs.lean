module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.Text.Defs

/-!
# Memory-returning readers of blob bytes and symbol text

`Silmaril.Wasm.Game.HandleAccept.MemSound.Text` reads the text of a string atom through a
return pointer. This topic reads the **bytes of a blob** (a byte-string atom, kind `bytes` of
`MemAtom`) the same way:

* `blob_bytes(h, retptr)` (`BlobImports.bytes`): the host writes, canonical-ABI style, the
  `list<u8>` of the bytes of the blob `h` through the return pointer: `(ptr, len)` at `retptr`
  and the `len` bytes at `ptr` (`Text.bytesList`), read off the memory **after** the answer,
  and returns nothing. The decoded event is the read `read (atom h) (atom bytes)` of the blob
  (`blobRead`); a reply the decoder cannot read (out of bounds, no memory) is the ill-typed
  answer `handle 0`, never a correct answer of the `atom` query (`sexpR`). Unlike
  `string_text`, every byte list is an answer (no UTF-8 condition).
* `blobRoles`, `blobTraces`, `blobReaderLang`, `blobContract`: roles, reader traces, reader
  language (reader `sexpR MemAtom`) and reader contract, as for `string_text`.
* `blobMod`: `itemsMod` with `blob_bytes` for `items` (the body of `textMod`: accept `h` only
  when the length word at `[4, 8)` is `2`); `twoByteBlobs`: blobs of two bytes.
* **Symbols** the same way: `symbol_text(h, retptr)` (`SymTextImports`, `symTextRead`) returns
  the UTF-8 text of the symbol `h` (an unreadable or non-UTF-8 reply is `handle 0`);
  `symTextMod` accepts `h` when the text has two bytes; `twoByteSyms`.

New definitions (no source).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.Readers

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Game.Accept
  Silmaril.Wasm.Game.IOAccept Silmaril.Accept.Handle Silmaril.Formats Silmaril.Formats.Api
  Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Game.HandleAccept.MemSound.Items Silmaril.Wasm.Game.HandleAccept.MemSound.Text

/-- The named imports of the blob reader. -/
structure BlobImports where
  bytes : String × String := ("sexp", "blob_bytes")
  accept : String × String := ("sexp", "accept")

/-- The answer of `blob_bytes` read off the reply: the blob of the bytes, or the ill-typed
`handle 0` when the reply cannot be read. -/
def blobAns (w : HostReply) (retptr : BitVec 32) : SxA MemAtom (BitVec 32) :=
  match w.mem.bind fun mem => bytesList mem retptr.toNat with
  | some bs => .atom ⟨.bytes, by decide, bs⟩
  | none => .handle 0

/-- **A read of `blob_bytes(h, retptr)`**, decoded at its answer (returning no values). -/
def blobRead (ix : BlobImports) (o : Callout) (w : HostReply) : Option MemREv :=
  if o.imp = ix.bytes then
    match o.args, w.result with
    | [.num ⟨.int .i32, h⟩, .num ⟨.int .i32, rp⟩], .values [] =>
        some (.read (.atom h) (blobAns w rp))
    | _, _ => none
  else none

/-- A call of `accept(h)`. -/
def blobAccept (ix : BlobImports) (o : Callout) : Option MemREv :=
  if o.imp = ix.accept then (Callout.args1 Callout.i32? o.args).map .accept else none

/-- The roles of the blob reader: accepts at calls, reads at answers. -/
def blobRoles (ix : BlobImports) : Roles Unit MemREv Unit Unit where
  callIn := blobAccept ix
  answerIn := blobRead ix

/-- **The reader traces of a module** through the blob reader. -/
def blobTraces (P : Profile) (Envs : Store Nat → SEnv UImp → Prop) (memIdx : Nat)
    (m : Module) (ix : BlobImports) : Set (List MemREv) :=
  inputsOf (some .enter) '' tagTraces P Envs memIdx m (blobRoles ix)

/-- **The reader language of a module** through the blob reader. -/
def blobReaderLang (P : Profile) (Envs : Store Nat → SEnv UImp → Prop) (memIdx : Nat)
    (m : Module) (ix : BlobImports) (pol : OnBadRead (SxQ (BitVec 32)) (SxA MemAtom (BitVec 32)))
    (oa : OnInvalid) (Rhos : Set (Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp)) :
    Set SymStrBytesSExp :=
  readerLang (sexpR MemAtom (BitVec 32)) pol oa Rhos (blobTraces P Envs memIdx m ix)

/-- **The reader contract** of the blob reader in the fixed environment `ρ`. -/
def blobContract (ix : BlobImports) (ρ : Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp)
    (L : Set SymStrBytesSExp) (reply : UCall Nat → UReply → Prop) : MemContract MemREv where
  pre o := ∀ h, blobAccept ix o = some (.accept h) → ∀ t, ρ h = some t → t ∈ L
  ans x := ∀ q a, x = .read q a →
    (sexpR MemAtom (BitVec 32)).valid ρ q ∧ (sexpR MemAtom (BitVec 32)).ok ρ q a
  reply := reply

/-- **The module**: `itemsMod` with `blob_bytes` for `items`. -/
def blobMod : Module :=
  { itemsMod with
    imports := [⟨"sexp", "blob_bytes", .func ⟨0⟩⟩, ⟨"sexp", "accept", .func ⟨1⟩⟩] }

/-- Blobs of two bytes. -/
def twoByteBlobs : Set SymStrBytesSExp :=
  {x | ∃ bs : List UInt8, bs.length = 2 ∧ x = .atom ⟨.bytes, by decide, bs⟩}

end Silmaril.Wasm.Game.HandleAccept.MemSound.Readers

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.Readers

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Game.Accept
  Silmaril.Wasm.Game.IOAccept Silmaril.Accept.Handle Silmaril.Formats Silmaril.Formats.Api
  Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Game.HandleAccept.MemSound.Items Silmaril.Wasm.Game.HandleAccept.MemSound.Text

/-! ## The symbol text reader -/

/-- The named imports of the symbol text reader. -/
structure SymTextImports where
  text : String × String := ("sexp", "symbol_text")
  accept : String × String := ("sexp", "accept")

/-- The answer of `symbol_text` read off the reply: the symbol of the UTF-8 text, or the
ill-typed `handle 0` when the reply cannot be read. -/
def symTextAns (w : HostReply) (retptr : BitVec 32) : SxA MemAtom (BitVec 32) :=
  match (w.mem.bind fun mem => bytesList mem retptr.toNat).bind utf8? with
  | some s => .atom ⟨.symbol, by decide, s⟩
  | none => .handle 0

/-- **A read of `symbol_text(h, retptr)`**, decoded at its answer (returning no values). -/
def symTextRead (ix : SymTextImports) (o : Callout) (w : HostReply) : Option MemREv :=
  if o.imp = ix.text then
    match o.args, w.result with
    | [.num ⟨.int .i32, h⟩, .num ⟨.int .i32, rp⟩], .values [] =>
        some (.read (.atom h) (symTextAns w rp))
    | _, _ => none
  else none

/-- A call of `accept(h)`. -/
def symTextAccept (ix : SymTextImports) (o : Callout) : Option MemREv :=
  if o.imp = ix.accept then (Callout.args1 Callout.i32? o.args).map .accept else none

/-- The roles of the symbol text reader. -/
def symTextRoles (ix : SymTextImports) : Roles Unit MemREv Unit Unit where
  callIn := symTextAccept ix
  answerIn := symTextRead ix

/-- **The reader traces of a module** through the symbol text reader. -/
def symTextTraces (P : Profile) (Envs : Store Nat → SEnv UImp → Prop) (memIdx : Nat)
    (m : Module) (ix : SymTextImports) : Set (List MemREv) :=
  inputsOf (some .enter) '' tagTraces P Envs memIdx m (symTextRoles ix)

/-- **The reader language of a module** through the symbol text reader. -/
def symTextReaderLang (P : Profile) (Envs : Store Nat → SEnv UImp → Prop) (memIdx : Nat)
    (m : Module) (ix : SymTextImports)
    (pol : OnBadRead (SxQ (BitVec 32)) (SxA MemAtom (BitVec 32))) (oa : OnInvalid)
    (Rhos : Set (Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp)) :
    Set SymStrBytesSExp :=
  readerLang (sexpR MemAtom (BitVec 32)) pol oa Rhos (symTextTraces P Envs memIdx m ix)

/-- **The reader contract** of the symbol text reader in the fixed environment `ρ`. -/
def symTextContract (ix : SymTextImports)
    (ρ : Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp) (L : Set SymStrBytesSExp)
    (reply : UCall Nat → UReply → Prop) : MemContract MemREv where
  pre o := ∀ h, symTextAccept ix o = some (.accept h) → ∀ t, ρ h = some t → t ∈ L
  ans x := ∀ q a, x = .read q a →
    (sexpR MemAtom (BitVec 32)).valid ρ q ∧ (sexpR MemAtom (BitVec 32)).ok ρ q a
  reply := reply

/-- **The module**: `itemsMod` with `symbol_text` for `items`. -/
def symTextMod : Module :=
  { itemsMod with
    imports := [⟨"sexp", "symbol_text", .func ⟨0⟩⟩, ⟨"sexp", "accept", .func ⟨1⟩⟩] }

/-- Symbols of two UTF-8 bytes. -/
def twoByteSyms : Set SymStrBytesSExp :=
  {x | ∃ (bs : List UInt8) (s : String), bs.length = 2 ∧ utf8? bs = some s ∧
    x = .atom ⟨.symbol, by decide, s⟩}

end Silmaril.Wasm.Game.HandleAccept.MemSound.Readers

module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.Readers.Defs
public import Silmaril.Wasm.Game.HandleAccept.MemSound.Live.Defs

/-!
# Checking the children of a list through memory: lists of two symbols or two blobs

`Silmaril.Wasm.Game.HandleAccept.MemSound.Items` reads the children of a list (`items(h,
retptr)`); `Silmaril.Wasm.Game.HandleAccept.MemSound.Readers` reads the text of a symbol
(`symbol_text(h, retptr)`) and the bytes of a blob (`blob_bytes(h, retptr)`). This topic
combines them: a module that checks that a list has two children, **each of which is a symbol**
(or each a blob).

## The roles

* `ListImports`: the names of `items`, of the child reader `child` (`symbol_text` by default,
  `blobImports` for `blob_bytes`) and of `accept`.
* `childRead ix ans`: a read of `child(h, retptr)`, decoded at its answer (no values returned)
  as `read (atom h) (ans w retptr)`; `ans` reads the answer off the reply (`symTextAns`: the
  symbol of the UTF-8 text, `blobAns`: the blob of the bytes; an unreadable reply is the
  ill-typed `handle 0`).
* `listRead ix ans`: the reads of `items` (`itemsRead`, decoded first) and of `child`;
  `listRoles ix ans`: accepts at calls (`readAccept`), reads at answers. `listTraces`,
  `listReaderLang` are the reader traces and the reader language (reader `sexpR MemAtom`); the
  contract is the reader contract of `items` (`readerContract`), whose guarantee concerns only
  `accept` and whose assumption is the correctness of every decoded read.

## The module `listMod ix`

Imports `0 items : [i32 i32] → []`, `1 child : [i32 i32] → []`, `2 accept : [i32] → []`; one
memory of one page; export `check : [i32] → []` with two `i32` locals:

```wat
(func $check (param $h i32) (local $c1 i32) (local $c2 i32)
  (call $items (local.get $h) (i32.const 0))                    ;; (ptr, len) at [0, 8)
  (if (i32.ne (i32.load offset=4 (i32.const 0)) (i32.const 2)) (then (return)))
  (local.set $c1 (i32.load (i32.load (i32.const 0))))           ;; the handles at ptr
  (local.set $c2 (i32.load offset=4 (i32.load (i32.const 0))))
  (call $child (local.get $c1) (i32.const 0))
  (call $child (local.get $c2) (i32.const 0))
  (call $accept (local.get $h)))
```

Both child handles are loaded **before** any further call: a host may rewrite the memory at
every answer, and the loaded handles are those of the memory the `items` decoder read. Each
`child` call only has to be answered correctly (under the trapping read policy a session with
an incorrect or unreadable answer is discarded): a correct `symbol_text` read of `c` says that
`c` denotes a symbol. `symListMod` (with `symbol_text`) accepts only lists of two symbols
(`symPairs`), `blobListMod` (with `blob_bytes`) only lists of two blobs (`blobPairs`).

The admitted hosts are those of `itemsMod` (`itemsReply`: keep the code and the number of
memories, may rewrite memory, return no values).

## A concrete host

`listEnv h₁ h₂`: every call of host code `0` (`items`) or `1` (`child`) writes, in the caller's
memory `0`, the bytes of `Live.itemsBytes h₁ h₂` (the words `8, 2` at `[0, 8)`, then `h₁, h₂` at
`[8, 16)`, little-endian) and returns nothing; other calls return nothing in the caller's store.
Read through the return pointer `0`, these bytes are the `list<i32>` `[h₁, h₂]` for `items`, and
the `list<u8>` of the two low bytes of `h₁` for `symbol_text` and `blob_bytes`.

New definitions (no source).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Game.Accept
  Silmaril.Wasm.Game.IOAccept Silmaril.Accept.Handle Silmaril.Formats Silmaril.Formats.Api
  Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Game.HandleAccept.MemSound.Hi Silmaril.Wasm.Game.HandleAccept.MemSound.Items
  Silmaril.Wasm.Game.HandleAccept.MemSound.Readers

/-! ## The roles -/

/-- The named imports of the list checker. -/
structure ListImports where
  items : String × String := ("sexp", "items")
  child : String × String := ("sexp", "symbol_text")
  accept : String × String := ("sexp", "accept")

/-- The imports of the blob list checker: `blob_bytes` as the child reader. -/
def blobImports : ListImports := { child := ("sexp", "blob_bytes") }

/-- The `items` and `accept` imports, as those of the memory-returning reader. -/
def ListImports.toRead (ix : ListImports) : ReadImports := ⟨ix.items, ix.accept⟩

/-- **A read of `child(h, retptr)`**, decoded at its answer (returning no values); `ans` reads
the answer off the reply. -/
def childRead (ix : ListImports) (ans : HostReply → BitVec 32 → SxA MemAtom (BitVec 32))
    (o : Callout) (w : HostReply) : Option MemREv :=
  if o.imp = ix.child then
    match o.args, w.result with
    | [.num ⟨.int .i32, h⟩, .num ⟨.int .i32, rp⟩], .values [] =>
        some (.read (.atom h) (ans w rp))
    | _, _ => none
  else none

/-- The reads of the list checker: `items` first, then `child`. -/
def listRead (ix : ListImports) (ans : HostReply → BitVec 32 → SxA MemAtom (BitVec 32))
    (o : Callout) (w : HostReply) : Option MemREv :=
  if o.imp = ix.items then itemsRead ix.toRead o w else childRead ix ans o w

/-- The roles of the list checker: accepts at calls, reads of `items` and `child` at answers. -/
def listRoles (ix : ListImports) (ans : HostReply → BitVec 32 → SxA MemAtom (BitVec 32)) :
    Roles Unit MemREv Unit Unit where
  callIn := readAccept ix.toRead
  answerIn := listRead ix ans

/-- **The reader traces of a module** through the list checker's roles. -/
def listTraces (P : Profile) (Envs : Store Nat → SEnv UImp → Prop) (memIdx : Nat)
    (m : Module) (ix : ListImports) (ans : HostReply → BitVec 32 → SxA MemAtom (BitVec 32)) :
    Set (List MemREv) :=
  inputsOf (some .enter) '' tagTraces P Envs memIdx m (listRoles ix ans)

/-- **The reader language of a module** through the list checker's roles. -/
def listReaderLang (P : Profile) (Envs : Store Nat → SEnv UImp → Prop) (memIdx : Nat)
    (m : Module) (ix : ListImports) (ans : HostReply → BitVec 32 → SxA MemAtom (BitVec 32))
    (pol : OnBadRead (SxQ (BitVec 32)) (SxA MemAtom (BitVec 32))) (oa : OnInvalid)
    (Rhos : Set (Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp)) :
    Set SymStrBytesSExp :=
  readerLang (sexpR MemAtom (BitVec 32)) pol oa Rhos (listTraces P Envs memIdx m ix ans)

/-! ## The module -/

/-- The body of `check`. -/
def listBody : List Instr :=
  [.localGet ⟨0⟩, .intConst .i32 0, .call ⟨0⟩,
   .intConst .i32 0, .intLoad .i32 none ⟨0⟩ ⟨0, 4⟩,
   .intConst .i32 2, .intRelOp .i32 .ne, .if_ .empty [.return_] [],
   .intConst .i32 0, .intLoad .i32 none ⟨0⟩ ⟨0, 0⟩, .intLoad .i32 none ⟨0⟩ ⟨0, 0⟩,
   .localSet ⟨1⟩,
   .intConst .i32 0, .intLoad .i32 none ⟨0⟩ ⟨0, 0⟩, .intLoad .i32 none ⟨0⟩ ⟨0, 4⟩,
   .localSet ⟨2⟩,
   .localGet ⟨1⟩, .intConst .i32 0, .call ⟨1⟩,
   .localGet ⟨2⟩, .intConst .i32 0, .call ⟨1⟩,
   .localGet ⟨0⟩, .call ⟨2⟩]

/-- **The module** over the imports `ix`. -/
def listMod (ix : ListImports) : Module where
  types := [tyItems, tyAcc]
  imports := [⟨ix.items.1, ix.items.2, .func ⟨0⟩⟩, ⟨ix.child.1, ix.child.2, .func ⟨0⟩⟩,
    ⟨ix.accept.1, ix.accept.2, .func ⟨1⟩⟩]
  memories := [⟨.i32, ⟨1, none⟩⟩]
  funcs := [⟨⟨1⟩, [.i32, .i32], listBody⟩]
  exports := [⟨"check", .func ⟨3⟩⟩]

/-- **The symbol list checker**: `listMod` with `symbol_text`. -/
def symListMod : Module := listMod {}

/-- **The blob list checker**: `listMod` with `blob_bytes`. -/
def blobListMod : Module := listMod blobImports

/-- **A host of the list checker**: `items` and `child` calls write `itemsBytes h₁ h₂`. -/
def listEnv (h₁ h₂ : BitVec 32) : SEnv UImp where
  S := Unit
  Ans _ e a _ := a =
    ⟨if e.target = 0 ∨ e.target = 1 then Live.itemsStore h₁ h₂ e.store else e.store, .values []⟩
  Div _ _ := False

/-! ## The accepted lists -/

/-- Symbols. -/
def symbols : Set SymStrBytesSExp := {x | ∃ s : String, x = .atom ⟨.symbol, by decide, s⟩}

/-- Blobs (byte strings). -/
def blobs : Set SymStrBytesSExp := {x | ∃ bs : List UInt8, x = .atom ⟨.bytes, by decide, bs⟩}

/-- **Lists of two children in `S`.** -/
def pairsOf (S : Set SymStrBytesSExp) : Set SymStrBytesSExp :=
  {x | ∃ c₁ ∈ S, ∃ c₂ ∈ S, x = SExp.ofList [c₁, c₂]}

/-- **Lists of two symbols.** -/
abbrev symPairs : Set SymStrBytesSExp := pairsOf symbols

/-- **Lists of two blobs.** -/
abbrev blobPairs : Set SymStrBytesSExp := pairsOf blobs

end Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck

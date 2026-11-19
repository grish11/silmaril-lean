module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.Hi.Defs

/-!
# Atom kinds through linear memory: strings, byte strings and keywords

`Silmaril.Wasm.Game.HandleAccept.MemSound.Hi` proves a module writing the symbol `hi` through
`symbol(ptr, len)`. This topic proves the same module shape for every atom import:

* `atomMod name`: `hiMod` with its first import renamed to `sexp.<name> : [i32 i32] → [i32]`
  (import `0`; `accept` is import `1`); its export `run` stores the bytes `68 69` at `[0, 2)` and
  calls `accept(<name>(0, 2))`. `atomMod "symbol"` is `hiMod`.
* **Keywords.** The memory-carrying writer of `Silmaril.Wasm.Game.HandleAccept.Memory` has atoms
  `MemAtom = Atom [.symbol, .string, .bytes]` and no keyword import. `KwAtom` adds keywords
  (`Atom [.symbol, .string, .keyword, .bytes]`, the atoms of `SymStrKwBytesSExp`), and
  `kwWrite` decodes `keyword(ptr, len) -> i32` (the UTF-8 text at `[ptr, ptr + len)`, as a
  keyword atom) besides `symbol`, `string`, `blob` and `sexp`, exactly as `memWrite` does;
  `kwRoles`, `kwTraces` and `kwWriterLang` are the roles, writer traces and writer language.
* `rolesClosed R S reply`: the closed-writes contract for any roles `R` decoding n-ary writes at
  answers: every write the answer to a call decodes to (for every reply) is closed in `S`.

The trees: `strAtom` (the string `"hi"`), `blobAtom` (the byte string `68 69`) over `MemAtom`;
`kwAtom` (the keyword `hi`) over `KwAtom`.

New definitions (no source).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.Atoms

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Game.Accept
  Silmaril.Wasm.Game.IOAccept Silmaril.Accept.Handle Silmaril.Accept.IO Silmaril.Formats
  Silmaril.Formats.Api Silmaril.Wasm.Game.HandleAccept.Memory
  Silmaril.Wasm.Game.HandleAccept.MemSound Silmaril.Wasm.Game.HandleAccept.MemSound.Hi

/-! ## The modules -/

/-- **`hiMod` with the atom import `sexp.<name>`.** -/
def atomMod (name : String) : Module where
  types := [tySym, tyAcc, tyRun]
  imports := [⟨"sexp", name, .func ⟨0⟩⟩, ⟨"sexp", "accept", .func ⟨1⟩⟩]
  memories := [⟨.i32, ⟨1, none⟩⟩]
  funcs := [⟨⟨2⟩, [], hiBody⟩]
  exports := [⟨"run", .func ⟨2⟩⟩]

/-- The string `"hi"`. -/
def strAtom : MemAtom := ⟨.string, by decide, "hi"⟩

/-- The byte string `68 69`. -/
def blobAtom : MemAtom := ⟨.bytes, by decide, [0x68, 0x69]⟩

/-! ## Keywords -/

/-- Atoms with keywords: symbols, strings, keywords and byte strings. -/
abbrev KwAtom := Atom [.symbol, .string, .keyword, .bytes]

/-- Writer events over atoms with keywords. -/
abbrev KwWEv := WEv (SxOp KwAtom) (BitVec 32)

/-- The named imports of the writer with keywords. -/
structure KwImports where
  symbol : String × String := ("sexp", "symbol")
  string : String × String := ("sexp", "string")
  keyword : String × String := ("sexp", "keyword")
  blob : String × String := ("sexp", "blob")
  sexp : String × String := ("sexp", "sexp")
  accept : String × String := ("sexp", "accept")

/-- **The write of an answered call**, with `keyword(ptr, len)`. -/
def kwWrite (ix : KwImports) (o : Callout) (w : HostReply) : Option KwWEv := do
  let r ← replyI32 w
  if o.imp = ix.symbol then
    return .write (.atom ⟨.symbol, by decide, ← utf8? (← o.bytes32)⟩) [] r
  else if o.imp = ix.string then
    return .write (.atom ⟨.string, by decide, ← utf8? (← o.bytes32)⟩) [] r
  else if o.imp = ix.keyword then
    return .write (.atom ⟨.keyword, by decide, ← utf8? (← o.bytes32)⟩) [] r
  else if o.imp = ix.blob then
    return .write (.atom ⟨.bytes, by decide, ← o.bytes32⟩) [] r
  else if o.imp = ix.sexp then
    return .write .list (← handles32 o) r
  else none

/-- A call of `accept(h)`. -/
def kwAccept (ix : KwImports) (o : Callout) : Option KwWEv :=
  if o.imp = ix.accept then (Callout.args1 Callout.i32? o.args).map .accept else none

/-- The roles of the writer with keywords: accepts at calls, writes at answers. -/
def kwRoles (ix : KwImports) : Roles Unit KwWEv Unit Unit where
  callIn := kwAccept ix
  answerIn := kwWrite ix

/-- **The writer traces of a module** through the imports with keywords. -/
def kwTraces (P : Profile) (Envs : Store Nat → SEnv UImp → Prop) (memIdx : Nat) (m : Module)
    (ix : KwImports) : Set (List KwWEv) :=
  inputsOf (some .enter) '' tagTraces P Envs memIdx m (kwRoles ix)

/-- **The writer language of a module** through the imports with keywords. -/
def kwWriterLang (P : Profile) (Envs : Store Nat → SEnv UImp → Prop) (memIdx : Nat)
    (m : Module) (ix : KwImports) (pol : Policy (BitVec 32)) : Set SymStrKwBytesSExp :=
  writerLang (sexpW KwAtom) pol (kwTraces P Envs memIdx m ix)

/-- The keyword `hi`. -/
def kwAtom : KwAtom := ⟨.keyword, by decide, "hi"⟩

/-! ## Closed writes for any roles -/

/-- **The closed-writes contract** for roles `R` decoding n-ary writes at answers. -/
def rolesClosed {α : Type} (R : Roles Unit (WEv (SxOp α) (BitVec 32)) Unit Unit)
    (S : Set (SExp α)) (reply : UCall Nat → UReply → Prop) :
    MemContract (WEv (SxOp α) (BitVec 32)) where
  pre o := ∀ w op args r, R.answerIn o w = some (.write op args r) →
    Writers.WriteClosed (sexpW α) S op args
  reply := reply

end Silmaril.Wasm.Game.HandleAccept.MemSound.Atoms

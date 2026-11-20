module

public import Silmaril.Wasm.Game.HandleAccept.Families.Defs
public import Silmaril.Wasm.Game.HandleAccept.MemSound.Live.Thms
public import Silmaril.Wasm.Game.HandleAccept.MemSound.Atoms.Thms

/-!
# Atom families through linear memory: Wasm-proved examples

The memory-carrying writer imports decode trees over two atom types: `MemAtom` (symbols,
strings, byte strings; `Silmaril.Wasm.Game.HandleAccept.Memory.memWriterLang`) and `KwAtom`
(adding keywords; `Silmaril.Wasm.Game.HandleAccept.MemSound.Atoms.kwWriterLang`); the
memory-returning reader decodes `MemAtom` trees (`MemSound.memReaderLang`). A family whose atoms
embed in one of them is instantiated through the embedding of its atoms (`SExp.map`):

| family | embedding | Wasm-proved example(s) (exact languages) |
| --- | --- | --- |
| symbols-only (`String`) | `symbolsMem` | `hiMod` writes `hi` (`symbols_hiMod`) |
| byte trees (`List UInt8`) | `bytesMem` | `atomMod "blob"` writes `68 69` (`bytes_blobMod`) |
| symbols+strings | `symStrMem` | `atomMod "string"` writes `"hi"` (`symStr_strMod`), and `hi` |
| symbols+bytes | `symBytesMem` | `atomMod "blob"` (`symBytes_blobMod`), and `hi` |
| symbols+strings+bytes | identity | `hiMod`, `atomMod "string"`, `atomMod "blob"`, `pairMod` writes `(a b)` (`symStrBytes_pairMod`); the reader `itemsMod` accepts exactly the two-element lists over all fixed environments (`symStrBytes_itemsMod`) |
| symbols+strings+keywords | `symStrKwMem` | `atomMod "keyword"` writes `:hi` (`symStrKw_kwMod`) |
| symbols+strings+keywords+bytes | identity | `atomMod "keyword"` (`symStrKwBytes_kwMod`) |

Each language equality holds for every profile and every writer policy without undefined
behaviour (`pairMod`: without sentinel), against every host whose replies keep the code, may
rewrite memory and return the import's result shape; the upper bounds are Hoare-logic proofs,
the lower bounds concrete traced sessions (`Silmaril.Wasm.Game.HandleAccept.MemSound.Live`,
`Silmaril.Wasm.Game.HandleAccept.MemSound.Atoms`).

These examples go through the embeddings into `MemAtom`/`KwAtom`. Every family × API pair also
has a module over the family's own atom type, with soundness and a positive run, in
`Silmaril.Wasm.Game.HandleAccept.Families.Matrix` (generic writers over atom tables,
`MemSound.Tab`; generic reader probes, `MemSound.Probe`). Canonical Rivest and byte trees are
also instantiated through `blob` atoms in `Silmaril.Wasm.Game.HandleAccept.MemSound.Rivest`
(`rivest_bpairMod`, `bytes_bpairMod`).

New definitions (no source); the theorems restate `Live` and `Atoms` through the embeddings.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.Families

open Silmaril.Wasm Silmaril.Accept.Handle Silmaril.Formats Silmaril.Formats.Api
  Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Game.HandleAccept.MemSound.Hi Silmaril.Wasm.Game.HandleAccept.MemSound.Pair
  Silmaril.Wasm.Game.HandleAccept.MemSound.Items Silmaril.Wasm.Game.HandleAccept.MemSound.Live
  Silmaril.Wasm.Game.HandleAccept.MemSound.Atoms

/-! ## Embeddings of family atoms -/

/-- Symbols as memory atoms. -/
def symbolsMem (s : Fam.Atom .symbols) : MemAtom := ⟨.symbol, by decide, s⟩

/-- Byte strings as memory atoms. -/
def bytesMem (b : Fam.Atom .bytes) : MemAtom := ⟨.bytes, by decide, b⟩

/-- Symbols and strings as memory atoms. -/
def symStrMem (a : Fam.Atom .symStr) : MemAtom :=
  ⟨a.kind, by have := a.mem; simp only [List.mem_cons, List.not_mem_nil] at this ⊢; tauto,
    a.val⟩

/-- Symbols and byte strings as memory atoms. -/
def symBytesMem (a : Fam.Atom .symBytes) : MemAtom :=
  ⟨a.kind, by have := a.mem; simp only [List.mem_cons, List.not_mem_nil] at this ⊢; tauto,
    a.val⟩

/-- Symbols, strings and keywords as atoms with keywords. -/
def symStrKwMem (a : Fam.Atom .symStrKw) : KwAtom :=
  ⟨a.kind, by have := a.mem; simp only [List.mem_cons, List.not_mem_nil] at this ⊢; tauto,
    a.val⟩

/-! ## The examples -/

/-- **symbols-only**: `hiMod` writes exactly the symbol `hi`. -/
theorem symbols_hiMod (P : Profile) {pol : Policy (BitVec 32)} (ha : pol.onAccept ≠ .ub)
    (hw : pol.onWrite ≠ .ub) : memWriterLang P (ReplyEnvs hiReply) 0 hiMod {} pol =
      {(SExp.atom "hi" : SymbolSExp).map symbolsMem} :=
  hiMod_lang P ha hw

/-- **byte trees**: `atomMod "blob"` writes exactly the byte string `68 69`. -/
theorem bytes_blobMod (P : Profile) {pol : Policy (BitVec 32)} (ha : pol.onAccept ≠ .ub)
    (hw : pol.onWrite ≠ .ub) : memWriterLang P (ReplyEnvs hiReply) 0 (atomMod "blob") {} pol =
      {(SExp.atom [0x68, 0x69] : ByteSExp).map bytesMem} :=
  blob_lang P ha hw

/-- **symbols+strings**: `atomMod "string"` writes exactly the string `"hi"`. -/
theorem symStr_strMod (P : Profile) {pol : Policy (BitVec 32)} (ha : pol.onAccept ≠ .ub)
    (hw : pol.onWrite ≠ .ub) : memWriterLang P (ReplyEnvs hiReply) 0 (atomMod "string") {} pol =
      {(SExp.atom ⟨.string, by decide, "hi"⟩ : SymStrSExp).map symStrMem} :=
  str_lang P ha hw

/-- **symbols+bytes**: `atomMod "blob"` writes exactly the byte string `68 69`. -/
theorem symBytes_blobMod (P : Profile) {pol : Policy (BitVec 32)} (ha : pol.onAccept ≠ .ub)
    (hw : pol.onWrite ≠ .ub) : memWriterLang P (ReplyEnvs hiReply) 0 (atomMod "blob") {} pol =
      {(SExp.atom ⟨.bytes, by decide, [0x68, 0x69]⟩ : SymBytesSExp).map symBytesMem} :=
  blob_lang P ha hw

/-- **symbols+strings+bytes**: `pairMod` writes exactly `(a b)`. -/
theorem symStrBytes_pairMod (P : Profile) {pol : Policy (BitVec 32)}
    (hs : pol.sentinel = none) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    memWriterLang P (ReplyEnvs pairReply) 0 pairMod {} pol = {pairTree} :=
  pairMod_lang P hs hw ha

/-- **symbols+strings+bytes, reader**: over all fixed environments, `itemsMod` accepts exactly
the two-element lists. -/
theorem symStrBytes_itemsMod (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub) :
    memReaderLang P (ReplyEnvs itemsReply) 0 itemsMod {} .trap oa Set.univ = twoL :=
  itemsMod_lang_univ P hoa

/-- **symbols+strings+keywords**: `atomMod "keyword"` writes exactly the keyword `hi`. -/
theorem symStrKw_kwMod (P : Profile) {pol : Policy (BitVec 32)} (ha : pol.onAccept ≠ .ub)
    (hw : pol.onWrite ≠ .ub) : kwWriterLang P (ReplyEnvs hiReply) 0 (atomMod "keyword") {} pol =
      {(SExp.atom ⟨.keyword, by decide, "hi"⟩ : SymStrKwSExp).map symStrKwMem} :=
  kw_lang P ha hw

/-- **symbols+strings+keywords+bytes**: `atomMod "keyword"` writes exactly the keyword `hi`. -/
theorem symStrKwBytes_kwMod (P : Profile) {pol : Policy (BitVec 32)} (ha : pol.onAccept ≠ .ub)
    (hw : pol.onWrite ≠ .ub) : kwWriterLang P (ReplyEnvs hiReply) 0 (atomMod "keyword") {} pol =
      {(SExp.atom kwAtom : SymStrKwBytesSExp)} :=
  kw_lang P ha hw

end Silmaril.Wasm.Game.HandleAccept.Families

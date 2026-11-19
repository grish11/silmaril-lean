module

public import Silmaril.Formats.SExp.Api.Defs
public import Silmaril.Formats.SExp.Rivest
public import Silmaril.Wasm.Game.HandleAccept.Defs
public import Silmaril.Wasm.Game.HandleAccept.Writer.Defs
public import Silmaril.Wasm.Game.HandleAccept.Nary.Defs
public import Silmaril.Wasm.Game.HandleAccept.Ast.Defs
public import Silmaril.Wasm.Game.HandleAccept.Memory.Defs

/-!
# Atom families × handle APIs: named instantiations

An audit of the handle APIs (`Silmaril.Formats.Api`) at every named S-expression family of
`Silmaril.Formats.SExp.Family`, and of the Wasm module languages
(`Silmaril.Wasm.Game.HandleAccept`) that exist for them. Nothing new is constructed: every name
below abbreviates an existing generic definition at a family's atom type.

**Families.** `Fam` enumerates the families and `Fam.Atom` gives their atom types: `String`
(symbols-only, `SymbolSExp`), `List UInt8` (byte trees, `ByteSExp`), `BitVec 64` (word trees,
`WordSExp`), `Atom ks` for the mixed families (`SymStrSExp`, `SymBytesSExp`, `SymStrBytesSExp`,
`SymStrKwSExp`, `SymStrKwBytesSExp`), `Bytes` (Rivest canonical, `RivestSExp`) and `Hinted`
(Rivest with display hints, `HintedSExp`).

**APIs.** At every family, `Fam.naryW` (`sexpW`), `Fam.consW` (`consW`, dotted trees `SExp2`),
`Fam.naryR` (`sexpR`), `Fam.consR` (`consR`), and the AST API `Fam.astW`/`Fam.astR` (`astW`/`astR`
at the S-expression signature `sexpSig`). The per-combination names (`symbolsNaryW`, …,
`hintedAstR`) abbreviate these. Their laws (`Thms`, stated once for every `f : Fam`) are the
API-level ones already proved generically: the n-ary writer is a writer homomorphism into the
AST writer (`Fam.naryW_hom`, `Fam.naryLang_eq_astLang`), writer languages are downward closed
(`Fam.naryLang_downClosed`, `Fam.consLang_downClosed`), readers are monotone, and certified
cons-list readers are sound (`Fam.consListReader_sound`).

**Wasm module languages.** Only two atom types have decoders from instance plays:

* `i64` words (word trees): all five APIs, `wordsNaryWLang` (`Writers.moduleSxWLang`),
  `wordsConsWLang` (`Writers.moduleConsWLang`), `wordsNaryRLang` (`Nary.moduleSExpLang`),
  `wordsConsRLang` (`moduleConsLang`), and the AST languages `wordsAstWLang`/`wordsAstRLang`
  (`Ast.moduleAstWLang`/`moduleAstLang`) at `wordsWitSig`. The AST decoders take a `WitSig`, so
  `wordsWitSig` is the S-expression signature with a `u64` leaf payload: its trees are
  `AST wordsWitSig.toAstSig`, whose leaf payload is `UInt64 × Unit`, not `WordSExp`; no
  equivalence with `sexpSig (BitVec 64)` is proved in the repository.
* symbols, strings and byte strings (`MemAtom = Atom [.symbol, .string, .bytes]`): the n-ary
  writer only, through memory-carrying imports, `symStrBytesNaryWLang` (`Memory.memWriterLang`).

Every other combination has no Wasm decoder: the decoders are fixed to `i64` atoms or to
`MemAtom`, there is no keyword import, no memory-carrying reader or cons writer, and a
symbols-only or byte-tree family is not `MemAtom` (its atoms are `String` / `List UInt8`, not
tagged atoms). These rows say "not instantiable"; the API-level laws still hold.

## The audit

| family | API | Lean name(s) | proved theorem(s) (`Thms`) | status (Wasm-module level) |
| --- | --- | --- | --- | --- |
| symbols-only | n-ary writer | `symbolsNaryW` | `Fam.naryW_hom`, `Fam.naryLang_eq_astLang`, `Fam.naryLang_downClosed` | API laws only; Wasm: not instantiable (decoders fixed to `i64` atoms or `MemAtom`) |
| symbols-only | cons writer | `symbolsConsW` | `Fam.consLang_downClosed` | API laws only; Wasm: not instantiable (decoders fixed to `i64` atoms or `MemAtom`) |
| symbols-only | n-ary reader | `symbolsNaryR` | `Fam.naryR_mono` | API laws only; Wasm: not instantiable (decoders fixed to `i64` atoms or `MemAtom`) |
| symbols-only | cons reader | `symbolsConsR` | `Fam.consR_mono`, `Fam.consListReader_sound` | API laws only; Wasm: not instantiable (decoders fixed to `i64` atoms or `MemAtom`) |
| symbols-only | AST | `symbolsAstW`, `symbolsAstR` | `Fam.naryLang_eq_astLang`, `Fam.astR_mono` | API laws only; Wasm: not instantiable (decoders fixed to `i64` atoms or `MemAtom`) |
| byte trees | n-ary writer | `bytesNaryW` | `Fam.naryW_hom`, `Fam.naryLang_eq_astLang`, `Fam.naryLang_downClosed` | API laws only; Wasm: not instantiable (decoders fixed to `i64` atoms or `MemAtom`) |
| byte trees | cons writer | `bytesConsW` | `Fam.consLang_downClosed` | API laws only; Wasm: not instantiable (decoders fixed to `i64` atoms or `MemAtom`) |
| byte trees | n-ary reader | `bytesNaryR` | `Fam.naryR_mono` | API laws only; Wasm: not instantiable (decoders fixed to `i64` atoms or `MemAtom`) |
| byte trees | cons reader | `bytesConsR` | `Fam.consR_mono`, `Fam.consListReader_sound` | API laws only; Wasm: not instantiable (decoders fixed to `i64` atoms or `MemAtom`) |
| byte trees | AST | `bytesAstW`, `bytesAstR` | `Fam.naryLang_eq_astLang`, `Fam.astR_mono` | API laws only; Wasm: not instantiable (decoders fixed to `i64` atoms or `MemAtom`) |
| word trees | n-ary writer | `wordsNaryW`, `wordsNaryWLang` | `Fam.naryW_hom`, `Fam.naryLang_eq_astLang`, `Fam.naryLang_downClosed`; `wordsNaryWLang_subset_arities`, `wordsNaryWLang_subset_atoms`, `wordsNaryWLang_sxPair_binary` | structural bound only (the module `sxPair` is a proved example of the arity bound) |
| word trees | cons writer | `wordsConsW`, `wordsConsWLang` | `Fam.consLang_downClosed`; `wordsConsWLang_subset_atoms2`, `wordsConsWLang_twoWords`, `wordsConsWLang_twoWordsZ`, `wordsConsWLang_twoWordsM` | proved examples (`twoWords` without sentinel; `twoWordsZ`/`twoWordsM` with sentinel `0`/`-1`: accept only `(x x+1)`) |
| word trees | n-ary reader | `wordsNaryR`, `wordsNaryRLang` | `Fam.naryR_mono`; `wordsNaryRLang_pairCheck`, `wordsNaryRLang_sortedNCheck` | proved example (`pairCheck`, `sortedNCheck`) |
| word trees | cons reader | `wordsConsR`, `wordsConsRLang` | `Fam.consR_mono`, `Fam.consListReader_sound`; `wordsConsRLang_sortedCheck`, `wordsConsRLang_wordsCheck`, `wordsConsRLang_recProperCheck` | proved examples (`wordsCheck`, `sortedCheck`, `recProperCheck`) |
| word trees | AST | `wordsAstW`, `wordsAstR`, `wordsAstWLang`, `wordsAstRLang` (at `wordsWitSig`) | `Fam.naryLang_eq_astLang`, `Fam.astR_mono`; `wordsAstWLang_wellArity` | writer: structural bound only; reader: no theorem beyond the AG rule `Ast.astLang_sound_of_gameSat` |
| symbols+strings | n-ary writer | `symStrNaryW` | `Fam.naryW_hom`, `Fam.naryLang_eq_astLang`, `Fam.naryLang_downClosed` | API laws only; Wasm: not instantiable (decoders fixed to `i64` atoms or `MemAtom`) |
| symbols+strings | cons writer | `symStrConsW` | `Fam.consLang_downClosed` | API laws only; Wasm: not instantiable (decoders fixed to `i64` atoms or `MemAtom`) |
| symbols+strings | n-ary reader | `symStrNaryR` | `Fam.naryR_mono` | API laws only; Wasm: not instantiable (decoders fixed to `i64` atoms or `MemAtom`) |
| symbols+strings | cons reader | `symStrConsR` | `Fam.consR_mono`, `Fam.consListReader_sound` | API laws only; Wasm: not instantiable (decoders fixed to `i64` atoms or `MemAtom`) |
| symbols+strings | AST | `symStrAstW`, `symStrAstR` | `Fam.naryLang_eq_astLang`, `Fam.astR_mono` | API laws only; Wasm: not instantiable (decoders fixed to `i64` atoms or `MemAtom`) |
| symbols+bytes | n-ary writer | `symBytesNaryW` | `Fam.naryW_hom`, `Fam.naryLang_eq_astLang`, `Fam.naryLang_downClosed` | API laws only; Wasm: not instantiable (decoders fixed to `i64` atoms or `MemAtom`) |
| symbols+bytes | cons writer | `symBytesConsW` | `Fam.consLang_downClosed` | API laws only; Wasm: not instantiable (decoders fixed to `i64` atoms or `MemAtom`) |
| symbols+bytes | n-ary reader | `symBytesNaryR` | `Fam.naryR_mono` | API laws only; Wasm: not instantiable (decoders fixed to `i64` atoms or `MemAtom`) |
| symbols+bytes | cons reader | `symBytesConsR` | `Fam.consR_mono`, `Fam.consListReader_sound` | API laws only; Wasm: not instantiable (decoders fixed to `i64` atoms or `MemAtom`) |
| symbols+bytes | AST | `symBytesAstW`, `symBytesAstR` | `Fam.naryLang_eq_astLang`, `Fam.astR_mono` | API laws only; Wasm: not instantiable (decoders fixed to `i64` atoms or `MemAtom`) |
| symbols+strings+bytes | n-ary writer | `symStrBytesNaryW`, `symStrBytesNaryWLang` | `Fam.naryW_hom`, `Fam.naryLang_eq_astLang`, `Fam.naryLang_downClosed`; `symStrBytesNaryWLang_subset_atoms` | structural bound only (memory-carrying imports) |
| symbols+strings+bytes | cons writer | `symStrBytesConsW` | `Fam.consLang_downClosed` | API laws only; Wasm: not instantiable (decoders fixed to `i64` atoms or `MemAtom`) |
| symbols+strings+bytes | n-ary reader | `symStrBytesNaryR` | `Fam.naryR_mono` | API laws only; Wasm: not instantiable (decoders fixed to `i64` atoms or `MemAtom`) |
| symbols+strings+bytes | cons reader | `symStrBytesConsR` | `Fam.consR_mono`, `Fam.consListReader_sound` | API laws only; Wasm: not instantiable (decoders fixed to `i64` atoms or `MemAtom`) |
| symbols+strings+bytes | AST | `symStrBytesAstW`, `symStrBytesAstR` | `Fam.naryLang_eq_astLang`, `Fam.astR_mono` | API laws only; Wasm: not instantiable (decoders fixed to `i64` atoms or `MemAtom`) |
| symbols+strings+keywords | n-ary writer | `symStrKwNaryW` | `Fam.naryW_hom`, `Fam.naryLang_eq_astLang`, `Fam.naryLang_downClosed` | API laws only; Wasm: not instantiable (decoders fixed to `i64` atoms or `MemAtom`) |
| symbols+strings+keywords | cons writer | `symStrKwConsW` | `Fam.consLang_downClosed` | API laws only; Wasm: not instantiable (decoders fixed to `i64` atoms or `MemAtom`) |
| symbols+strings+keywords | n-ary reader | `symStrKwNaryR` | `Fam.naryR_mono` | API laws only; Wasm: not instantiable (decoders fixed to `i64` atoms or `MemAtom`) |
| symbols+strings+keywords | cons reader | `symStrKwConsR` | `Fam.consR_mono`, `Fam.consListReader_sound` | API laws only; Wasm: not instantiable (decoders fixed to `i64` atoms or `MemAtom`) |
| symbols+strings+keywords | AST | `symStrKwAstW`, `symStrKwAstR` | `Fam.naryLang_eq_astLang`, `Fam.astR_mono` | API laws only; Wasm: not instantiable (decoders fixed to `i64` atoms or `MemAtom`) |
| symbols+strings+keywords+bytes | n-ary writer | `symStrKwBytesNaryW` | `Fam.naryW_hom`, `Fam.naryLang_eq_astLang`, `Fam.naryLang_downClosed` | API laws only; Wasm: not instantiable (decoders fixed to `i64` atoms or `MemAtom`) |
| symbols+strings+keywords+bytes | cons writer | `symStrKwBytesConsW` | `Fam.consLang_downClosed` | API laws only; Wasm: not instantiable (decoders fixed to `i64` atoms or `MemAtom`) |
| symbols+strings+keywords+bytes | n-ary reader | `symStrKwBytesNaryR` | `Fam.naryR_mono` | API laws only; Wasm: not instantiable (decoders fixed to `i64` atoms or `MemAtom`) |
| symbols+strings+keywords+bytes | cons reader | `symStrKwBytesConsR` | `Fam.consR_mono`, `Fam.consListReader_sound` | API laws only; Wasm: not instantiable (decoders fixed to `i64` atoms or `MemAtom`) |
| symbols+strings+keywords+bytes | AST | `symStrKwBytesAstW`, `symStrKwBytesAstR` | `Fam.naryLang_eq_astLang`, `Fam.astR_mono` | API laws only; Wasm: not instantiable (decoders fixed to `i64` atoms or `MemAtom`) |
| Rivest canonical | n-ary writer | `rivestNaryW` | `Fam.naryW_hom`, `Fam.naryLang_eq_astLang`, `Fam.naryLang_downClosed` | API laws only; Wasm: not instantiable (decoders fixed to `i64` atoms or `MemAtom`) |
| Rivest canonical | cons writer | `rivestConsW` | `Fam.consLang_downClosed` | API laws only; Wasm: not instantiable (decoders fixed to `i64` atoms or `MemAtom`) |
| Rivest canonical | n-ary reader | `rivestNaryR` | `Fam.naryR_mono` | API laws only; Wasm: not instantiable (decoders fixed to `i64` atoms or `MemAtom`) |
| Rivest canonical | cons reader | `rivestConsR` | `Fam.consR_mono`, `Fam.consListReader_sound` | API laws only; Wasm: not instantiable (decoders fixed to `i64` atoms or `MemAtom`) |
| Rivest canonical | AST | `rivestAstW`, `rivestAstR` | `Fam.naryLang_eq_astLang`, `Fam.astR_mono` | API laws only; Wasm: not instantiable (decoders fixed to `i64` atoms or `MemAtom`) |
| Rivest hinted | n-ary writer | `hintedNaryW` | `Fam.naryW_hom`, `Fam.naryLang_eq_astLang`, `Fam.naryLang_downClosed` | API laws only; Wasm: not instantiable (decoders fixed to `i64` atoms or `MemAtom`) |
| Rivest hinted | cons writer | `hintedConsW` | `Fam.consLang_downClosed` | API laws only; Wasm: not instantiable (decoders fixed to `i64` atoms or `MemAtom`) |
| Rivest hinted | n-ary reader | `hintedNaryR` | `Fam.naryR_mono` | API laws only; Wasm: not instantiable (decoders fixed to `i64` atoms or `MemAtom`) |
| Rivest hinted | cons reader | `hintedConsR` | `Fam.consR_mono`, `Fam.consListReader_sound` | API laws only; Wasm: not instantiable (decoders fixed to `i64` atoms or `MemAtom`) |
| Rivest hinted | AST | `hintedAstW`, `hintedAstR` | `Fam.naryLang_eq_astLang`, `Fam.astR_mono` | API laws only; Wasm: not instantiable (decoders fixed to `i64` atoms or `MemAtom`) |

Family-level codec facts (not API facts): `hinted_toSpki_injective` (hinted trees embed in the
RFC 9804 model), `rivest_printCanonical?_sound` (checked canonical printing parses back).
Outside the families: AST examples exist only at the arithmetic signature
(`Ast.Examples.arithBuild_wellArity`, `Ast.Checkers.addCheck_sound`), and binary trees `Tree2`
have their own writer/reader (`Tree2.moduleTree2WLang`, `Tree2.Checkers.combCheck_sound`).

New definitions (no source).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.Families

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Accept.Handle
  Silmaril.Formats Silmaril.Formats.Api Silmaril.Wasm.Game.HandleAccept

/-! ## Families -/

/-- The named S-expression families. -/
inductive Fam where
  | symbols
  | bytes
  | words
  | symStr
  | symBytes
  | symStrBytes
  | symStrKw
  | symStrKwBytes
  | rivest
  | hinted
  deriving DecidableEq, Repr

/-- The atom type of a family (`Silmaril.Formats.SExp.Family`). -/
abbrev Fam.Atom : Fam → Type
  | .symbols => String
  | .bytes => List UInt8
  | .words => BitVec 64
  | .symStr => Silmaril.Formats.Atom [.symbol, .string]
  | .symBytes => Silmaril.Formats.Atom [.symbol, .bytes]
  | .symStrBytes => Silmaril.Formats.Atom [.symbol, .string, .bytes]
  | .symStrKw => Silmaril.Formats.Atom [.symbol, .string, .keyword]
  | .symStrKwBytes => Silmaril.Formats.Atom [.symbol, .string, .keyword, .bytes]
  | .rivest => Bytes
  | .hinted => Hinted

/-! ## The APIs at a family -/

/-- The n-ary writer. -/
abbrev Fam.naryW (f : Fam) : Writer (SxOp f.Atom) (SExp f.Atom) := Silmaril.Formats.Api.sexpW f.Atom

/-- The cons writer (dotted trees). -/
abbrev Fam.consW (f : Fam) : Writer (ConsOp f.Atom) (SExp2 f.Atom) :=
  Silmaril.Formats.Api.consW f.Atom

/-- The n-ary reader. -/
abbrev Fam.naryR (f : Fam) (H : Type) : Reader (SxQ H) (SxA f.Atom H) H (SExp f.Atom) :=
  Silmaril.Formats.Api.sexpR f.Atom H

/-- The cons reader. -/
abbrev Fam.consR (f : Fam) (H : Type) : Reader (ConsQ H) (ConsA f.Atom H) H (SExp2 f.Atom) :=
  Silmaril.Formats.Api.consR f.Atom H

/-- The AST writer at the S-expression signature. -/
abbrev Fam.astW (f : Fam) : Writer (Σ t, (sexpSig f.Atom).Arg t) (AST (sexpSig f.Atom)) :=
  Silmaril.Formats.Api.astW (sexpSig f.Atom)

/-- The AST reader at the S-expression signature. -/
abbrev Fam.astR (f : Fam) (H : Type) :
    Reader (AstQ H) (AstA (sexpSig f.Atom) H) H (AST (sexpSig f.Atom)) :=
  Silmaril.Formats.Api.astR (sexpSig f.Atom) H

/-! ## Every combination -/

/-! ### symbols-only (`Fam.symbols`) -/

abbrev symbolsNaryW := Fam.naryW .symbols
abbrev symbolsConsW := Fam.consW .symbols
abbrev symbolsNaryR (H : Type) := Fam.naryR .symbols H
abbrev symbolsConsR (H : Type) := Fam.consR .symbols H
abbrev symbolsAstW := Fam.astW .symbols
abbrev symbolsAstR (H : Type) := Fam.astR .symbols H

/-! ### byte trees (`Fam.bytes`) -/

abbrev bytesNaryW := Fam.naryW .bytes
abbrev bytesConsW := Fam.consW .bytes
abbrev bytesNaryR (H : Type) := Fam.naryR .bytes H
abbrev bytesConsR (H : Type) := Fam.consR .bytes H
abbrev bytesAstW := Fam.astW .bytes
abbrev bytesAstR (H : Type) := Fam.astR .bytes H

/-! ### word trees (`Fam.words`) -/

abbrev wordsNaryW := Fam.naryW .words
abbrev wordsConsW := Fam.consW .words
abbrev wordsNaryR (H : Type) := Fam.naryR .words H
abbrev wordsConsR (H : Type) := Fam.consR .words H
abbrev wordsAstW := Fam.astW .words
abbrev wordsAstR (H : Type) := Fam.astR .words H

/-! ### symbols+strings (`Fam.symStr`) -/

abbrev symStrNaryW := Fam.naryW .symStr
abbrev symStrConsW := Fam.consW .symStr
abbrev symStrNaryR (H : Type) := Fam.naryR .symStr H
abbrev symStrConsR (H : Type) := Fam.consR .symStr H
abbrev symStrAstW := Fam.astW .symStr
abbrev symStrAstR (H : Type) := Fam.astR .symStr H

/-! ### symbols+bytes (`Fam.symBytes`) -/

abbrev symBytesNaryW := Fam.naryW .symBytes
abbrev symBytesConsW := Fam.consW .symBytes
abbrev symBytesNaryR (H : Type) := Fam.naryR .symBytes H
abbrev symBytesConsR (H : Type) := Fam.consR .symBytes H
abbrev symBytesAstW := Fam.astW .symBytes
abbrev symBytesAstR (H : Type) := Fam.astR .symBytes H

/-! ### symbols+strings+bytes (`Fam.symStrBytes`) -/

abbrev symStrBytesNaryW := Fam.naryW .symStrBytes
abbrev symStrBytesConsW := Fam.consW .symStrBytes
abbrev symStrBytesNaryR (H : Type) := Fam.naryR .symStrBytes H
abbrev symStrBytesConsR (H : Type) := Fam.consR .symStrBytes H
abbrev symStrBytesAstW := Fam.astW .symStrBytes
abbrev symStrBytesAstR (H : Type) := Fam.astR .symStrBytes H

/-! ### symbols+strings+keywords (`Fam.symStrKw`) -/

abbrev symStrKwNaryW := Fam.naryW .symStrKw
abbrev symStrKwConsW := Fam.consW .symStrKw
abbrev symStrKwNaryR (H : Type) := Fam.naryR .symStrKw H
abbrev symStrKwConsR (H : Type) := Fam.consR .symStrKw H
abbrev symStrKwAstW := Fam.astW .symStrKw
abbrev symStrKwAstR (H : Type) := Fam.astR .symStrKw H

/-! ### symbols+strings+keywords+bytes (`Fam.symStrKwBytes`) -/

abbrev symStrKwBytesNaryW := Fam.naryW .symStrKwBytes
abbrev symStrKwBytesConsW := Fam.consW .symStrKwBytes
abbrev symStrKwBytesNaryR (H : Type) := Fam.naryR .symStrKwBytes H
abbrev symStrKwBytesConsR (H : Type) := Fam.consR .symStrKwBytes H
abbrev symStrKwBytesAstW := Fam.astW .symStrKwBytes
abbrev symStrKwBytesAstR (H : Type) := Fam.astR .symStrKwBytes H

/-! ### Rivest canonical (`Fam.rivest`) -/

abbrev rivestNaryW := Fam.naryW .rivest
abbrev rivestConsW := Fam.consW .rivest
abbrev rivestNaryR (H : Type) := Fam.naryR .rivest H
abbrev rivestConsR (H : Type) := Fam.consR .rivest H
abbrev rivestAstW := Fam.astW .rivest
abbrev rivestAstR (H : Type) := Fam.astR .rivest H

/-! ### Rivest hinted (`Fam.hinted`) -/

abbrev hintedNaryW := Fam.naryW .hinted
abbrev hintedConsW := Fam.consW .hinted
abbrev hintedNaryR (H : Type) := Fam.naryR .hinted H
abbrev hintedConsR (H : Type) := Fam.consR .hinted H
abbrev hintedAstW := Fam.astW .hinted
abbrev hintedAstR (H : Type) := Fam.astR .hinted H

/-! ## Wasm module languages: word trees -/

/-- The n-ary writer language of a module, word trees. -/
noncomputable abbrev wordsNaryWLang (P : Profile) (m : Module) (ix : Writers.SxWImports)
    (pol : Policy (BitVec 32)) : Set WordSExp :=
  Writers.moduleSxWLang P m ix pol

/-- The cons writer language of a module, word trees. -/
noncomputable abbrev wordsConsWLang (P : Profile) (m : Module) (ix : Writers.ConsWImports)
    (pol : Policy (BitVec 32)) : Set (SExp2 (BitVec 64)) :=
  Writers.moduleConsWLang P m ix pol

/-- The n-ary reader language of a module, word trees. -/
noncomputable abbrev wordsNaryRLang (P : Profile) (m : Module) (ix : Nary.SxRImports)
    (pol : OnBadRead (SxQ (BitVec 32)) (SxA (BitVec 64) (BitVec 32))) (oa : OnInvalid)
    (Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) WordSExp)) : Set WordSExp :=
  Nary.moduleSExpLang P m ix pol oa Envs

/-- The cons reader language of a module, word trees. -/
noncomputable abbrev wordsConsRLang (P : Profile) (m : Module) (ix : ConsImports)
    (pol : OnBadRead (ConsQ (BitVec 32)) (ConsA (BitVec 64) (BitVec 32))) (oa : OnInvalid)
    (Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64)))) :
    Set (SExp2 (BitVec 64)) :=
  moduleConsLang P m ix pol oa Envs

/-- **The S-expression signature with a `u64` leaf payload**, as a `WitSig` (the AST decoders
take WIT-typed signatures). Its leaf payload is `PTy.Vals [.u64] = UInt64 × Unit`. -/
def wordsWitSig : WitSig where
  Tag := SxTag
  params
    | .branch => []
    | .leaf => [.u64]
  arity
    | .branch => .star
    | .leaf => .fixed 0

/-- The AST writer language of a module at `wordsWitSig`. -/
noncomputable abbrev wordsAstWLang (P : Profile) (m : Module) (ix : Ast.AstWImports wordsWitSig)
    (pol : Policy (BitVec 32)) : Set (AST wordsWitSig.toAstSig) :=
  Ast.moduleAstWLang P m ix pol

/-- The AST reader language of a module at `wordsWitSig`. -/
noncomputable abbrev wordsAstRLang (P : Profile) (m : Module) (ix : Ast.AstRImports wordsWitSig)
    (pol : OnBadRead (AstQ (BitVec 32)) (AstA wordsWitSig.toAstSig (BitVec 32)))
    (oa : OnInvalid)
    (Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) (AST wordsWitSig.toAstSig))) :
    Set (AST wordsWitSig.toAstSig) :=
  Ast.moduleAstLang P m ix pol oa Envs

/-! ## Wasm module languages: symbols, strings and byte strings -/

/-- The n-ary writer language of a module through memory-carrying imports. -/
abbrev symStrBytesNaryWLang (P : Profile) (Envs : Store Nat → SEnv UImp → Prop) (memIdx : Nat)
    (m : Module)
    (ix : Memory.MemImports) (pol : Policy (BitVec 32)) : Set SymStrBytesSExp :=
  Memory.memWriterLang P Envs memIdx m ix pol

end Silmaril.Wasm.Game.HandleAccept.Families

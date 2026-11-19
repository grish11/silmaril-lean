module

public import Silmaril.Wasm.Game.HandleAccept.Families.Defs
public import Silmaril.Formats.SExp.Api.Thms
public import Silmaril.Formats.SExp.Family.Thms
public import Silmaril.Formats.SExp.Printer
public import Silmaril.Wasm.Game.HandleAccept.Thms
public import Silmaril.Wasm.Game.HandleAccept.Writer.Thms
public import Silmaril.Wasm.Game.HandleAccept.Writer.Builders.Thms
public import Silmaril.Wasm.Game.HandleAccept.Nary.Checkers.Thms
public import Silmaril.Wasm.Game.HandleAccept.Checkers.Thms
public import Silmaril.Wasm.Game.HandleAccept.Checkers.RecProper.Thms
public import Silmaril.Wasm.Game.HandleAccept.Writer.Sentinel.Thms
public import Silmaril.Wasm.Game.HandleAccept.Ast.Thms
public import Silmaril.Wasm.Game.HandleAccept.Memory.Thms

/-!
# Atom families × handle APIs: the strongest proved theorems

Restatements, at the named instantiations of `Defs`, of theorems already proved in the
repository; no new proofs. See the table in `Defs` for the status of each combination.

* **Every family** (`f : Fam`): `Fam.naryW_hom`, `Fam.naryLang_eq_astLang` (the n-ary writer is
  the AST API at `sexpSig`), `Fam.naryLang_downClosed`, `Fam.consLang_downClosed`,
  `Fam.naryR_mono`, `Fam.consR_mono`, `Fam.astR_mono`, `Fam.consListReader_sound`.
* **Family codecs**: `hinted_toSpki_injective`, `rivest_printCanonical?_sound`.
* **Word trees, Wasm modules**: structural bounds `wordsNaryWLang_subset_arities`,
  `wordsNaryWLang_subset_atoms`, `wordsConsWLang_subset_atoms2`, `wordsAstWLang_wellArity`; the
  arity bound of the example `sxPair` (`wordsNaryWLang_sxPair_binary`); proved examples
  `wordsConsWLang_twoWords`, with a failure sentinel `wordsConsWLang_twoWordsZ` (sentinel `0`)
  and `wordsConsWLang_twoWordsM` (sentinel `-1`), `wordsNaryRLang_pairCheck`,
  `wordsNaryRLang_sortedNCheck`, `wordsConsRLang_wordsCheck`, `wordsConsRLang_sortedCheck`,
  `wordsConsRLang_recProperCheck` (nested lists, within the recursively proper lists).
* **Symbols, strings and byte strings, Wasm modules**: the structural bound
  `symStrBytesNaryWLang_subset_atoms` only.

No theorem is stated for the AST reader language `wordsAstRLang`: the repository has only the
assume/guarantee rule `Ast.astLang_sound_of_gameSat` for it, and no module proved at
`wordsWitSig`.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.Families

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Accept.Handle
  Silmaril.Formats Silmaril.Formats.Api Silmaril.Wasm.Game.HandleAccept

/-! ## Every family: API-level laws -/

/-- The n-ary writer is a writer homomorphism into the AST writer. -/
theorem Fam.naryW_hom (f : Fam) : (Fam.naryW f).Hom (Fam.astW f) SxOp.toAST SExp.toAST :=
  sexpW_hom

/-- **The n-ary API is the AST API** at the S-expression signature (no UB). -/
theorem Fam.naryLang_eq_astLang (f : Fam) {H : Type} [DecidableEq H] {pol : Policy H}
    (ha : pol.onAccept ≠ .ub) (hw : pol.onWrite ≠ .ub) (T : Set (List (WEv (SxOp f.Atom) H))) :
    writerLang (Fam.astW f) pol (List.map (WEv.mapOp SxOp.toAST) '' T) =
      SExp.toAST '' writerLang (Fam.naryW f) pol T :=
  sexpLang_eq_astLang ha hw T

/-- n-ary writer languages without `accept_all` are closed under children. -/
theorem Fam.naryLang_downClosed (f : Fam) {H : Type} [DecidableEq H] {pol : Policy H}
    (hw : pol.onWrite ≠ .ub) {T : Set (List (WEv (SxOp f.Atom) H))}
    (hT : ∀ t ∈ T, ∀ e ∈ t, AllOnly e) :
    DownClosed SExp.Child (writerLang (Fam.naryW f) pol T) :=
  sexpLang_all_downClosed hw hT

/-- Cons writer languages without `accept_all` are closed under car and cdr. -/
theorem Fam.consLang_downClosed (f : Fam) {H : Type} [DecidableEq H] {pol : Policy H}
    (hw : pol.onWrite ≠ .ub) {T : Set (List (WEv (ConsOp f.Atom) H))}
    (hT : ∀ t ∈ T, ∀ e ∈ t, AllOnly e) :
    DownClosed SExp2.Child (writerLang (Fam.consW f) pol T) :=
  writerLang_downClosed consW_childRel hw hT

theorem Fam.naryR_mono (f : Fam) (H : Type) : (Fam.naryR f H).Mono :=
  Silmaril.Formats.Api.sexpR_mono

theorem Fam.consR_mono (f : Fam) (H : Type) : (Fam.consR f H).Mono :=
  Silmaril.Formats.Api.consR_mono

theorem Fam.astR_mono (f : Fam) (H : Type) : (Fam.astR f H).Mono := Silmaril.Formats.Api.astR_mono

/-- **Certified cons-list readers are sound** (trapping reads, every environment). -/
theorem Fam.consListReader_sound (f : Fam) {H : Type} {P : List f.Atom → Prop} {oa : OnInvalid}
    (hoa : oa ≠ .ub) {T : Set (List (REv (ConsQ H) (ConsA f.Atom H) H))}
    (hT : Certified (listCert P) T) (Envs : Set (Silmaril.Accept.Handle.Env H (SExp2 f.Atom))) :
    readerLang (Fam.consR f H) .trap oa Envs T ⊆ {x | ∃ as, x = SExp2.ofAtoms as ∧ P as} :=
  listReader_sound hoa hT Envs

/-! ## Family codecs -/

theorem hinted_toSpki_injective : Function.Injective HintedSExp.toSpki :=
  HintedSExp.toSpki_injective

theorem rivest_printCanonical?_sound {value : SExp (Fam.Atom .rivest)} {bytes : Bytes}
    (h : RivestSExp.printCanonical? value = some bytes) :
    RivestSExp.parseCanonical? bytes = some value :=
  RivestSExp.printCanonical?_sound h

/-! ## Word trees: Wasm modules -/

variable {P : Profile} {m : Module}

/-- Structural bound: list arities are those of the list-constructor imports. -/
theorem wordsNaryWLang_subset_arities {ix : Writers.SxWImports} {pol : Policy (BitVec 32)}
    (ha : pol.onAccept ≠ .ub) (hw : pol.onWrite ≠ .ub) :
    wordsNaryWLang P m ix pol ⊆
      {x | Writers.ListArities (Writers.sxArities ix (Verify.instOf m).imports) x} :=
  Writers.moduleSxWLang_subset_arities ha hw

/-- Structural bound: without list-constructor imports, only words. -/
theorem wordsNaryWLang_subset_atoms {ix : Writers.SxWImports} {pol : Policy (BitVec 32)}
    (hl : ∀ j ∈ ix.lists, (Verify.instOf m).imports.length ≤ j) (ha : pol.onAccept ≠ .ub)
    (hw : pol.onWrite ≠ .ub) : wordsNaryWLang P m ix pol ⊆ Writers.atoms :=
  Writers.moduleSxWLang_subset_atoms hl ha hw

/-- The example `sxPair` builds only binary lists (an arity bound, not functional correctness). -/
theorem wordsNaryWLang_sxPair_binary (P : Profile) {pol : Policy (BitVec 32)}
    (ha : pol.onAccept ≠ .ub) (hw : pol.onWrite ≠ .ub) :
    wordsNaryWLang P Writers.Examples.sxPair Writers.Examples.sxPairIx pol ⊆
      {x | Writers.ListArities {2} x} :=
  Writers.Examples.sxPair_binary P ha hw

/-- Structural bound: without `nil` and `cons` imports, only words. -/
theorem wordsConsWLang_subset_atoms2 {ix : Writers.ConsWImports} {pol : Policy (BitVec 32)}
    (hn : (Verify.instOf m).imports.length ≤ ix.nil)
    (hc : (Verify.instOf m).imports.length ≤ ix.cons) (ha : pol.onAccept ≠ .ub)
    (hw : pol.onWrite ≠ .ub) : wordsConsWLang P m ix pol ⊆ Writers.atoms2 :=
  Writers.moduleConsWLang_subset_atoms2 hn hc ha hw

/-- Proved example: `twoWords` accepts only `(x x+1)`. -/
theorem wordsConsWLang_twoWords (P : Profile) {pol : Policy (BitVec 32)}
    (hsen : pol.sentinel = none) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    wordsConsWLang P Writers.Builders.twoWords Writers.Builders.twoIx pol ⊆
      Writers.Builders.twoWordsL :=
  Writers.Builders.twoWords_sound P hsen hw ha

/-- Proved example with the sentinel `0`: `twoWordsZ` accepts only `(x x+1)`. -/
theorem wordsConsWLang_twoWordsZ (P : Profile) {pol : Policy (BitVec 32)}
    (hsen : pol.sentinel = some 0) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    wordsConsWLang P Writers.Sentinel.twoWordsZ Writers.Builders.twoIx pol ⊆
      Writers.Builders.twoWordsL :=
  Writers.Sentinel.twoWordsZ_sound P hsen hw ha

/-- Proved example with the sentinel `-1`: `twoWordsM` accepts only `(x x+1)`. -/
theorem wordsConsWLang_twoWordsM (P : Profile) {pol : Policy (BitVec 32)}
    (hsen : pol.sentinel = some (-1)) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    wordsConsWLang P Writers.Sentinel.twoWordsM Writers.Builders.twoIx pol ⊆
      Writers.Builders.twoWordsL :=
  Writers.Sentinel.twoWordsM_sound P hsen hw ha

/-- Proved example: `pairCheck` accepts only two-element lists. -/
theorem wordsNaryRLang_pairCheck (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) WordSExp)) :
    wordsNaryRLang P Nary.Examples.pairCheck Nary.Examples.pairIx .trap oa Envs ⊆
      Nary.Examples.pairL :=
  Nary.Checkers.pairCheck_sound P hoa Envs

/-- Proved example: `sortedNCheck` accepts only sorted lists of words. -/
theorem wordsNaryRLang_sortedNCheck (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) WordSExp)) :
    wordsNaryRLang P Nary.Checkers.sortedNCheck Nary.Examples.pairIx .trap oa Envs ⊆
      Nary.Checkers.sortedNL :=
  Nary.Checkers.sortedNCheck_sound P hoa Envs

/-- Proved example: `wordsCheck` accepts only proper lists of words. -/
theorem wordsConsRLang_wordsCheck (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64)))) :
    wordsConsRLang P Checkers.wordsCheck Checkers.consIx .trap oa Envs ⊆ Checkers.wordsL :=
  Checkers.wordsCheck_sound P hoa Envs

/-- Proved example: `sortedCheck` accepts only sorted proper lists of words. -/
theorem wordsConsRLang_sortedCheck (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64)))) :
    wordsConsRLang P Checkers.sortedCheck Checkers.consIx .trap oa Envs ⊆ Checkers.sortedL :=
  Checkers.sortedCheck_sound P hoa Envs

/-- Proved example: `recProperCheck` accepts only nested lists (`nestL ⊆ recProperL`). -/
theorem wordsConsRLang_recProperCheck (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64)))) :
    wordsConsRLang P Checkers.recProperCheck Checkers.consIx .trap oa Envs ⊆ Checkers.nestL :=
  Checkers.recProperCheck_sound P hoa Envs

/-- Structural bound: AST writer modules accept only well-arity trees. -/
theorem wordsAstWLang_wellArity {ix : Ast.AstWImports wordsWitSig} {pol : Policy (BitVec 32)}
    (ha : pol.onAccept ≠ .ub) (hw : pol.onWrite ≠ .ub) :
    wordsAstWLang P m ix pol ⊆ {x | AST.WellArity x} :=
  Ast.moduleAstWLang_wellArity ha hw

/-! ## Symbols, strings and byte strings: Wasm modules -/

/-- Structural bound: without the `sexp` import, only atoms. -/
theorem symStrBytesNaryWLang_subset_atoms {Envs : Store Nat → SEnv UImp → Prop} {memIdx : Nat}
    {ix : Memory.MemImports} {pol : Policy (BitVec 32)}
    (hs : ∀ i ∈ m.imports, (i.moduleName, i.name) ≠ ix.sexp) (ha : pol.onAccept ≠ .ub)
    (hw : pol.onWrite ≠ .ub) :
    symStrBytesNaryWLang P Envs memIdx m ix pol ⊆ {x | ∃ a, x = .atom a} :=
  Memory.memWriterLang_subset_atoms hs ha hw

end Silmaril.Wasm.Game.HandleAccept.Families

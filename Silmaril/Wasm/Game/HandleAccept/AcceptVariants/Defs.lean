module

public import Silmaril.Wasm.Game.HandleAccept.Writer.Defs

/-!
# Accept variants of the cons writer API: `accept_err`, `accept_all`, `accept_batch`

The cons writer API of `Silmaril.Wasm.Game.HandleAccept.Writers` (`nil`, `cons`, `word`) with
every accept variant of `Silmaril.Accept.Handle.WEv` as an optional import (`ConsXImports`):

* `accept : [i32] → []`: `.accept h`, observed when asked;
* `accept_err : [i32] → [i32]`, the **error-return accept**: `.acceptErr h ok`, observed when
  *answered*, with `ok` the status `0` (success; any other code is an error). Under the writer
  semantics a valid handle answers `ok = true` and accepts its tree; an invalid one answers
  `ok = false` and accepts nothing (`WStep.acceptErrOk`, `WStep.acceptErrBad`);
* `accept_all : [] → []`: `.acceptAll` (every tree constructed so far), observed when asked;
* `accept_batch : [i32] → []`: `.acceptBatch keep` with `keep` the argument `≠ 0` (accept or
  drop the trees constructed since the previous batch), observed when asked.

`moduleConsXLang P m ix pol` is the writer language (store semantics) of a module's decoded
traces.

**Assume/guarantee specification** (`storeISpec W s dAsk dAns ρ L C`) in a fixed environment
`ρ`: answered writes return the sentinel `s` or a handle denoting in `ρ` the tree built in `ρ`
(`post`); `accept(h)` and `accept_err(h)` name handles whose meaning in `ρ`, if any, is in `L`,
every constructor call builds in `ρ` (if anything) a tree of `C`, the bound on the
**constructed set**, and a bulk accept (`accept_all()`, `accept_batch(keep ≠ 0)`) is only
called when `C ⊆ L` (`pre`). The store bridge (`Thms`) then bounds the language by `L`.

New definitions (no source).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.AcceptVariants

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game
  Silmaril.Accept.Handle Silmaril.Formats Silmaril.Formats.Api
open Silmaril.Wasm.Game.HandleAccept Silmaril.Wasm.Game.HandleAccept.Writers
open Silmaril.Wasm.Logic.Strategy (ISpec)

/-- Import indices of the cons writer API with accept variants. -/
structure ConsXImports where
  nil : Nat
  cons : Nat
  word : Nat
  accept : Option Nat := none
  acceptErr : Option Nat := none
  acceptAll : Option Nat := none
  acceptBatch : Option Nat := none

variable {ts : List FnType}

/-- Calls of `accept(h)`, `accept_all()` and `accept_batch(keep)`. -/
def consXDecAsk (ix : ConsXImports) (e : (ifaceSig ts).Op) : Option ConsWEv :=
  if ix.accept = some e.1.val then (i32Arg e.2.1).map .accept
  else if ix.acceptAll = some e.1.val then (if e.2.1 = [] then some .acceptAll else none)
  else if ix.acceptBatch = some e.1.val then (i32Arg e.2.1).map fun b => .acceptBatch (b != 0)
  else none

/-- Answered calls of `accept_err(h)` (status `0`: success) and of the writes `nil()`,
`cons(a, b)`, `word(x)` returning a handle. -/
def consXDecAns (ix : ConsXImports) (e : (ifaceSig ts).Op) (v : (ifaceSig ts).Ar e) :
    Option ConsWEv := do
  let r ← retI32 v
  if ix.acceptErr = some e.1.val then return .acceptErr (← i32Arg e.2.1) (r == 0)
  else if e.1.val = ix.word then return .write (.atom (← i64Arg e.2.1)) [] r
  else if e.1.val = ix.nil then
    if e.2.1 = [] then return .write .nil [] r else none
  else if e.1.val = ix.cons then return .write .cons (← i32Pair e.2.1) r
  else none

/-- **The writer language of a module** through the cons API with accept variants (store
semantics). -/
noncomputable def moduleConsXLang (P : Profile) (m : Module) (ix : ConsXImports)
    (pol : Policy (BitVec 32)) : Set (SExp2 (BitVec 64)) :=
  writerLang (consW (BitVec 64)) pol (moduleTraces P m (consXDecAsk ix) (consXDecAns ix))

/-- **The assume/guarantee specification of a writer with accept variants** in the fixed
environment `ρ`, for the sentinel `s`, accepted language `L` and constructed-set bound `C`. -/
def storeISpec {E : Sig.{0}} {Op X : Type} (W : Writer Op X) (s : Option (BitVec 32))
    (dAsk : E.Op → Option (WEv Op (BitVec 32)))
    (dAns : (e : E.Op) → E.Ar e → Option (WEv Op (BitVec 32)))
    (ρ : Env (BitVec 32) X) (L C : Set X) : ISpec E where
  pre e := (∀ h, dAsk e = some (.accept h) → ∀ t, ρ h = some t → t ∈ L) ∧
    (∀ v h b, dAns e v = some (.acceptErr h b) → ∀ t, ρ h = some t → t ∈ L) ∧
    (∀ v op args r, dAns e v = some (.write op args r) → ∀ t, W.built ρ op args = some t →
      t ∈ C) ∧
    (dAsk e = some .acceptAll ∨ dAsk e = some (.acceptBatch true) → C ⊆ L)
  post e v := ∀ op args r, dAns e v = some (.write op args r) →
    s = some r ∨ ∃ t, W.built ρ op args = some t ∧ ρ r = some t

end Silmaril.Wasm.Game.HandleAccept.AcceptVariants

namespace Silmaril.Wasm.Game.HandleAccept.AcceptVariants

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Formats

/-! ## Example modules

Every module below has the same seven imports (`variantsIx`): `0 nil : [] → [i32]`,
`1 cons : [i32 i32] → [i32]`, `2 word : [i64] → [i32]`, `3 accept : [i32] → []`,
`4 accept_err : [i32] → [i32]`, `5 accept_all : [] → []`, `6 accept_batch : [i32] → []`, and
one export `run : [i64] → []`. -/

/-- `[] → [i32]`. -/
def tyNil : RecType := ⟨[⟨true, [], .func ⟨[], [.i32]⟩⟩]⟩
/-- `[i32 i32] → [i32]`. -/
def tyCons : RecType := ⟨[⟨true, [], .func ⟨[.i32, .i32], [.i32]⟩⟩]⟩
/-- `[i64] → [i32]`. -/
def tyWord : RecType := ⟨[⟨true, [], .func ⟨[.i64], [.i32]⟩⟩]⟩
/-- `[i32] → []`. -/
def tyA : RecType := ⟨[⟨true, [], .func ⟨[.i32], []⟩⟩]⟩
/-- `[i32] → [i32]`. -/
def tyQ : RecType := ⟨[⟨true, [], .func ⟨[.i32], [.i32]⟩⟩]⟩
/-- `[] → []`. -/
def tyUnit : RecType := ⟨[⟨true, [], .func ⟨[], []⟩⟩]⟩
/-- `[i64] → []`. -/
def tyRun : RecType := ⟨[⟨true, [], .func ⟨[.i64], []⟩⟩]⟩

/-- A module with the seven imports and the export `run` of body `body`. -/
def variantsModule (body : List Instr) : Module where
  types := [tyNil, tyCons, tyWord, tyA, tyQ, tyUnit, tyRun]
  imports := [⟨"sexp", "nil", .func ⟨0⟩⟩, ⟨"sexp", "cons", .func ⟨1⟩⟩,
    ⟨"sexp", "word", .func ⟨2⟩⟩, ⟨"sexp", "accept", .func ⟨3⟩⟩,
    ⟨"sexp", "accept_err", .func ⟨4⟩⟩, ⟨"sexp", "accept_all", .func ⟨5⟩⟩,
    ⟨"sexp", "accept_batch", .func ⟨3⟩⟩]
  funcs := [⟨⟨6⟩, [], body⟩]
  exports := [⟨"run", .func ⟨7⟩⟩]

/-- The import indices. -/
def variantsIx : ConsXImports := ⟨0, 1, 2, some 3, some 4, some 5, some 6⟩

/-- `run(x)`: `st = accept_err(word(x))`; on an error status, `accept(nil())`. -/
def errBody : List Instr :=
  [.localGet ⟨0⟩, .call ⟨2⟩, .call ⟨4⟩, .if_ .empty [.call ⟨0⟩, .call ⟨3⟩] []]

/-- **Error-return accept with a fallback**: tries to accept the word `x`; if `accept_err`
reports an error (for instance because `word` failed and returned the sentinel), accepts
`nil` instead. -/
def errAccept : Module := variantsModule errBody

/-- Words and `nil`: the language of `errAccept`. -/
def errL : Set (SExp2 (BitVec 64)) := {t | (∃ w, t = .atom w) ∨ t = .nil}

/-- `run(x)`: build `word(x)`, `nil()` and `cons(word(x), nil())`, then `accept_all()`. -/
def allBody : List Instr :=
  [.localGet ⟨0⟩, .call ⟨2⟩, .call ⟨0⟩, .call ⟨1⟩, .drop, .call ⟨5⟩]

/-- **Accept everything constructed**: two trees, `(x)` and its parts. -/
def allAccept : Module := variantsModule allBody

/-- The constructed set of `allAccept`: words, `nil` and one-element lists of words. -/
def allL : Set (SExp2 (BitVec 64)) :=
  {t | (∃ w, t = .atom w) ∨ t = .nil ∨ ∃ w, t = .cons (.atom w) .nil}

/-- `run(x)`: `a = word(x)`; `accept_batch(0)` (drop); `cons(a, nil())`; `accept_batch(1)`
(keep). -/
def batchBody : List Instr :=
  [.localGet ⟨0⟩, .call ⟨2⟩, .intConst .i32 0, .call ⟨6⟩, .call ⟨0⟩, .call ⟨1⟩, .drop,
   .intConst .i32 1, .call ⟨6⟩]

/-- **Batches**: drop the batch holding the word, keep the batch holding `nil` and `(x)`. -/
def batchAccept : Module := variantsModule batchBody

/-- The store invariant of a module. -/
def variantsInv (m : Module) (s : Store Nat) : Prop := s.funcs = (Verify.instOf m).store.funcs

end Silmaril.Wasm.Game.HandleAccept.AcceptVariants

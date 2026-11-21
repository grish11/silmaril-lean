module

public import Silmaril.Wasm.Game.HandleAccept.Writer.Thms

/-!
# Writer modules: examples

Three Core 3.0 modules (Lean AST literals) building trees through writer imports, each
exporting `run : [i64] → []` (the environment may call it any number of times):

* `wordAccept` (imports `0 word : [i64] → [i32]`, `1 accept : [i32] → []`): accepts `word(x)`.
  It has no `nil`/`cons` import, so its cons-writer language is included in the words for every
  profile and every policy without UB (`wordAccept_atoms`), with no Hoare-logic obligation.
* `consPair` (imports `0 nil`, `1 cons`, `2 word`, `3 accept`): accepts `cons(word(x), nil())`,
  the one-element list `(x)`.
* `sxPair` (imports `0 word`, `1 list2 : [i32 i32] → [i32]`, `2 accept`): accepts
  `list2(word(x), word(x))`. Its only list constructor has two parameters, so every list node of
  every tree it accepts through the n-ary API has two children (`sxPair_binary`).

All three validate and instantiate (`decide +kernel` on `Silmaril.Wasm.Verify.instance?`).
The languages are upper bounds; non-vacuity (a replayed play reaching `accept`) is not shown here.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.Writers.Examples

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Formats
  Silmaril.Accept.Handle

/-- `[i64] → [i32]`. -/
def tyWord : RecType := ⟨[⟨true, [], .func ⟨[.i64], [.i32]⟩⟩]⟩
/-- `[i32] → []`. -/
def tyA : RecType := ⟨[⟨true, [], .func ⟨[.i32], []⟩⟩]⟩
/-- `[i64] → []`. -/
def tyRun : RecType := ⟨[⟨true, [], .func ⟨[.i64], []⟩⟩]⟩
/-- `[] → [i32]`. -/
def tyNil : RecType := ⟨[⟨true, [], .func ⟨[], [.i32]⟩⟩]⟩
/-- `[i32 i32] → [i32]`. -/
def tyCons : RecType := ⟨[⟨true, [], .func ⟨[.i32, .i32], [.i32]⟩⟩]⟩

/-- **Accept a word**: `accept(word(x))`. -/
def wordAccept : Module where
  types := [tyWord, tyA, tyRun]
  imports := [⟨"sexp", "word", .func ⟨0⟩⟩, ⟨"sexp", "accept", .func ⟨1⟩⟩]
  funcs := [⟨⟨2⟩, [], [.localGet ⟨0⟩, .call ⟨0⟩, .call ⟨1⟩]⟩]
  exports := [⟨"run", .func ⟨2⟩⟩]

/-- **Accept a one-element dotted list**: `accept(cons(word(x), nil()))`. -/
def consPair : Module where
  types := [tyNil, tyCons, tyWord, tyA, tyRun]
  imports := [⟨"sexp", "nil", .func ⟨0⟩⟩, ⟨"sexp", "cons", .func ⟨1⟩⟩,
    ⟨"sexp", "word", .func ⟨2⟩⟩, ⟨"sexp", "accept", .func ⟨3⟩⟩]
  funcs := [⟨⟨4⟩, [], [.localGet ⟨0⟩, .call ⟨2⟩, .call ⟨0⟩, .call ⟨1⟩, .call ⟨3⟩]⟩]
  exports := [⟨"run", .func ⟨4⟩⟩]

/-- **Accept a pair of words**: `accept(list2(word(x), word(x)))`. -/
def sxPair : Module where
  types := [tyWord, tyCons, tyA, tyRun]
  imports := [⟨"sexp", "word", .func ⟨0⟩⟩, ⟨"sexp", "list2", .func ⟨1⟩⟩,
    ⟨"sexp", "accept", .func ⟨2⟩⟩]
  funcs := [⟨⟨3⟩, [], [.localGet ⟨0⟩, .call ⟨0⟩, .localGet ⟨0⟩, .call ⟨0⟩, .call ⟨1⟩, .call ⟨2⟩]⟩]
  exports := [⟨"run", .func ⟨3⟩⟩]

/-- Import indices of `wordAccept` as a cons writer (no `nil`, no `cons`: indices `2`, `3` are
out of range). -/
def wordAcceptIx : ConsWImports := ⟨2, 3, 0, 1, none⟩
/-- Import indices of `consPair`. -/
def consPairIx : ConsWImports := ⟨0, 1, 2, 3, none⟩
/-- Import indices of `sxPair`. -/
def sxPairIx : SxWImports := ⟨0, [1], 2, none⟩

theorem wordAccept_instance : (Verify.instance? wordAccept).isSome = true := by decide +kernel
theorem consPair_instance : (Verify.instance? consPair).isSome = true := by decide +kernel
theorem sxPair_instance : (Verify.instance? sxPair).isSome = true := by decide +kernel

theorem wordAccept_imports : (Verify.instOf wordAccept).imports =
    [⟨[.num (.int .i64)], [.num (.int .i32)]⟩, ⟨[.num (.int .i32)], []⟩] := by decide +kernel

theorem sxPair_imports : (Verify.instOf sxPair).imports =
    [⟨[.num (.int .i64)], [.num (.int .i32)]⟩,
     ⟨[.num (.int .i32), .num (.int .i32)], [.num (.int .i32)]⟩, ⟨[.num (.int .i32)], []⟩] := by
  decide +kernel

/-- **`wordAccept` accepts only words**, for every profile and every policy without UB. -/
theorem wordAccept_atoms (P : Profile) {pol : Policy (BitVec 32)} (ha : pol.onAccept ≠ .ub)
    (hw : pol.onWrite ≠ .ub) : moduleConsWLang P wordAccept wordAcceptIx pol ⊆ atoms2 :=
  moduleConsWLang_subset_atoms2 (by rw [wordAccept_imports]; decide)
    (by rw [wordAccept_imports]; decide) ha hw

theorem listArities_mono {α : Type} {K K' : Set Nat} (hK : K ⊆ K') :
    ∀ {x : SExp α}, ListArities K x → ListArities K' x
  | .atom _, _ => trivial
  | .list _ _, ⟨hn, hc⟩ => ⟨hK hn, fun i => listArities_mono hK (hc i)⟩

theorem sxPair_arities : sxArities sxPairIx (Verify.instOf sxPair).imports ⊆ {2} := by
  rw [sxPair_imports]
  rintro n ⟨j, hj, hlt, rfl⟩
  cases List.mem_singleton.1 hj
  rfl

/-- **`sxPair` builds only binary lists**: every list node of every tree it accepts through the
n-ary API has exactly two children (every profile, every policy without UB). -/
theorem sxPair_binary (P : Profile) {pol : Policy (BitVec 32)} (ha : pol.onAccept ≠ .ub)
    (hw : pol.onWrite ≠ .ub) :
    moduleSxWLang P sxPair sxPairIx pol ⊆ {x | ListArities {2} x} :=
  fun _ hx => listArities_mono sxPair_arities (moduleSxWLang_subset_arities ha hw hx)

end Silmaril.Wasm.Game.HandleAccept.Writers.Examples

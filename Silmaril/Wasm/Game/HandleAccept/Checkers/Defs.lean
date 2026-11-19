module

public import Silmaril.Wasm.Game.HandleAccept.Defs

/-!
# Executable reader checkers over the cons API

Three Core 3.0 modules (Lean AST literals) that inspect a dotted S-expression through the cons
reader API and call `accept(h)` on the handle `h` they were given when it passes. Imports, by
index (`consIx`): `0 kind : [i32] → [i32]` (`0` nil, `1` atom, `2` cons), `1 car`,
`2 cdr : [i32] → [i32]`, `3 word : [i32] → [i64]`, `4 accept : [i32] → []`. Each exports
`check : [i32] → []`; the environment may call it any number of times with any handles
(handles to inspect are chosen by the module from there: `car`/`cdr` results).

* `properCheck`: follows `cdr` from `h` while `kind` answers cons; accepts `h` on nil, returns
  otherwise. Language `properL`: **spine-proper** lists (`SpineProperList`): a `nil`-terminated
  `cdr` spine whose elements are arbitrary trees, dotted pairs included. This is the ordinary
  cons-cell meaning of a proper list; it is weaker than `SExp2.ProperList` (recursively proper:
  every element is itself an atom or a recursively proper list), whose language is
  `recProperL`. `properCheck` does not inspect elements, so it does not check recursive
  properness.
* `wordsCheck`: additionally requires every element (`car`) to be an atom, i.e. a word.
  Language `wordsL`: proper lists of `i64` words, `SExp2.ofAtoms ws`.
* `sortedCheck`: additionally reads each word and requires them non-decreasing in the
  **signed** `i64` order (`i64.le_s`, `BitVec.sle`). Language `sortedL ⊆ wordsL`.

Words are `i64` payloads (`BitVec 64`), handles `i32` (`BitVec 32`): a handle is an opaque
32-bit name (its signedness is irrelevant), while sorting compares the 64-bit payloads as signed
integers; an unsigned order would be `BitVec.ule`/`i64.le_u`.

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Checkers

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Formats

/-- `[i32] → [i32]`. -/
def tyQ : RecType := ⟨[⟨true, [], .func ⟨[.i32], [.i32]⟩⟩]⟩
/-- `[i32] → [i64]`. -/
def tyW : RecType := ⟨[⟨true, [], .func ⟨[.i32], [.i64]⟩⟩]⟩
/-- `[i32] → []`. -/
def tyA : RecType := ⟨[⟨true, [], .func ⟨[.i32], []⟩⟩]⟩

/-- The cons reader imports. -/
def consImports : List Import :=
  [⟨"sexp", "kind", .func ⟨0⟩⟩, ⟨"sexp", "car", .func ⟨0⟩⟩, ⟨"sexp", "cdr", .func ⟨0⟩⟩,
   ⟨"sexp", "word", .func ⟨1⟩⟩, ⟨"sexp", "accept", .func ⟨2⟩⟩]

/-- Their indices. -/
def consIx : ConsImports := ⟨0, 1, 2, 3, 4⟩

/-- `kind(cur)` into local 2; accept the argument on nil; return unless cons. -/
def stepHead : List Instr :=
  [.localGet ⟨1⟩, .call ⟨0⟩, .localSet ⟨2⟩,
   .localGet ⟨2⟩, .intTestOp .i32 .eqz, .if_ .empty [.localGet ⟨0⟩, .call ⟨4⟩, .return_] [],
   .localGet ⟨2⟩, .intConst .i32 2, .intRelOp .i32 .ne, .if_ .empty [.return_] []]

/-- `cur := cdr(cur)`, next iteration. -/
def stepTail : List Instr := [.localGet ⟨1⟩, .call ⟨2⟩, .localSet ⟨1⟩, .br ⟨0⟩]

/-- The element (`car(cur)`, into local 3) must be an atom. -/
def elemAtom : List Instr :=
  [.localGet ⟨1⟩, .call ⟨1⟩, .localSet ⟨3⟩,
   .localGet ⟨3⟩, .call ⟨0⟩, .intConst .i32 1, .intRelOp .i32 .ne, .if_ .empty [.return_] []]

/-- The word of the element (local 4, an `i64`) is at least the previous one (local 5) unless
it is the first (local 6 clear); then it becomes the previous one. -/
def elemSorted : List Instr :=
  [.localGet ⟨3⟩, .call ⟨3⟩, .localSet ⟨4⟩,
   .localGet ⟨6⟩,
   .if_ .empty [.localGet ⟨5⟩, .localGet ⟨4⟩, .intRelOp .i64 (.le .signed), .intTestOp .i32 .eqz,
     .if_ .empty [.return_] []] [],
   .localGet ⟨4⟩, .localSet ⟨5⟩, .intConst .i32 1, .localSet ⟨6⟩]

/-- A checker module from the body of its loop. -/
def checker (locals : List ValType) (loopBody : List Instr) : Module where
  types := [tyQ, tyW, tyA]
  imports := consImports
  funcs := [⟨⟨2⟩, locals, [.localGet ⟨0⟩, .localSet ⟨1⟩, .loop .empty loopBody]⟩]
  exports := [⟨"check", .func ⟨5⟩⟩]

/-- **Proper lists.** -/
def properCheck : Module := checker [.i32, .i32] (stepHead ++ stepTail)

/-- **Proper lists of words.** -/
def wordsCheck : Module := checker [.i32, .i32, .i32] (stepHead ++ elemAtom ++ stepTail)

/-- **Sorted proper lists of words.** -/
def sortedCheck : Module :=
  checker [.i32, .i32, .i32, .i64, .i64, .i32] (stepHead ++ elemAtom ++ elemSorted ++ stepTail)

/-! ## Languages -/

/-- **Spine-proper lists**: `nil`, or a cons cell with any `car` and a spine-proper `cdr`
(the elements may be any trees, dotted pairs included). Equivalently `x = SExp2.ofList xs`
(`spineProperList_iff`). -/
inductive SpineProperList {α : Type} : SExp2 α → Prop where
  | nil : SpineProperList .nil
  | cons (x : SExp2 α) {y : SExp2 α} : SpineProperList y → SpineProperList (.cons x y)

/-- Proper lists in the cons-cell sense (spine-proper): the language of `properCheck`. -/
def properL : Set (SExp2 (BitVec 64)) := {x | SpineProperList x}

/-- Recursively proper lists (`SExp2.ProperList`): every element is an atom or itself a
recursively proper list. Strictly smaller than `properL`; not checked by `properCheck`. -/
def recProperL : Set (SExp2 (BitVec 64)) := {x | SExp2.ProperList x}

/-- Proper lists of words. -/
def wordsL : Set (SExp2 (BitVec 64)) := {x | ∃ ws, x = SExp2.ofAtoms ws}

/-- Sorted proper lists of words (signed `i64` order). -/
def sortedL : Set (SExp2 (BitVec 64)) :=
  {x | ∃ ws, x = SExp2.ofAtoms ws ∧ ws.Pairwise fun a b => a.sle b = true}

/-! ## The store invariant -/

/-- **The store invariant of a checker**: the store's functions are those of the instantiated
module. The Hoare-logic specification (`Silmaril.Wasm.Logic.GameLink.GameSat`) of an export
quantifies over every store meeting the invariant; with the trivial invariant it would include
stores without the checker's function, where the call is stuck, so the specification would be
false. This invariant holds at instantiation, import calls return the store unchanged
(`GameLink.importSpec`), and the checkers write no store. -/
def consInv (m : Module) (s : Store Nat) : Prop := s.funcs = (Verify.instOf m).store.funcs

end Silmaril.Wasm.Game.HandleAccept.Checkers

module

public import Silmaril.Wasm.Game.HandleAccept.Mixed.Stream.Stack.Defs
public import Silmaril.Semantics.Accept.Mixed.Chunk.Defs

/-!
# Chunk exports in instance plays: the chunk buffer as ghost state

`Silmaril.Wasm.Game.HandleAccept.Mixed.Stream` reads a streaming parser's export answers with the
**append buffer** as ghost state (`streamSSpec`). For the chunked exports
`feed(chunk)`/`finish(n) -> (used, tree)` (`Silmaril.Accept.Parse.PEv.feed`, `PEv.finish`), the
returned tree is constrained by the `used` values after the cursor: here the ghost state is the
**chunk buffer** of the parsing session, moved by
`Silmaril.Accept.Mixed.chunkStep` (a chunk is appended; `finish(used, _)`
drops `used` values when that many are buffered, and keeps the buffer otherwise, as an overrun
answered by `callTrap` or `ignore` does).

* `chunkNext pix g f v`: the buffer after the export answer `v` to `f` (unchanged when the answer
  decodes to no parsing event);
* `chunkSSpec pix ppol ρ R Inv` (a `Silmaril.Wasm.Game.HandleAccept.Mixed.Stream.SSpec`): the store
  invariant `Inv` relates the module's store to the buffer; a decoded event returning, from a
  parsing state whose chunk buffer is the ghost `g`, a non-sentinel handle `h` for the input `w`
  has `(w, x) ∈ R` for `ρ h = some x`. For `finish(used, h)` the input is `g.take used`.

## The example `chunkStack`

Imports (by `twoIx`): `0 nil`, `1 cons`, `2 word`, `3 accept` (unused). Three mutable `i32`
globals, initially `0`: a flag `0`, a handle `1` and a count `2`. Exports:

* `0 feed : [i64] → []`: if the count is `-1` (`2³² - 1` values buffered), loop forever
  (`cntGuard`: a further value could not be counted); otherwise the prelude of `stackParse` (if
  the flag is clear, `1 := nil()` and set it), then `1 := cons(word(x), 1)` and `2 := 2 + 1`;
* `1 finish : [i32] → [i32 i32]`: if `n < count` (unsigned), return `(0, nil())`: nothing is
  consumed, the buffered values stay for a later `finish`; otherwise the prelude, then return
  `(count, 1)` and clear the flag and the count: every buffered value is consumed.

So `finish(n)` returns `(used, tree)` with `tree` the list of the `used` consumed values, most
recent first: `chunkR` relates the values to `SExp2.ofAtoms vs.reverse` (for `used = 0`, to
`()`). `ChunkRep`, `chunkInv`: the flag, handle and count represent the buffer `g`: the count is
`g`'s length, a clear flag means `g` is empty, a set flag that the handle denotes `g` reversed.

New definitions (no source).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game
  Silmaril.Accept.Handle Silmaril.Accept.Parse Silmaril.Accept.Mixed Silmaril.Formats
  Silmaril.Wasm.Game.HandleAccept.Parsing Silmaril.Wasm.Game.HandleAccept.Mixed.Stream
  Silmaril.Wasm.Game.HandleAccept.Mixed.Stream.Stack
  Silmaril.Wasm.Game.HandleAccept.Writers.Examples

/-! ## The chunk specification -/

variable {I : ScalarInstance} {V X : Type}

/-- The chunk buffer after an export answer. -/
def chunkNext (pix : ParseExports V) (g : List V) (f : I.F.Op) (v : I.F.Ar f) : List V :=
  match parseDec pix f v with
  | some e => chunkStep g e
  | none => g

/-- **The chunk parsing specification** in the environment `ρ`, with the store invariant `Inv`
relating the module's store to the chunk buffer. -/
def chunkSSpec (pix : ParseExports V) (ppol : PPolicy (BitVec 32))
    (ρ : Silmaril.Accept.Handle.Env (BitVec 32) X) (R : Set (List V × X))
    (Inv : List V → Store Nat → Prop) : SSpec I (List V) where
  inv := Inv
  post g f v := ∀ e, parseDec pix f v = some e → ∀ ps w h ps', ps.buf = g →
    Returns ppol ps e w h ps' → h ≠ ppol.sentinel → ∀ x, ρ h = some x → (w, x) ∈ R
  next := chunkNext pix

/-! ## The example -/

/-- `[i32] → [i32 i32]`. -/
def tyFin2 : RecType := ⟨[⟨true, [], .func ⟨[.i32], [.i32, .i32]⟩⟩]⟩

/-- `if count = -1 then loop forever`. -/
def cntGuard : List Instr :=
  [.globalGet ⟨2⟩, .intConst .i32 (BitVec.allOnes 32), .intRelOp .i32 .eq,
   .if_ .empty [.loop .empty [.br ⟨0⟩]] []]

/-- The body of `feed(x)`. -/
def feedBody : List Instr :=
  cntGuard ++ prelude ++ [.localGet ⟨0⟩, .call ⟨2⟩, .globalGet ⟨1⟩, .call ⟨1⟩, .globalSet ⟨1⟩,
    .globalGet ⟨2⟩, .intConst .i32 1, .intBinOp .i32 .add, .globalSet ⟨2⟩, .return_]

/-- The body of `finish(n)`. -/
def finBody : List Instr :=
  [.localGet ⟨0⟩, .globalGet ⟨2⟩, .intRelOp .i32 (.lt .unsigned),
   .if_ .empty [.intConst .i32 0, .call ⟨0⟩, .return_] []] ++ prelude ++
  [.globalGet ⟨2⟩, .globalGet ⟨1⟩, .intConst .i32 0, .globalSet ⟨0⟩, .intConst .i32 0,
   .globalSet ⟨2⟩, .return_]

/-- **A chunked parser returning the list of the consumed values.** -/
def chunkStack : Module where
  types := [tyNil, tyCons, tyWord, tyA, tyRun, tyFin2]
  imports := [⟨"sexp", "nil", .func ⟨0⟩⟩, ⟨"sexp", "cons", .func ⟨1⟩⟩,
    ⟨"sexp", "word", .func ⟨2⟩⟩, ⟨"sexp", "accept", .func ⟨3⟩⟩]
  globals := [var0, var0, var0]
  funcs := [⟨⟨4⟩, [], feedBody⟩, ⟨⟨5⟩, [], finBody⟩]
  exports := [⟨"feed", .func ⟨4⟩⟩, ⟨"finish", .func ⟨5⟩⟩]

/-- Its parsing exports. -/
def chunkPix : ParseExports (BitVec 64) := {val := i64Val, feed := some 0, finish := some 1}

/-- **The relation of `chunkStack`**: the consumed values and their list, reversed. -/
def chunkR : Set (List (BitVec 64) × SExp2 (BitVec 64)) :=
  {q | q.2 = SExp2.ofAtoms q.1.reverse}

/-- The globals represent the chunk buffer `g`: flag `fl`, handle `acc`, count `cnt`. -/
def ChunkRep (ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64)))
    (g : List (BitVec 64)) (s : Store Nat) (fl acc cnt : BitVec 32) : Prop :=
  gval s 0 = some (.i32 fl) ∧ gval s 1 = some (.i32 acc) ∧ gval s 2 = some (.i32 cnt) ∧
    cnt.toNat = g.length ∧ (fl = 0 → g = []) ∧
    (fl ≠ 0 → ρ acc = some (SExp2.ofAtoms g.reverse))

/-- **The store invariant**: the store represents the chunk buffer `g`. -/
def chunkInv (ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64)))
    (g : List (BitVec 64)) (s : Store Nat) : Prop :=
  s.funcs = (Verify.instOf chunkStack).store.funcs ∧ ∃ fl acc cnt, ChunkRep ρ g s fl acc cnt

end Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk

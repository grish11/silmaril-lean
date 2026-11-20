module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.Hi.Defs

/-!
# Word-tree atoms through linear memory: `word(ptr)`

The memory-carrying writer of `Silmaril.Wasm.Game.HandleAccept.Memory` builds trees over symbols,
strings and byte strings. Word trees (`Silmaril.Formats.WordSExp`, atoms `i64`) through memory:

* `wordWrite` decodes, at the answer of a call returning one `i32` handle `r`,
  - `word(ptr) -> i32`: the `i64` stored **little-endian at `[ptr, ptr + 8)`** of the memory at
    the call (`le64`; out of bounds: no event), as a word atom;
  - `sexp(ptr, len) -> i32`: a list node of `len` child handles at `ptr` (as `memWrite` does);
* `wordAccept` decodes `accept(h)` at the call; `wordRoles`, `wordTraces` and `wordWriterLang` are
  the roles, writer traces and writer language (`sexpW (BitVec 64)`).

The example `wordMod`: imports `0 sexp.word : [i32] → [i32]`, `1 sexp.accept : [i32] → []`, one
memory page; its export `run` stores the `i64` `42` at `[0, 8)` (`i64.store`) and calls
`accept(word(0))`. The admitted hosts are those of `hiMod` (`hiReply`: they keep the code, may
rewrite memory, return one `i32` from import `0` and nothing from import `1`).

New definitions (no source).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.WordAtom

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Game.Accept
  Silmaril.Wasm.Game.IOAccept Silmaril.Accept.Handle Silmaril.Accept.IO Silmaril.Formats
  Silmaril.Formats.Api Silmaril.Wasm.Game.HandleAccept.Memory
  Silmaril.Wasm.Game.HandleAccept.MemSound.Hi

/-- Writer events of word trees. -/
abbrev WordWEv := WEv (SxOp (BitVec 64)) (BitVec 32)

/-- The named imports of the word-tree writer through memory. -/
structure WordImports where
  word : String × String := ("sexp", "word")
  sexp : String × String := ("sexp", "sexp")
  accept : String × String := ("sexp", "accept")

/-- A little-endian `i64` (exactly eight bytes). -/
def le64 : List UInt8 → Option (BitVec 64)
  | [b₀, b₁, b₂, b₃, b₄, b₅, b₆, b₇] =>
      some (BitVec.ofNat 64 (b₀.toNat + 2 ^ 8 * b₁.toNat + 2 ^ 16 * b₂.toNat +
        2 ^ 24 * b₃.toNat + 2 ^ 32 * b₄.toNat + 2 ^ 40 * b₅.toNat + 2 ^ 48 * b₆.toNat +
        2 ^ 56 * b₇.toNat))
  | _ => none

/-- **`word(ptr)`**: the `i64` at `[ptr, ptr + 8)` of the memory at the call. -/
def Callout.word64 (o : Callout) : Option (BitVec 64) := do
  let p ← Callout.args1 Callout.i32? o.args
  le64 (← o.segment p.toNat 8)

/-- **The write of an answered call**: `word(ptr)` or `sexp(ptr, len)` answered with a handle. -/
def wordWrite (ix : WordImports) (o : Callout) (w : HostReply) : Option WordWEv := do
  let r ← replyI32 w
  if o.imp = ix.word then
    return .write (.atom (← Callout.word64 o)) [] r
  else if o.imp = ix.sexp then
    return .write .list (← handles32 o) r
  else none

/-- A call of `accept(h)`. -/
def wordAccept (ix : WordImports) (o : Callout) : Option WordWEv :=
  if o.imp = ix.accept then (Callout.args1 Callout.i32? o.args).map .accept else none

/-- The roles of the word-tree writer: accepts at calls, writes at answers. -/
def wordRoles (ix : WordImports) : Roles Unit WordWEv Unit Unit where
  callIn := wordAccept ix
  answerIn := wordWrite ix

/-- **The writer traces of a module** through the word-tree imports. -/
def wordTraces (P : Profile) (Envs : Store Nat → SEnv UImp → Prop) (memIdx : Nat) (m : Module)
    (ix : WordImports) : Set (List WordWEv) :=
  inputsOf (some .enter) '' tagTraces P Envs memIdx m (wordRoles ix)

/-- **The writer language of a module** through the word-tree imports. -/
def wordWriterLang (P : Profile) (Envs : Store Nat → SEnv UImp → Prop) (memIdx : Nat)
    (m : Module) (ix : WordImports) (pol : Policy (BitVec 32)) : Set WordSExp :=
  writerLang (sexpW (BitVec 64)) pol (wordTraces P Envs memIdx m ix)

/-! ## The example -/

/-- `[i32] → [i32]`. -/
def tyWordP : RecType := ⟨[⟨true, [], .func ⟨[.i32], [.i32]⟩⟩]⟩

/-- The body of `run`: `i64.store 0 42; accept(word(0))`. -/
def wordBody : List Instr :=
  [.intConst .i32 0, .intConst .i64 42, .intStore .i64 none ⟨0⟩ ⟨0, 0⟩,
   .intConst .i32 0, .call ⟨0⟩, .call ⟨1⟩]

/-- **The module.** -/
def wordMod : Module where
  types := [tyWordP, tyAcc, tyRun]
  imports := [⟨"sexp", "word", .func ⟨0⟩⟩, ⟨"sexp", "accept", .func ⟨1⟩⟩]
  memories := [⟨.i32, ⟨1, none⟩⟩]
  funcs := [⟨⟨2⟩, [], wordBody⟩]
  exports := [⟨"run", .func ⟨2⟩⟩]

end Silmaril.Wasm.Game.HandleAccept.MemSound.WordAtom

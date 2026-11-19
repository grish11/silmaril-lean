module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.Items.Defs

/-!
# A memory-returning reader of atom text

`MemSound.Defs` reads the children of a list through linear memory (`items(h, retptr)`). This
topic reads the **text of a string atom** the same way:

* `string_text(h, retptr)` (`TextImports.text`): the host writes, canonical-ABI style, the
  `list<u8>` of the UTF-8 text of the string atom `h` through the return pointer: `(ptr, len)`
  at `retptr` (two little-endian `i32`s) and the `len` bytes at `ptr` (`bytesList`), read off
  the memory **after** the answer, and returns nothing. The decoded event is the read
  `read (atom h) (atom "text")` of the string atom (`textRead`); a reply the decoder cannot read
  (out of bounds, no memory, not UTF-8) is the ill-typed answer `handle 0`, never a correct
  answer of the `atom` query (`sexpR`), so under the trapping read policy such a session is
  discarded. The import's name fixes the kind of the answered atom (a string), as `string(ptr,
  len)` does for writes.
* `textRoles`, `textTraces`, `textReaderLang`, `textContract`: the roles, reader traces, reader
  language (`Silmaril.Accept.Handle.readerLang`, reader `sexpR`) and reader contract, as
  `memReadRoles`, `memReadTraces`, `memReaderLang`, `readerContract` for `items`.

## The checker `textMod`

`textMod` is `itemsMod` with `string_text` for `items`: its export `check(h)` reads the text of
`h` through the return pointer `0` and accepts `h` only when the length word at `[4, 8)` is `2`:

```wat
(func $check (param $h i32)
  (call $string_text (local.get $h) (i32.const 0))  ;; (ptr, len) at [0, 8)
  (if (i32.ne (i32.load offset=4 (i32.const 0)) (i32.const 2)) (then (return)))
  (call $accept (local.get $h)))
```

`twoByteStrs` is what it should accept: string atoms whose UTF-8 encoding has two bytes. The
admitted hosts are `itemsReply` (keep the code, may rewrite memory, return no values).

New definitions (no source).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.Text

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Game.Accept
  Silmaril.Wasm.Game.IOAccept Silmaril.Accept.Handle Silmaril.Formats Silmaril.Formats.Api
  Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Game.HandleAccept.MemSound.Hi Silmaril.Wasm.Game.HandleAccept.MemSound.Items

/-- The named imports of the text reader. -/
structure TextImports where
  text : String × String := ("sexp", "string_text")
  accept : String × String := ("sexp", "accept")

/-- The `list<u8>` returned through `retptr`: `(ptr, len)` at `retptr`, then `len` bytes at
`ptr`. -/
def bytesList (mem : ByteArray) (retptr : Nat) : Option (List UInt8) := do
  let (p, n) ← pair32 (← le32s (← segOf mem retptr 8))
  segOf mem p.toNat n.toNat

/-- The answer of `string_text` read off the reply: the string atom of the UTF-8 text, or the
ill-typed `handle 0` when the reply cannot be read. -/
def textAns (w : HostReply) (retptr : BitVec 32) : SxA MemAtom (BitVec 32) :=
  match (w.mem.bind fun mem => bytesList mem retptr.toNat).bind utf8? with
  | some s => .atom ⟨.string, by decide, s⟩
  | none => .handle 0

/-- **A read of `string_text(h, retptr)`**, decoded at its answer (returning no values). -/
def textRead (ix : TextImports) (o : Callout) (w : HostReply) : Option MemREv :=
  if o.imp = ix.text then
    match o.args, w.result with
    | [.num ⟨.int .i32, h⟩, .num ⟨.int .i32, rp⟩], .values [] =>
        some (.read (.atom h) (textAns w rp))
    | _, _ => none
  else none

/-- A call of `accept(h)`. -/
def textAccept (ix : TextImports) (o : Callout) : Option MemREv :=
  if o.imp = ix.accept then (Callout.args1 Callout.i32? o.args).map .accept else none

/-- The roles of the text reader: accepts at calls, reads at answers. -/
def textRoles (ix : TextImports) : Roles Unit MemREv Unit Unit where
  callIn := textAccept ix
  answerIn := textRead ix

/-- **The reader traces of a module** through the text reader. -/
def textTraces (P : Profile) (Envs : Store Nat → SEnv UImp → Prop) (memIdx : Nat)
    (m : Module) (ix : TextImports) : Set (List MemREv) :=
  inputsOf (some .enter) '' tagTraces P Envs memIdx m (textRoles ix)

/-- **The reader language of a module** through the text reader. -/
def textReaderLang (P : Profile) (Envs : Store Nat → SEnv UImp → Prop) (memIdx : Nat)
    (m : Module) (ix : TextImports) (pol : OnBadRead (SxQ (BitVec 32)) (SxA MemAtom (BitVec 32)))
    (oa : OnInvalid) (Rhos : Set (Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp)) :
    Set SymStrBytesSExp :=
  readerLang (sexpR MemAtom (BitVec 32)) pol oa Rhos (textTraces P Envs memIdx m ix)

/-- **The reader contract** of the text reader in the fixed environment `ρ`. -/
def textContract (ix : TextImports) (ρ : Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp)
    (L : Set SymStrBytesSExp) (reply : UCall Nat → UReply → Prop) : MemContract MemREv where
  pre o := ∀ h, textAccept ix o = some (.accept h) → ∀ t, ρ h = some t → t ∈ L
  ans x := ∀ q a, x = .read q a →
    (sexpR MemAtom (BitVec 32)).valid ρ q ∧ (sexpR MemAtom (BitVec 32)).ok ρ q a
  reply := reply

/-- **The module**: `itemsMod` with `string_text` for `items`. -/
def textMod : Module :=
  { itemsMod with
    imports := [⟨"sexp", "string_text", .func ⟨0⟩⟩, ⟨"sexp", "accept", .func ⟨1⟩⟩] }

/-- String atoms of two UTF-8 bytes. -/
def twoByteStrs : Set SymStrBytesSExp :=
  {x | ∃ (bs : List UInt8) (s : String), bs.length = 2 ∧ utf8? bs = some s ∧
    x = .atom ⟨.string, by decide, s⟩}

end Silmaril.Wasm.Game.HandleAccept.MemSound.Text

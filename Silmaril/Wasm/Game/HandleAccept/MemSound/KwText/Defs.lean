module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.Text.Defs
public import Silmaril.Wasm.Game.HandleAccept.MemSound.Atoms.Defs

/-!
# A memory-returning reader of keyword text

`Silmaril.Wasm.Game.HandleAccept.MemSound.Text` reads the text of a **string** atom through a
return pointer (`string_text(h, retptr)`), over the atoms `MemAtom` (no keywords). This topic
reads the text of a **keyword** the same way, over the atoms with keywords `KwAtom`
(`Silmaril.Wasm.Game.HandleAccept.MemSound.Atoms`, the atoms of `SymStrKwBytesSExp`):

* `keyword_text(h, retptr)` (`KwTextImports.text`): the host writes the `list<u8>` of the UTF-8
  text of the keyword `h` through the return pointer (`(ptr, len)` at `retptr`, the bytes at
  `ptr`, `Text.bytesList`), read off the memory **after** the answer, and returns nothing. The
  decoded event is the read `read (atom h) (atom :text)` (`kwTextRead`); an unreadable reply is
  the ill-typed answer `handle 0`. The import's name fixes the kind of the answered atom (a
  keyword).
* `kwTextRoles`, `kwTextTraces`, `kwTextReaderLang`, `kwTextContract`: roles, reader traces,
  reader language (reader `sexpR KwAtom`) and reader contract, as for `string_text`.
* `kwTextMod`: `textMod` with `keyword_text` for `string_text` (same body: accept `h` only when
  the length word at `[4, 8)` is `2`); `twoByteKws`: keywords whose UTF-8 text has two bytes.

New definitions (no source).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.KwText

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Game.Accept
  Silmaril.Wasm.Game.IOAccept Silmaril.Accept.Handle Silmaril.Formats Silmaril.Formats.Api
  Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Game.HandleAccept.MemSound.Items Silmaril.Wasm.Game.HandleAccept.MemSound.Text
  Silmaril.Wasm.Game.HandleAccept.MemSound.Atoms

/-- Reader events over atoms with keywords and `i32` handles. -/
abbrev KwREv := REv (SxQ (BitVec 32)) (SxA KwAtom (BitVec 32)) (BitVec 32)

/-- The named imports of the keyword text reader. -/
structure KwTextImports where
  text : String × String := ("sexp", "keyword_text")
  accept : String × String := ("sexp", "accept")

/-- The answer of `keyword_text` read off the reply: the keyword of the UTF-8 text, or the
ill-typed `handle 0` when the reply cannot be read. -/
def kwTextAns (w : HostReply) (retptr : BitVec 32) : SxA KwAtom (BitVec 32) :=
  match (w.mem.bind fun mem => bytesList mem retptr.toNat).bind utf8? with
  | some s => .atom ⟨.keyword, by decide, s⟩
  | none => .handle 0

/-- **A read of `keyword_text(h, retptr)`**, decoded at its answer (returning no values). -/
def kwTextRead (ix : KwTextImports) (o : Callout) (w : HostReply) : Option KwREv :=
  if o.imp = ix.text then
    match o.args, w.result with
    | [.num ⟨.int .i32, h⟩, .num ⟨.int .i32, rp⟩], .values [] =>
        some (.read (.atom h) (kwTextAns w rp))
    | _, _ => none
  else none

/-- A call of `accept(h)`. -/
def kwTextAccept (ix : KwTextImports) (o : Callout) : Option KwREv :=
  if o.imp = ix.accept then (Callout.args1 Callout.i32? o.args).map .accept else none

/-- The roles of the keyword text reader: accepts at calls, reads at answers. -/
def kwTextRoles (ix : KwTextImports) : Roles Unit KwREv Unit Unit where
  callIn := kwTextAccept ix
  answerIn := kwTextRead ix

/-- **The reader traces of a module** through the keyword text reader. -/
def kwTextTraces (P : Profile) (Envs : Store Nat → SEnv UImp → Prop) (memIdx : Nat)
    (m : Module) (ix : KwTextImports) : Set (List KwREv) :=
  inputsOf (some .enter) '' tagTraces P Envs memIdx m (kwTextRoles ix)

/-- **The reader language of a module** through the keyword text reader. -/
def kwTextReaderLang (P : Profile) (Envs : Store Nat → SEnv UImp → Prop) (memIdx : Nat)
    (m : Module) (ix : KwTextImports)
    (pol : OnBadRead (SxQ (BitVec 32)) (SxA KwAtom (BitVec 32))) (oa : OnInvalid)
    (Rhos : Set (Silmaril.Accept.Handle.Env (BitVec 32) SymStrKwBytesSExp)) :
    Set SymStrKwBytesSExp :=
  readerLang (sexpR KwAtom (BitVec 32)) pol oa Rhos (kwTextTraces P Envs memIdx m ix)

/-- **The reader contract** of the keyword text reader in the fixed environment `ρ`. -/
def kwTextContract (ix : KwTextImports)
    (ρ : Silmaril.Accept.Handle.Env (BitVec 32) SymStrKwBytesSExp) (L : Set SymStrKwBytesSExp)
    (reply : UCall Nat → UReply → Prop) : MemContract KwREv where
  pre o := ∀ h, kwTextAccept ix o = some (.accept h) → ∀ t, ρ h = some t → t ∈ L
  ans x := ∀ q a, x = .read q a →
    (sexpR KwAtom (BitVec 32)).valid ρ q ∧ (sexpR KwAtom (BitVec 32)).ok ρ q a
  reply := reply

/-- **The module**: `itemsMod` with `keyword_text` for `items`. -/
def kwTextMod : Module :=
  { itemsMod with
    imports := [⟨"sexp", "keyword_text", .func ⟨0⟩⟩,
      ⟨"sexp", "accept", .func ⟨1⟩⟩] }

/-- Keywords of two UTF-8 bytes. -/
def twoByteKws : Set SymStrKwBytesSExp :=
  {x | ∃ (bs : List UInt8) (s : String), bs.length = 2 ∧ utf8? bs = some s ∧
    x = .atom ⟨.keyword, by decide, s⟩}

end Silmaril.Wasm.Game.HandleAccept.MemSound.KwText

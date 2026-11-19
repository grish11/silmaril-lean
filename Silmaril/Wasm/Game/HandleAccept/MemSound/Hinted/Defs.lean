module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.Hi.Defs

/-!
# Hinted Rivest atoms through linear memory: `hinted(hptr, hlen, ptr, len)`

`Silmaril.Formats.HintedSExp` trees have atoms `Hinted = Option (List UInt8) × List UInt8`: an
octet string with an optional display hint (RFC 9804 `[hint]octets`). Through memory:

* `hintedWrite` decodes, at the answer of a call returning one `i32` handle `r`,
  - `hinted(hptr, hlen, ptr, len) -> i32`: the hint at `[hptr, hptr + hlen)` and the octets at
    `[ptr, ptr + len)` of the memory at the call (out of bounds: no event), as the atom
    `(some hint, octets)`;
  - `blob(ptr, len) -> i32`: the hint-free atom `(none, octets)`;
  - `sexp(ptr, len) -> i32`: a list node of `len` child handles at `ptr`;
* `hintedAccept` decodes `accept(h)` at the call; `hintedRoles`, `hintedTraces` and
  `hintedWriterLang` are the roles, writer traces and writer language (`sexpW Hinted`).

The example `hintedMod`: imports `0 sexp.hinted : [i32 i32 i32 i32] → [i32]`,
`1 sexp.accept : [i32] → []`, one memory page; its export `run` stores the bytes `68 69` at
`[0, 2)` (as `hiMod`) and calls `accept(hinted(0, 2, 0, 2))`: the atom `[hi]hi` (hint `hi`,
octets `hi`). The admitted hosts are those of `hiMod` (`hiReply`).

New definitions (no source).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.Hinted

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Game.Accept
  Silmaril.Wasm.Game.IOAccept Silmaril.Accept.Handle Silmaril.Accept.IO Silmaril.Formats
  Silmaril.Formats.Api Silmaril.Wasm.Game.HandleAccept.Memory
  Silmaril.Wasm.Game.HandleAccept.MemSound.Hi

/-- Writer events of hinted trees. -/
abbrev HintedWEv := WEv (SxOp Hinted) (BitVec 32)

/-- The named imports of the hinted writer through memory. -/
structure HintedImports where
  hinted : String × String := ("sexp", "hinted")
  blob : String × String := ("sexp", "blob")
  sexp : String × String := ("sexp", "sexp")
  accept : String × String := ("sexp", "accept")

/-- **`hinted(hptr, hlen, ptr, len)`**: the hint and the octets in the memory at the call. -/
def Callout.hinted (o : Callout) : Option Hinted :=
  match o.args with
  | [.num ⟨.int .i32, hp⟩, .num ⟨.int .i32, hl⟩, .num ⟨.int .i32, p⟩, .num ⟨.int .i32, l⟩] =>
      (o.segment hp.toNat hl.toNat).bind fun h =>
        (o.segment p.toNat l.toNat).map fun bs => (some h, bs)
  | _ => none

/-- **The write of an answered call**: `hinted`, `blob` or `sexp` answered with a handle. -/
def hintedWrite (ix : HintedImports) (o : Callout) (w : HostReply) : Option HintedWEv := do
  let r ← replyI32 w
  if o.imp = ix.hinted then
    return .write (.atom (← Callout.hinted o)) [] r
  else if o.imp = ix.blob then
    return .write (.atom (none, ← o.bytes32)) [] r
  else if o.imp = ix.sexp then
    return .write .list (← handles32 o) r
  else none

/-- A call of `accept(h)`. -/
def hintedAccept (ix : HintedImports) (o : Callout) : Option HintedWEv :=
  if o.imp = ix.accept then (Callout.args1 Callout.i32? o.args).map .accept else none

/-- The roles of the hinted writer: accepts at calls, writes at answers. -/
def hintedRoles (ix : HintedImports) : Roles Unit HintedWEv Unit Unit where
  callIn := hintedAccept ix
  answerIn := hintedWrite ix

/-- **The writer traces of a module** through the hinted imports. -/
def hintedTraces (P : Profile) (Envs : Store Nat → SEnv UImp → Prop) (memIdx : Nat)
    (m : Module) (ix : HintedImports) : Set (List HintedWEv) :=
  inputsOf (some .enter) '' tagTraces P Envs memIdx m (hintedRoles ix)

/-- **The writer language of a module** through the hinted imports. -/
def hintedWriterLang (P : Profile) (Envs : Store Nat → SEnv UImp → Prop) (memIdx : Nat)
    (m : Module) (ix : HintedImports) (pol : Policy (BitVec 32)) : Set HintedSExp :=
  writerLang (sexpW Hinted) pol (hintedTraces P Envs memIdx m ix)

/-! ## The example -/

/-- `[i32 i32 i32 i32] → [i32]`. -/
def tyHinted : RecType := ⟨[⟨true, [], .func ⟨[.i32, .i32, .i32, .i32], [.i32]⟩⟩]⟩

/-- The body of `run`: store `68 69` at `[0, 2)`; `accept(hinted(0, 2, 0, 2))`. -/
def hintedBody : List Instr :=
  [.intConst .i32 0, .intConst .i32 0x6968, .intStore .i32 (some .i16) ⟨0⟩ ⟨0, 0⟩,
   .intConst .i32 0, .intConst .i32 2, .intConst .i32 0, .intConst .i32 2, .call ⟨0⟩,
   .call ⟨1⟩]

/-- **The module.** -/
def hintedMod : Module where
  types := [tyHinted, tyAcc, tyRun]
  imports := [⟨"sexp", "hinted", .func ⟨0⟩⟩, ⟨"sexp", "accept", .func ⟨1⟩⟩]
  memories := [⟨.i32, ⟨1, none⟩⟩]
  funcs := [⟨⟨2⟩, [], hintedBody⟩]
  exports := [⟨"run", .func ⟨2⟩⟩]

/-- The atom `[hi]hi`: hint `hi`, octets `hi`. -/
def hiHinted : Hinted := (some [0x68, 0x69], [0x68, 0x69])

/-! ## Hint and octets from separate segments -/

/-- The body of `run` in `hintedSepMod`: store `68 69 61 62` (`hiab`, one little-endian `i32`) at
`[0, 4)`; `accept(hinted(0, 2, 2, 2))`: the hint from `[0, 2)`, the octets from `[2, 4)`. -/
def hintedSepBody : List Instr :=
  [.intConst .i32 0, .intConst .i32 0x62616968, .intStore .i32 none ⟨0⟩ ⟨0, 0⟩,
   .intConst .i32 0, .intConst .i32 2, .intConst .i32 2, .intConst .i32 2, .call ⟨0⟩,
   .call ⟨1⟩]

/-- **The module `hintedSepMod`**: as `hintedMod`, with hint and octets in disjoint segments. -/
def hintedSepMod : Module where
  types := [tyHinted, tyAcc, tyRun]
  imports := [⟨"sexp", "hinted", .func ⟨0⟩⟩, ⟨"sexp", "accept", .func ⟨1⟩⟩]
  memories := [⟨.i32, ⟨1, none⟩⟩]
  funcs := [⟨⟨2⟩, [], hintedSepBody⟩]
  exports := [⟨"run", .func ⟨2⟩⟩]

/-- The atom `[hi]ab`: hint `hi`, octets `ab`. -/
def hiabHinted : Hinted := (some [0x68, 0x69], [0x61, 0x62])

end Silmaril.Wasm.Game.HandleAccept.MemSound.Hinted

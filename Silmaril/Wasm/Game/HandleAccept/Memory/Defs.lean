module

public import Silmaril.Wasm.Game.IOAccept.Defs
public import Silmaril.Formats.SExp.Api.Defs

/-!
# Memory-carrying writer imports of core Wasm modules

Instance plays carry argument values and results but not memory, so writer imports passing
strings and lists through linear memory are decoded from the **traced sessions** of
`Silmaril.Wasm.Game.IOAccept` instead: a callout (`Silmaril.Wasm.Game.Accept.Callout`) carries
the bytes of the instance's memory **at the call**, and a host answer (`HostReply`) the raw
result. The writer is the n-ary S-expression writer `sexpW MemAtom` over atoms that are
symbols, strings or byte strings (`Silmaril.Formats.SymStrBytesSExp`); imports are named
(`MemImports`, by `(module, name)`):

* `symbol(ptr, len) -> i32`, `string(ptr, len) -> i32`: the UTF-8 text at `[ptr, ptr + len)`
  of the memory (invalid UTF-8 or out of bounds: no event), as a symbol or a string atom;
* `blob(ptr, len) -> i32`: the bytes at `[ptr, ptr + len)`, as a byte-string atom;
* `sexp(ptr, len) -> i32`: a `list<i32>` of `len` child handles at `ptr`, little-endian (the
  canonical ABI layout: `4 * len` bytes), as a list node;
* `accept(h)`.

A write is the event `write op args r` of a call answered with one `i32` `r`, decoded by the
`answerIn` role (`memWrite`), which sees the callout (arguments, memory at the call) and the
reply; `accept(h)` is decoded at the call by the `callIn` role (`memAccept`). Both are inputs of
`Silmaril.Accept.IO.Tag`; `memTraces` keeps them in order (`inputsOf`) over `tagTraces`, with
every export invocation (`Tag.enter`) as the export-call boundary `WEv.enter`, and
`memWriterLang` is the writer language (`Silmaril.Accept.Handle.writerLang`) of those traces.

New definitions (no source).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.Memory

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Game.Accept
  Silmaril.Wasm.Game.IOAccept Silmaril.Accept.Handle Silmaril.Accept.IO Silmaril.Formats
  Silmaril.Formats.Api

/-- Atoms of memory-carrying writers: symbols, strings and byte strings. -/
abbrev MemAtom := Atom [.symbol, .string, .bytes]

/-- Writer events of memory-carrying writers. -/
abbrev MemWEv := WEv (SxOp MemAtom) (BitVec 32)

/-- The named imports of a memory-carrying writer API. -/
structure MemImports where
  symbol : String × String := ("sexp", "symbol")
  string : String × String := ("sexp", "string")
  blob : String × String := ("sexp", "blob")
  sexp : String × String := ("sexp", "sexp")
  accept : String × String := ("sexp", "accept")

/-- Little-endian `i32`s (`none` unless the length is a multiple of four). -/
def le32s : List UInt8 → Option (List (BitVec 32))
  | [] => some []
  | a :: b :: c :: d :: rest =>
      (le32s rest).map fun hs =>
        BitVec.ofNat 32 (a.toNat + 256 * b.toNat + 65536 * c.toNat + 16777216 * d.toNat) :: hs
  | _ => none

/-- UTF-8 text. -/
def utf8? (bs : List UInt8) : Option String := String.fromUTF8? bs.toByteArray

/-- The single `i32` result of a reply. -/
def replyI32 (w : HostReply) : Option (BitVec 32) :=
  match w.result with
  | .values [.num ⟨.int .i32, r⟩] => some r
  | _ => none

/-- The `list<i32>` argument `(ptr, len)` of a callout: `len` little-endian handles. -/
def handles32 (o : Callout) : Option (List (BitVec 32)) := do
  let (p, n) ← Callout.args2 Callout.i32? o.args
  le32s (← o.segment p.toNat (4 * n.toNat))

/-- **The write of an answered call**: `symbol`, `string`, `blob` or `sexp` answered with a
handle. -/
def memWrite (ix : MemImports) (o : Callout) (w : HostReply) : Option MemWEv := do
  let r ← replyI32 w
  if o.imp = ix.symbol then
    return .write (.atom ⟨.symbol, by decide, ← utf8? (← o.bytes32)⟩) [] r
  else if o.imp = ix.string then
    return .write (.atom ⟨.string, by decide, ← utf8? (← o.bytes32)⟩) [] r
  else if o.imp = ix.blob then
    return .write (.atom ⟨.bytes, by decide, ← o.bytes32⟩) [] r
  else if o.imp = ix.sexp then
    return .write .list (← handles32 o) r
  else none

/-- **A call of `accept(h)`.** -/
def memAccept (ix : MemImports) (o : Callout) : Option MemWEv :=
  if o.imp = ix.accept then (Callout.args1 Callout.i32? o.args).map .accept else none

/-- The roles of a memory-carrying writer: accepts at calls, writes at answers. -/
def memRoles (ix : MemImports) : Roles Unit MemWEv Unit Unit where
  callIn := memAccept ix
  answerIn := memWrite ix

/-- The inputs of a tag list, in order, with every export invocation (`Tag.enter`) read as
`enter`. -/
def inputsOf {X I O C : Type} (enter : Option I) : List (Tag X I O C) → List I
  | [] => []
  | .inp i :: ts => i :: inputsOf enter ts
  | .enter _ :: ts => enter.toList ++ inputsOf enter ts
  | _ :: ts => inputsOf enter ts

/-- **The writer traces of a module**: the inputs of its traced sessions (every instantiation
and environment of `Envs`, memory index `memIdx`), every export invocation read as the
export-call boundary `WEv.enter`. -/
def memTraces (P : Profile) (Envs : Store Nat → SEnv UImp → Prop) (memIdx : Nat) (m : Module)
    (ix : MemImports) : Set (List MemWEv) :=
  inputsOf (some .enter) '' tagTraces P Envs memIdx m (memRoles ix)

/-- **The writer language of a module** through memory-carrying imports. -/
def memWriterLang (P : Profile) (Envs : Store Nat → SEnv UImp → Prop) (memIdx : Nat)
    (m : Module) (ix : MemImports) (pol : Policy (BitVec 32)) : Set SymStrBytesSExp :=
  writerLang (sexpW MemAtom) pol (memTraces P Envs memIdx m ix)

end Silmaril.Wasm.Game.HandleAccept.Memory

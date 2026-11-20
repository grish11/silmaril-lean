module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.Hi.Defs

/-!
# The tagged-node (AST) writer through linear memory: `tag(tagptr, taglen, children, n)`

`Silmaril.Formats.Api.astW S` builds tagged ASTs (`AST S`): one operation per tag with its
payload, children admitted by the tag's arity. Through memory, with tag names as text:

* `strSig`: the AST signature whose tags are strings, with no payload and any number of
  children (`Arity.star`);
* `Callout.tagNode`: the call `tag(tagptr, taglen, children, n)` reads the UTF-8 tag name at
  `[tagptr, tagptr + taglen)` and `n` little-endian `i32` child handles at
  `[children, children + 4n)` of the memory at the call (out of bounds or invalid UTF-8: no
  event);
* `astWrite` decodes, at the answer of a call returning one `i32` handle `r`, the write
  `write ⟨name, ()⟩ [c₁, …, cₙ] r`; `astAccept` decodes `accept(h)` at the call; `astRoles`,
  `astTraces` and `astWriterLang` are the roles, writer traces (every export invocation read as
  `WEv.enter`) and writer language (`Silmaril.Accept.Handle.writerLang` of `astW strSig`).

## The example `astMod`

Imports `0 ast.tag : [i32 i32 i32 i32] → [i32]`, `1 ast.accept : [i32] → []`; one memory of one
page; export `run : [] → []` with one `i32` local:

```wat
(func $run (local $a i32)
  (i32.store8 (i32.const 16) (i32.const 0x61))                   ;; "a" at 16
  (local.set $a (call $tag (i32.const 16) (i32.const 1) (i32.const 0) (i32.const 0)))
  (i32.store (i32.const 0) (local.get $a))                       ;; list<i32> [$a] at 0
  (i32.store8 (i32.const 16) (i32.const 0x66))                   ;; "f" at 16
  (call $accept (call $tag (i32.const 16) (i32.const 1) (i32.const 0) (i32.const 1))))
```

It builds the node `f(a)` (`faTree`): the leaf `a` (no children) and the node `f` whose one
child is the handle of `a`, stored in memory after the first `tag` call returned. The admitted
hosts are those of `hiMod` (`hiReply`: keep the code and the number of memories, may rewrite
memory, one `i32` from `tag`, nothing from `accept`).

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.Ast

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Game.Accept
  Silmaril.Wasm.Game.IOAccept Silmaril.Accept.Handle Silmaril.Accept.IO Silmaril.Formats
  Silmaril.Formats.Api Silmaril.Wasm.Game.HandleAccept.Memory
  Silmaril.Wasm.Game.HandleAccept.MemSound.Hi

/-! ## The signature and the decoder -/

/-- **The AST signature with string tags**: any tag name, no payload, any number of children. -/
def strSig : AstSig where
  Tag := String
  Arg _ := Unit
  arity _ := .star

/-- Writer events of the string-tagged AST writer. -/
abbrev AstWEv := WEv (Σ t, strSig.Arg t) (BitVec 32)

/-- The named imports of the AST writer through memory. -/
structure AstImports where
  tag : String × String := ("ast", "tag")
  accept : String × String := ("ast", "accept")

/-- **`tag(tagptr, taglen, children, n)`**: the UTF-8 tag name at `[tagptr, tagptr + taglen)`
and the `n` little-endian child handles at `[children, children + 4n)` of the memory at the
call. -/
def Callout.tagNode (o : Callout) : Option (String × List (BitVec 32)) :=
  match o.args with
  | [.num ⟨.int .i32, tp⟩, .num ⟨.int .i32, tl⟩, .num ⟨.int .i32, cp⟩, .num ⟨.int .i32, n⟩] =>
      (o.segment tp.toNat tl.toNat).bind fun bs => (utf8? bs).bind fun name =>
        (o.segment cp.toNat (4 * n.toNat)).bind fun cs => (le32s cs).map fun hs => (name, hs)
  | _ => none

/-- **The write of an answered call**: `tag` answered with a handle. -/
def astWrite (ix : AstImports) (o : Callout) (w : HostReply) : Option AstWEv := do
  let r ← replyI32 w
  if o.imp = ix.tag then
    let (name, hs) ← Callout.tagNode o
    return .write ⟨name, ()⟩ hs r
  else none

/-- A call of `accept(h)`. -/
def astAccept (ix : AstImports) (o : Callout) : Option AstWEv :=
  if o.imp = ix.accept then (Callout.args1 Callout.i32? o.args).map .accept else none

/-- The roles of the AST writer: accepts at calls, writes at answers. -/
def astRoles (ix : AstImports) : Roles Unit AstWEv Unit Unit where
  callIn := astAccept ix
  answerIn := astWrite ix

/-- **The writer traces of a module** through the AST imports. -/
def astTraces (P : Numerics.Profile) (Envs : Store Nat → SEnv UImp → Prop) (memIdx : Nat)
    (m : Module) (ix : AstImports) : Set (List AstWEv) :=
  inputsOf (some .enter) '' tagTraces P Envs memIdx m (astRoles ix)

/-- **The writer language of a module** through the AST imports. -/
def astWriterLang (P : Numerics.Profile) (Envs : Store Nat → SEnv UImp → Prop) (memIdx : Nat)
    (m : Module) (ix : AstImports) (pol : Policy (BitVec 32)) : Set (AST strSig) :=
  writerLang (astW strSig) pol (astTraces P Envs memIdx m ix)

/-! ## The example -/

/-- `[i32 i32 i32 i32] → [i32]`. -/
def tyTag : RecType := ⟨[⟨true, [], .func ⟨[.i32, .i32, .i32, .i32], [.i32]⟩⟩]⟩

/-- The body of `run`. -/
def astBody : List Instr :=
  [.intConst .i32 16, .intConst .i32 0x61, .intStore .i32 (some .i8) ⟨0⟩ ⟨0, 0⟩,
   .intConst .i32 16, .intConst .i32 1, .intConst .i32 0, .intConst .i32 0, .call ⟨0⟩,
   .localSet ⟨0⟩,
   .intConst .i32 0, .localGet ⟨0⟩, .intStore .i32 none ⟨0⟩ ⟨0, 0⟩,
   .intConst .i32 16, .intConst .i32 0x66, .intStore .i32 (some .i8) ⟨0⟩ ⟨0, 0⟩,
   .intConst .i32 16, .intConst .i32 1, .intConst .i32 0, .intConst .i32 1, .call ⟨0⟩,
   .call ⟨1⟩]

/-- **The module.** -/
def astMod : Module where
  types := [tyTag, tyAcc, tyRun]
  imports := [⟨"ast", "tag", .func ⟨0⟩⟩, ⟨"ast", "accept", .func ⟨1⟩⟩]
  memories := [⟨.i32, ⟨1, none⟩⟩]
  funcs := [⟨⟨2⟩, [.i32], astBody⟩]
  exports := [⟨"run", .func ⟨2⟩⟩]

/-- The leaf `a`. -/
def leafA : AST strSig := AST.node (S := strSig) "a" () []

/-- **The node `f(a)`.** -/
def faTree : AST strSig := AST.node (S := strSig) "f" () [leafA]

end Silmaril.Wasm.Game.HandleAccept.MemSound.Ast

module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.Hi.Defs

/-!
# The cons API through linear memory

`Silmaril.Wasm.Game.HandleAccept.Memory` decodes the n-ary writer `sexp(ptr, len)` over atoms read
from memory. This topic decodes the **cons writer** (`Silmaril.Formats.Api.consW`, trees
`SExp2`) through memory-carrying imports, from the traced sessions of
`Silmaril.Wasm.Game.IOAccept`:

* `symbol(ptr, len) -> i32`, `string(ptr, len) -> i32`: the UTF-8 text at `[ptr, ptr + len)` of the
  memory at the call, as a symbol or a string atom; `blob(ptr, len) -> i32`: the bytes, as a
  byte-string atom (`MemAtom`, as for the n-ary writer);
* `nil() -> i32`: the empty list; `cons(a, b) -> i32`: the pair of the trees `a` and `b` denote;
* `accept(h)`.

`consWrite` decodes a write at the answer (one `i32` result), `consAccept` an accept at the call;
`consRoles`, `consTraces` and `consWriterLang` are the roles, writer traces (every export
invocation read as `WEv.enter`) and writer language (`Silmaril.Accept.Handle.writerLang` of
`consW MemAtom`).

`roleWriterContract R W sent ρ L reply`: the writer contract of
`Silmaril.Wasm.Game.HandleAccept.MemSound.writerContract` for any roles `R` and writer `W`:
accepts decoded at a call name members of `L` in `ρ`; decoded writes return the sentinel `sent`
or a handle denoting in `ρ` the tree they build in `ρ`.

## The example `consMod`

Imports `0 sexp.symbol : [i32 i32] → [i32]`, `1 sexp.nil : [] → [i32]`,
`2 sexp.cons : [i32 i32] → [i32]`, `3 sexp.accept : [i32] → []`; one memory of one page; export
`run : [] → []`:

```wat
(func $run
  (i32.store16 (i32.const 0) (i32.const 0x6968))                    ;; "hi" at [0, 2)
  (call $accept (call $cons (call $symbol (i32.const 0) (i32.const 2)) (call $nil))))
```

It builds the one-element list `(hi)` = `cons(hi, nil)` (`hiList`). The admitted hosts
(`consReply`) keep the code and the number of memories, may rewrite memory, and return one `i32`
from `symbol`, `nil` and `cons` and nothing from `accept`.

New definitions (no source).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.Cons

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Game.Accept
  Silmaril.Wasm.Game.IOAccept Silmaril.Accept.Handle Silmaril.Accept.IO Silmaril.Formats
  Silmaril.Formats.Api Silmaril.Wasm.Game.HandleAccept.Memory
  Silmaril.Wasm.Game.HandleAccept.MemSound Silmaril.Wasm.Game.HandleAccept.MemSound.Hi

/-! ## The decoder -/

/-- Writer events of the cons writer over memory-carrying atoms. -/
abbrev ConsWEv := WEv (ConsOp MemAtom) (BitVec 32)

/-- The named imports of the cons writer through memory. -/
structure ConsImports where
  symbol : String × String := ("sexp", "symbol")
  string : String × String := ("sexp", "string")
  blob : String × String := ("sexp", "blob")
  nil : String × String := ("sexp", "nil")
  cons : String × String := ("sexp", "cons")
  accept : String × String := ("sexp", "accept")

/-- **The write of an answered call**: an atom read from memory, `nil()` or `cons(a, b)`. -/
def consWrite (ix : ConsImports) (o : Callout) (w : HostReply) : Option ConsWEv := do
  let r ← replyI32 w
  if o.imp = ix.symbol then
    return .write (.atom ⟨.symbol, by decide, ← utf8? (← o.bytes32)⟩) [] r
  else if o.imp = ix.string then
    return .write (.atom ⟨.string, by decide, ← utf8? (← o.bytes32)⟩) [] r
  else if o.imp = ix.blob then
    return .write (.atom ⟨.bytes, by decide, ← o.bytes32⟩) [] r
  else if o.imp = ix.nil then
    if o.args = [] then return .write .nil [] r else none
  else if o.imp = ix.cons then
    let (a, b) ← Callout.args2 Callout.i32? o.args
    return .write .cons [a, b] r
  else none

/-- A call of `accept(h)`. -/
def consAccept (ix : ConsImports) (o : Callout) : Option ConsWEv :=
  if o.imp = ix.accept then (Callout.args1 Callout.i32? o.args).map .accept else none

/-- The roles of the cons writer: accepts at calls, writes at answers. -/
def consRoles (ix : ConsImports) : Roles Unit ConsWEv Unit Unit where
  callIn := consAccept ix
  answerIn := consWrite ix

/-- **The writer traces of a module** through the cons imports. -/
def consTraces (P : Profile) (Envs : Store Nat → SEnv UImp → Prop) (memIdx : Nat) (m : Module)
    (ix : ConsImports) : Set (List ConsWEv) :=
  inputsOf (some .enter) '' tagTraces P Envs memIdx m (consRoles ix)

/-- **The writer language of a module** through the cons imports. -/
def consWriterLang (P : Profile) (Envs : Store Nat → SEnv UImp → Prop) (memIdx : Nat)
    (m : Module) (ix : ConsImports) (pol : Policy (BitVec 32)) : Set (SExp2 MemAtom) :=
  writerLang (consW MemAtom) pol (consTraces P Envs memIdx m ix)

/-! ## Writer contracts for any roles -/

/-- **The writer contract** for roles `R` and writer `W` in the fixed environment `ρ`. -/
def roleWriterContract {Op Y : Type} (R : Roles Unit (WEv Op (BitVec 32)) Unit Unit)
    (W : Writer Op Y) (sent : Option (BitVec 32)) (ρ : Silmaril.Accept.Handle.Env (BitVec 32) Y)
    (L : Set Y)
    (reply : UCall Nat → UReply → Prop) : MemContract (WEv Op (BitVec 32)) where
  pre o := ∀ h, R.callIn o = some (.accept h) → ∀ t, ρ h = some t → t ∈ L
  ans x := ∀ op args r, x = .write op args r →
    sent = some r ∨ ∃ t, W.built ρ op args = some t ∧ ρ r = some t
  reply := reply

/-! ## The example -/

/-- `[] → [i32]`. -/
def tyNil : RecType := ⟨[⟨true, [], .func ⟨[], [.i32]⟩⟩]⟩

/-- The body of `run`. -/
def consBody : List Instr :=
  [.intConst .i32 0, .intConst .i32 0x6968, .intStore .i32 (some .i16) ⟨0⟩ ⟨0, 0⟩,
   .intConst .i32 0, .intConst .i32 2, .call ⟨0⟩, .call ⟨1⟩, .call ⟨2⟩, .call ⟨3⟩]

/-- **The module.** -/
def consMod : Module where
  types := [tySym, tyAcc, tyRun, tyNil]
  imports := [⟨"sexp", "symbol", .func ⟨0⟩⟩, ⟨"sexp", "nil", .func ⟨3⟩⟩,
    ⟨"sexp", "cons", .func ⟨0⟩⟩, ⟨"sexp", "accept", .func ⟨1⟩⟩]
  memories := [⟨.i32, ⟨1, none⟩⟩]
  funcs := [⟨⟨2⟩, [], consBody⟩]
  exports := [⟨"run", .func ⟨4⟩⟩]

/-- The shape of the values returned by host code `k`: one `i32` from `symbol`, `nil` and
`cons`, nothing from `accept`. -/
def consShape (k : Nat) (vs : List Val) : Prop :=
  (k = 0 ∨ k = 1 ∨ k = 2 → ∃ c, vs = [.i32 c]) ∧ (k = 3 → vs = [])

/-- The admitted host replies. -/
def consReply : UCall Nat → UReply → Prop := ShapedReply consShape

/-- A counting host's answers for `consMod`: one handle from host codes `0`, `1` and `2`,
nothing otherwise. -/
def consOut : Nat → BitVec 32 → List Val
  | 0, q => [.i32 q]
  | 1, q => [.i32 q]
  | 2, q => [.i32 q]
  | _, _ => []

/-- The one-element list `(hi)`. -/
def hiList : SExp2 MemAtom := .cons (.atom hiAtom) .nil

/-! ## Mixed atom kinds: `consMix` -/

/-- The body of `run` in `consMix`: `"hi"` at `[0, 2)`, `symbol(0, 2)`; `"hi"` at `[0, 2)` again
(the host may have rewritten memory), `string(0, 2)`; `nil()`; two `cons`; `accept`. -/
def consMixBody : List Instr :=
  [.intConst .i32 0, .intConst .i32 0x6968, .intStore .i32 (some .i16) ⟨0⟩ ⟨0, 0⟩,
   .intConst .i32 0, .intConst .i32 2, .call ⟨0⟩,
   .intConst .i32 0, .intConst .i32 0x6968, .intStore .i32 (some .i16) ⟨0⟩ ⟨0, 0⟩,
   .intConst .i32 0, .intConst .i32 2, .call ⟨1⟩,
   .call ⟨2⟩, .call ⟨3⟩, .call ⟨3⟩, .call ⟨4⟩]

/-- **The module `consMix`**: imports `0 sexp.symbol`, `1 sexp.string : [i32 i32] → [i32]`,
`2 sexp.nil`, `3 sexp.cons`, `4 sexp.accept`; it builds `(hi "hi")`, a list of a symbol and a
string atom read from the same bytes. -/
def consMix : Module where
  types := [tySym, tyAcc, tyRun, tyNil]
  imports := [⟨"sexp", "symbol", .func ⟨0⟩⟩, ⟨"sexp", "string", .func ⟨0⟩⟩,
    ⟨"sexp", "nil", .func ⟨3⟩⟩, ⟨"sexp", "cons", .func ⟨0⟩⟩, ⟨"sexp", "accept", .func ⟨1⟩⟩]
  memories := [⟨.i32, ⟨1, none⟩⟩]
  funcs := [⟨⟨2⟩, [], consMixBody⟩]
  exports := [⟨"run", .func ⟨5⟩⟩]

/-- The shape of the values returned by host code `k` in `consMix`: one `i32` from `symbol`,
`string`, `nil` and `cons`, nothing from `accept`. -/
def consMixShape (k : Nat) (vs : List Val) : Prop :=
  (k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 → ∃ c, vs = [.i32 c]) ∧ (k = 4 → vs = [])

/-- The admitted host replies of `consMix`. -/
def consMixReply : UCall Nat → UReply → Prop := ShapedReply consMixShape

/-- A counting host's answers for `consMix`. -/
def consMixOut : Nat → BitVec 32 → List Val
  | 0, q => [.i32 q]
  | 1, q => [.i32 q]
  | 2, q => [.i32 q]
  | 3, q => [.i32 q]
  | _, _ => []

/-- The string atom `"hi"`. -/
def hiStr : MemAtom := ⟨.string, by decide, "hi"⟩

/-- The two-element list `(hi "hi")`: the symbol `hi` and the string `"hi"`. -/
def mixList : SExp2 MemAtom := .cons (.atom hiAtom) (.cons (.atom hiStr) .nil)

end Silmaril.Wasm.Game.HandleAccept.MemSound.Cons

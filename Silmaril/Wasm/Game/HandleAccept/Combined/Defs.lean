module

public import Silmaril.Wasm.Game.HandleAccept.Writer.Defs

/-!
# Combined writer and reader sessions of core Wasm modules

A module that **writes** trees through a constructor API and **reads** them back through an
inspection API, over the same `i32` handles: the combined host
`Silmaril.Accept.Handle.combined W R pol rpol` (store semantics; reads are answered from the
current store). Its events `CEv` are decoded per move from the plays of the instance:

* `accept(h)` is observed when it is asked: `.w (.accept h)`;
* answered writes `nil()`, `word(x)`, `cons(a, b)` returning `r`: `.w (.write op args r)`;
* answered reads `kind(h)`, `car(h)`, `cdr(h)`: `.r q a` (`kind` codes as `kindAns`);
* export calls: `.w .enter`.

`CombImports` are the import indices; `combDecAsk`, `combDecAns` the decoders;
`moduleCombLang P m ix pol` the combined language of a module (cons writer `consW`, cons reader
`consR`, the trapping read policy).

**Assume/guarantee specification** (`combISpec W R s dAsk dAns ρ L`), in a fixed environment
`ρ`: answered writes return the sentinel `s` or a handle denoting in `ρ` the tree built in `ρ`;
answered reads are correct in `ρ`; `accept(h)` names a handle whose meaning in `ρ`, if any, is in
`L`. The store bridge (`Thms`) instantiates `ρ` with the final store of a run.

New definitions (no source).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.Combined

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game
  Silmaril.Accept Silmaril.Accept.Handle Silmaril.Formats Silmaril.Formats.Api
open Silmaril.Wasm.Game.HandleAccept Silmaril.Wasm.Game.HandleAccept.Writers
open Silmaril.Wasm.Logic.Strategy (ISpec)

/-- Combined cons writer and reader events over `i32` handles and `i64` words. -/
abbrev ConsCEv := CEv (ConsOp (BitVec 64)) (BitVec 32) (ConsQ (BitVec 32))
  (ConsA (BitVec 64) (BitVec 32))

/-- Import indices of the combined cons API. -/
structure CombImports where
  nil : Nat
  cons : Nat
  word : Nat
  accept : Nat
  kind : Nat
  car : Nat
  cdr : Nat

variable {ts : List FnType}

/-- Calls of `accept(h)`. -/
def combDecAsk (ix : CombImports) (e : (ifaceSig ts).Op) : Option ConsCEv :=
  if e.1.val = ix.accept then (i32Arg e.2.1).map fun h => .w (.accept h) else none

/-- Answered writes (`nil`, `word`, `cons`) and reads (`kind`, `car`, `cdr`). -/
def combDecAns (ix : CombImports) (e : (ifaceSig ts).Op) (v : (ifaceSig ts).Ar e) :
    Option ConsCEv := do
  let r ← retI32 v
  if e.1.val = ix.word then return .w (.write (.atom (← i64Arg e.2.1)) [] r)
  else if e.1.val = ix.nil then
    if e.2.1 = [] then return .w (.write .nil [] r) else none
  else if e.1.val = ix.cons then return .w (.write .cons (← i32Pair e.2.1) r)
  else if e.1.val = ix.kind then return .r (.kind (← i32Arg e.2.1)) (kindAns r)
  else if e.1.val = ix.car then return .r (.car (← i32Arg e.2.1)) (.handle r)
  else if e.1.val = ix.cdr then return .r (.cdr (← i32Arg e.2.1)) (.handle r)
  else none

/-- **The combined language of a module**: cons writer and cons reader over the same handles,
store semantics, reads trapping when invalid. -/
noncomputable def moduleCombLang (P : Profile) (m : Module) (ix : CombImports)
    (pol : Policy (BitVec 32)) : Set (SExp2 (BitVec 64)) :=
  (combined (consW (BitVec 64)) (consR (BitVec 64) (BitVec 32)) pol .trap).lang
    (handleTraces ((Verify.instOf m).strategy P (Verify.instOf m).store) (some (.w .enter))
      (combDecAsk ix) (combDecAns ix))

/-- **The assume/guarantee specification of a combined session** in the fixed environment `ρ`
for the sentinel `s`. -/
def combISpec {E : Sig.{0}} {Op Q A X : Type} (W : Writer Op X) (R : Reader Q A (BitVec 32) X)
    (s : Option (BitVec 32)) (dAsk : E.Op → Option (CEv Op (BitVec 32) Q A))
    (dAns : (e : E.Op) → E.Ar e → Option (CEv Op (BitVec 32) Q A))
    (ρ : Env (BitVec 32) X) (L : Set X) : ISpec E where
  pre e := ∀ h, dAsk e = some (.w (.accept h)) → ∀ t, ρ h = some t → t ∈ L
  post e v := (∀ op args r, dAns e v = some (.w (.write op args r)) →
      s = some r ∨ ∃ t, W.built ρ op args = some t ∧ ρ r = some t) ∧
    ∀ q a, dAns e v = some (.r q a) → R.valid ρ q ∧ R.ok ρ q a

end Silmaril.Wasm.Game.HandleAccept.Combined

namespace Silmaril.Wasm.Game.HandleAccept.Combined

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Formats

/-! ## A write-then-read-back module -/

/-- `[] → [i32]`. -/
def tyNil : RecType := ⟨[⟨true, [], .func ⟨[], [.i32]⟩⟩]⟩
/-- `[i32 i32] → [i32]`. -/
def tyCons : RecType := ⟨[⟨true, [], .func ⟨[.i32, .i32], [.i32]⟩⟩]⟩
/-- `[i64] → [i32]`. -/
def tyWord : RecType := ⟨[⟨true, [], .func ⟨[.i64], [.i32]⟩⟩]⟩
/-- `[i32] → []`. -/
def tyA : RecType := ⟨[⟨true, [], .func ⟨[.i32], []⟩⟩]⟩
/-- `[i32] → [i32]`. -/
def tyQ : RecType := ⟨[⟨true, [], .func ⟨[.i32], [.i32]⟩⟩]⟩
/-- `[i64] → []`. -/
def tyRun : RecType := ⟨[⟨true, [], .func ⟨[.i64], []⟩⟩]⟩

/-- The body of `run(x)` (locals: `1` the written handle `c`, `2` its `cdr`). It writes
`c = cons(word(x), nil())`, then reads it back: returns unless `kind(c)` is cons,
`kind(car(c))` is atom and `kind(cdr(c))` is nil, and then accepts `c`. -/
def readBackBody : List Instr :=
  [.localGet ⟨0⟩, .call ⟨2⟩, .call ⟨0⟩, .call ⟨1⟩, .localSet ⟨1⟩,
   .localGet ⟨1⟩, .call ⟨4⟩, .intConst .i32 2, .intRelOp .i32 .ne, .if_ .empty [.return_] [],
   .localGet ⟨1⟩, .call ⟨5⟩, .call ⟨4⟩, .intConst .i32 1, .intRelOp .i32 .ne,
   .if_ .empty [.return_] [],
   .localGet ⟨1⟩, .call ⟨6⟩, .localSet ⟨2⟩,
   .localGet ⟨2⟩, .call ⟨4⟩, .intConst .i32 0, .intRelOp .i32 .ne, .if_ .empty [.return_] [],
   .localGet ⟨1⟩, .call ⟨3⟩]

/-- **Write a one-element list, read it back, accept it if the reads confirm the shape.**
Imports (`readBackIx`): `0 nil`, `1 cons`, `2 word`, `3 accept`, `4 kind`, `5 car`, `6 cdr`;
export `run : [i64] → []`. -/
def readBack : Module where
  types := [tyNil, tyCons, tyWord, tyA, tyQ, tyRun]
  imports := [⟨"sexp", "nil", .func ⟨0⟩⟩, ⟨"sexp", "cons", .func ⟨1⟩⟩,
    ⟨"sexp", "word", .func ⟨2⟩⟩, ⟨"sexp", "accept", .func ⟨3⟩⟩,
    ⟨"sexp", "kind", .func ⟨4⟩⟩, ⟨"sexp", "car", .func ⟨4⟩⟩, ⟨"sexp", "cdr", .func ⟨4⟩⟩]
  funcs := [⟨⟨5⟩, [.i32, .i32], readBackBody⟩]
  exports := [⟨"run", .func ⟨7⟩⟩]

/-- Its import indices. -/
def readBackIx : CombImports := ⟨0, 1, 2, 3, 4, 5, 6⟩

/-- One-element lists of words: the language of `readBack`. -/
def singleL : Set (SExp2 (BitVec 64)) := {t | ∃ w, t = .cons (.atom w) .nil}

/-- The store invariant: the store's functions are those of the instance. -/
def readBackInv (s : Store Nat) : Prop := s.funcs = (Verify.instOf readBack).store.funcs

end Silmaril.Wasm.Game.HandleAccept.Combined

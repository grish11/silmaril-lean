module

public import Silmaril.Wasm.Game.HandleAccept.Defs

/-!
# Writer APIs of core Wasm modules over `i32` handles

Decoders from the plays of a module instance (`Silmaril.Wasm.Game.HandleAccept.playEvents`)
into the writer events `Silmaril.Accept.Handle.WEv` of two constructor APIs over `i32` handles
and `i64` words:

* **the cons API** (`ConsWImports`, writer `Silmaril.Formats.Api.consW`, dotted
  S-expressions `SExp2 (BitVec 64)`): `nil : [] → [i32]`, `cons : [i32 i32] → [i32]`,
  `word : [i64] → [i32]`, `accept : [i32] → []` and optionally `accept_all : [] → []`;
* **the n-ary API** (`SxWImports`, writer `Silmaril.Formats.Api.sexpW`, `SExp (BitVec 64)`):
  `word : [i64] → [i32]`, any number of fixed-arity list constructors
  `list_k : [i32 × k] → [i32]` (the children are all the arguments, so `list0`, `list1`, … are
  imports of the same operation `SxOp.list` with different arities), `accept` and optionally
  `accept_all`.

**Where events come from.** A write is observed when it is *answered*: the Opponent move
`.inl (.ans e v)` carries the import index and its arguments (`e`) and the answer `v`; an
answer returning one `i32` `r` is the event `write op args r`. Every other answer of a
constructor import (a trap or an uncaught exception from the environment) is no event: the
environment did not return a handle, and the module observes nothing it could later pass back.
`accept(h)` and `accept_all()` are observed when they are *asked* (the Proponent move
`.inl (.ask e)`), before any answer, as in `WEv`. Arguments are decoded exactly: a call whose
arguments are not of the expected shape (only possible when the import is declared with
another type) is no event.

**Languages.** `moduleTraces P m dAsk dAns` are the decoded traces of every play of the
instance `Verify.instOf m` from its initial store, for the profile `P`, every export call
decoded as `WEv.enter` (the instance and its store persist across export calls, so a
call-local trap is resumed by the next one); the writer languages
are `writerLang` (store semantics) and `fixedLang` (fixed environments) of the writer over
them: `moduleConsWLang`, `moduleSxWLang`, `moduleConsWFixedLang`, `moduleSxWFixedLang`.

**Assume/guarantee specifications.** `writerISpec W s dAsk dAns ρ L` is the import
specification of a writer API in a fixed environment `ρ`: an answered write returns the sentinel
`s` or a handle denoting, in `ρ`, the tree the call builds in `ρ` (`post`), and `accept(h)` names
a handle whose meaning in `ρ`, if any, is in `L` (`pre`). Unlike the reader specifications this
does not say which handles are fresh: a module proof that needs no freshness can ignore it.

New definitions (no source).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.Writers

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game
  Silmaril.Accept.Handle Silmaril.Formats Silmaril.Formats.Api
open Silmaril.Wasm.Game.HandleAccept
open Silmaril.Wasm.Logic.Strategy (ISpec)

/-! ## Values -/

/-- A list of `i32` arguments. -/
def i32Args : List Val → Option (List (BitVec 32))
  | [] => some []
  | .num ⟨.int .i32, h⟩ :: vs => (i32Args vs).map (h :: ·)
  | _ => none

/-- Exactly two `i32` arguments. -/
def i32Pair : List Val → Option (List (BitVec 32))
  | [.num ⟨.int .i32, a⟩, .num ⟨.int .i32, b⟩] => some [a, b]
  | _ => none

/-- A single `i64` argument. -/
def i64Arg : List Val → Option (BitVec 64)
  | [.num ⟨.int .i64, w⟩] => some w
  | _ => none

/-- The single `i32` returned by an answer, if it returned one. -/
def retI32 {ft : FnType} (v : Answer ft) : Option (BitVec 32) :=
  (ansVals v).bind i32Res

/-- The decoded traces of every play of a module's instance from its initial store, export calls
decoded as `enter`. -/
noncomputable def moduleTraces {Op H : Type} (P : Profile) (m : Module)
    (dAsk : (Verify.instOf m).E.Op → Option (WEv Op H))
    (dAns : (e : (Verify.instOf m).E.Op) → (Verify.instOf m).E.Ar e → Option (WEv Op H)) :
    Set (List (WEv Op H)) :=
  handleTraces ((Verify.instOf m).strategy P (Verify.instOf m).store) (some .enter) dAsk dAns

/-! ## The cons writer API -/

/-- Import indices of the cons writer API. -/
structure ConsWImports where
  nil : Nat
  cons : Nat
  word : Nat
  accept : Nat
  acceptAll : Option Nat := none

/-- Cons writer events over `i32` handles and `i64` words. -/
abbrev ConsWEv := WEv (ConsOp (BitVec 64)) (BitVec 32)

variable {ts : List FnType}

/-- Calls of `accept(h)` and `accept_all()`. -/
def consWDecAsk (ix : ConsWImports) (e : (ifaceSig ts).Op) : Option ConsWEv :=
  if e.1.val = ix.accept then (i32Arg e.2.1).map .accept
  else if ix.acceptAll = some e.1.val then some .acceptAll
  else none

/-- Answered calls of `nil()`, `cons(a, b)` and `word(x)` returning a handle. -/
def consWDecAns (ix : ConsWImports) (e : (ifaceSig ts).Op) (v : (ifaceSig ts).Ar e) :
    Option ConsWEv := do
  let r ← retI32 v
  if e.1.val = ix.word then return .write (.atom (← i64Arg e.2.1)) [] r
  else if e.1.val = ix.nil then
    if e.2.1 = [] then return .write .nil [] r else none
  else if e.1.val = ix.cons then return .write .cons (← i32Pair e.2.1) r
  else none

/-- **The writer language of a module** through the cons API (store semantics). -/
noncomputable def moduleConsWLang (P : Profile) (m : Module) (ix : ConsWImports)
    (pol : Policy (BitVec 32)) : Set (SExp2 (BitVec 64)) :=
  writerLang (consW (BitVec 64)) pol (moduleTraces P m (consWDecAsk ix) (consWDecAns ix))

/-- The writer language through the cons API over the fixed environments `Envs`. -/
noncomputable def moduleConsWFixedLang (P : Profile) (m : Module) (ix : ConsWImports)
    (pol : Policy (BitVec 32)) (Envs : Set (Env (BitVec 32) (SExp2 (BitVec 64)))) :
    Set (SExp2 (BitVec 64)) :=
  fixedLang (consW (BitVec 64)) pol Envs (moduleTraces P m (consWDecAsk ix) (consWDecAns ix))

/-! ## The n-ary writer API -/

/-- Import indices of the n-ary writer API: `lists` are the list constructors (of any fixed
arity: their children are their arguments). -/
structure SxWImports where
  word : Nat
  lists : List Nat
  accept : Nat
  acceptAll : Option Nat := none

/-- N-ary writer events over `i32` handles and `i64` words. -/
abbrev SxWEv := WEv (SxOp (BitVec 64)) (BitVec 32)

/-- Calls of `accept(h)` and `accept_all()`. -/
def sxWDecAsk (ix : SxWImports) (e : (ifaceSig ts).Op) : Option SxWEv :=
  if e.1.val = ix.accept then (i32Arg e.2.1).map .accept
  else if ix.acceptAll = some e.1.val then some .acceptAll
  else none

/-- Answered calls of `word(x)` and `list_k(c₁, …, c_k)` returning a handle. -/
def sxWDecAns (ix : SxWImports) (e : (ifaceSig ts).Op) (v : (ifaceSig ts).Ar e) :
    Option SxWEv := do
  let r ← retI32 v
  if e.1.val = ix.word then return .write (.atom (← i64Arg e.2.1)) [] r
  else if e.1.val ∈ ix.lists then return .write .list (← i32Args e.2.1) r
  else none

/-- **The writer language of a module** through the n-ary API (store semantics). -/
noncomputable def moduleSxWLang (P : Profile) (m : Module) (ix : SxWImports)
    (pol : Policy (BitVec 32)) : Set (SExp (BitVec 64)) :=
  writerLang (sexpW (BitVec 64)) pol (moduleTraces P m (sxWDecAsk ix) (sxWDecAns ix))

/-- The writer language through the n-ary API over the fixed environments `Envs`. -/
noncomputable def moduleSxWFixedLang (P : Profile) (m : Module) (ix : SxWImports)
    (pol : Policy (BitVec 32)) (Envs : Set (Env (BitVec 32) (SExp (BitVec 64)))) :
    Set (SExp (BitVec 64)) :=
  fixedLang (sexpW (BitVec 64)) pol Envs (moduleTraces P m (sxWDecAsk ix) (sxWDecAns ix))

/-! ## Assume/guarantee specifications -/

/-- **The assume/guarantee specification of a writer API** in the fixed environment `ρ`, for
the sentinel `s`: answered writes return `s` or a handle denoting in `ρ` the tree built in `ρ`;
`accept(h)` names a handle whose meaning in `ρ`, if any, is in `L`. -/
def writerISpec {E : Sig.{0}} {Op X : Type} (W : Writer Op X) (s : Option (BitVec 32))
    (dAsk : E.Op → Option (WEv Op (BitVec 32)))
    (dAns : (e : E.Op) → E.Ar e → Option (WEv Op (BitVec 32)))
    (ρ : Env (BitVec 32) X) (L : Set X) : ISpec E where
  pre e := ∀ h, dAsk e = some (.accept h) → ∀ t, ρ h = some t → t ∈ L
  post e v := ∀ op args r, dAns e v = some (.write op args r) →
    s = some r ∨ ∃ t, W.built ρ op args = some t ∧ ρ r = some t

/-- Atoms (words) of dotted S-expressions. -/
def atoms2 : Set (SExp2 (BitVec 64)) := {x | ∃ w, x = .atom w}

/-- Atoms (words) of S-expressions. -/
def atoms : Set (SExp (BitVec 64)) := {x | ∃ w, x = .atom w}

end Silmaril.Wasm.Game.HandleAccept.Writers

namespace Silmaril.Wasm.Game.HandleAccept.Writers

open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Accept.Handle Silmaril.Formats Silmaril.Formats.Api

/-! ## Structural invariants -/

/-- **A write closed in `S`**: whatever trees of `S` its arguments denote, the call builds a
tree of `S` (if any). -/
def WriteClosed {Op X H : Type} (W : Writer Op X) (S : Set X) (op : Op) (args : List H) :
    Prop :=
  ∀ ts y, ts.length = args.length → W.build op ts = some y → (∀ z ∈ ts, z ∈ S) → y ∈ S

/-- Every list node of an S-expression has a number of children in `K`. -/
def ListArities {α : Type} (K : Set Nat) : SExp α → Prop
  | .atom _ => True
  | .list n cs => n ∈ K ∧ ∀ i, ListArities K (cs i)

/-- The arities of the list constructors of an import list: the numbers of parameters of the
imports in `ix.lists`. -/
def sxArities (ix : SxWImports) (ts : List FnType) : Set Nat :=
  {n | ∃ j ∈ ix.lists, ∃ hj : j < ts.length, (ts.get ⟨j, hj⟩).params.length = n}

end Silmaril.Wasm.Game.HandleAccept.Writers

module

public import Silmaril.Wasm.Game.HandleAccept.Defs

/-!
# The n-ary S-expression reader API of core Wasm modules

The `count`/`child` reader API (`Silmaril.Formats.Api.sexpR`) over `i32` handles and `i64`
words, decoded from instance plays (`Silmaril.Wasm.Game.HandleAccept.playEvents`). Imports, by
index (`SxRImports`):

* `kind : [i32] → [i32]`: `0` atom, `1` list; any other code is an ill-typed answer, decoded as
  an answer that is never correct for `kind` (`SxA.handle`);
* `count : [i32] → [i32]`: the number of children, read as an **unsigned** 32-bit number;
* `child : [i32 i32] → [i32]`: the child at an **unsigned** index;
* `word : [i32] → [i64]`: the atom of a handle;
* `accept : [i32] → []`.

No `items(h) -> list<i32>` import: a list of handles would pass through memory, which instance
plays do not carry. Reads are decoded from answer moves (`sxDecAns`: the query from the
arguments, the answer from the returned values; a trap or an exception is no event), accepts
from ask moves (`sxDecAsk`). `sxDecAns` is `sxDecRead` mapped to `REv.read`, so it never yields
an `accept`.

`moduleSExpLang` is the reader language of a module's instance, and `sexpISpec ix ρ L` the
assume/guarantee import specification in a fixed environment `ρ`: answers are correct reads in
`ρ`, `accept` names a handle denoting a member of `L`; its `GameSat` obligation gives soundness
(`Thms`).

New definitions (no source).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.Nary

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game
  Silmaril.Accept.Handle Silmaril.Formats Silmaril.Formats.Api Silmaril.Wasm.Game.HandleAccept
open Silmaril.Wasm.Logic.Strategy (ISpec)

/-- Import indices of the n-ary reader API. -/
structure SxRImports where
  kind : Nat
  count : Nat
  child : Nat
  word : Nat
  accept : Nat

/-- N-ary reader events over `i32` handles and `i64` words. -/
abbrev SxEv := REv (SxQ (BitVec 32)) (SxA (BitVec 64) (BitVec 32)) (BitVec 32)

/-- Exactly two `i32` arguments. -/
def i32Two : List Val → Option (BitVec 32 × BitVec 32)
  | [.num ⟨.int .i32, a⟩, .num ⟨.int .i32, b⟩] => some (a, b)
  | _ => none

/-- The answer of `kind`: `0` atom, `1` list; other codes are ill-typed answers. -/
def sxKindAns (k : BitVec 32) : SxA (BitVec 64) (BitVec 32) :=
  if k = 0 then .isList false else if k = 1 then .isList true else .handle k

variable {ts : List FnType}

/-- Calls of `accept(h)`. -/
def sxDecAsk (ix : SxRImports) (e : (ifaceSig ts).Op) : Option SxEv :=
  if e.1.val = ix.accept then (i32Arg e.2.1).map .accept else none

/-- The query and answer of an answered `kind`, `count`, `child` or `word` call. -/
def sxDecRead (ix : SxRImports) (e : (ifaceSig ts).Op) (v : (ifaceSig ts).Ar e) :
    Option (SxQ (BitVec 32) × SxA (BitVec 64) (BitVec 32)) := do
  let vs ← ansVals v
  if e.1.val = ix.kind then return (.kind (← i32Arg e.2.1), sxKindAns (← i32Res vs))
  else if e.1.val = ix.count then return (.count (← i32Arg e.2.1), .count (← i32Res vs).toNat)
  else if e.1.val = ix.child then
    let (h, i) ← i32Two e.2.1
    return (.child h i.toNat, .handle (← i32Res vs))
  else if e.1.val = ix.word then return (.atom (← i32Arg e.2.1), .atom (← i64Res vs))
  else none

/-- Answers of `kind`, `count`, `child` and `word`, as read events. -/
def sxDecAns (ix : SxRImports) (e : (ifaceSig ts).Op) (v : (ifaceSig ts).Ar e) :
    Option SxEv :=
  (sxDecRead ix e v).map fun qa => .read qa.1 qa.2

/-- **The reader language of a module** through the n-ary API: the trees its instance accepts
in some environment of `Envs`, for the profile `P`. -/
noncomputable def moduleSExpLang (P : Profile) (m : Module) (ix : SxRImports)
    (pol : OnBadRead (SxQ (BitVec 32)) (SxA (BitVec 64) (BitVec 32))) (oa : OnInvalid)
    (Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) (SExp (BitVec 64)))) :
    Set (SExp (BitVec 64)) :=
  readerLang (sexpR (BitVec 64) (BitVec 32)) pol oa Envs
    (handleTraces ((Verify.instOf m).strategy P (Verify.instOf m).store) (some .enter)
      (sxDecAsk ix) (sxDecAns ix))

/-- **The assume/guarantee specification of an n-ary reader checker** in the fixed environment
`ρ`: answers are correct in `ρ`; `accept` names a member of `L`. -/
def sexpISpec (ix : SxRImports) (ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp (BitVec 64)))
    (L : Set (SExp (BitVec 64))) : ISpec (ifaceSig ts) where
  pre e := ∀ h, sxDecAsk ix e = some (.accept h) → ∀ t, ρ h = some t → t ∈ L
  post e v := ∀ q a, sxDecAns ix e v = some (.read q a) →
    (sexpR (BitVec 64) (BitVec 32)).valid ρ q ∧ (sexpR (BitVec 64) (BitVec 32)).ok ρ q a

end Silmaril.Wasm.Game.HandleAccept.Nary

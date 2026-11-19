module

public import Silmaril.Wasm.Game.HandleAccept.Writer.Defs

/-!
# Tagged-AST APIs of core Wasm modules

Fixed-arity AST imports for a signature with WIT-typed payloads (`Silmaril.Formats.WitSig`)
whose payloads are **scalars**: `bool` (an `i32`, nonzero is true, as the canonical ABI lifts
it), `s32`/`u32` (an `i32`) and `s64`/`u64` (an `i64`). `string`, `list<u8>` and `list<T>`
payloads live in memory and are not decoded here (`ofVal?` is `none` for them).

## Writer

Each tag `t` has an import `t(args…, c₁, …, cₙ) -> i32`: its payload arguments (in the order of
`S.params t`) followed by `i32` child handles. `AstWImports` gives the tag of each import index
(`tagOf`) and the `accept : [i32] → []` index. An answered call returning a handle `r` is the
write `write ⟨t, a⟩ [c₁, …, cₙ] r` of the generic AST writer `Silmaril.Formats.Api.astW`; the
writer checks the arity (`AstSig.arity`), so a call with a wrong number of children is an
invalid write (handled by the policy). `moduleAstWLang` is the writer language.

## Reader

`AstRImports`: `tag : [i32] → [i32, p₁, …]` returns a tag code (decoded by `tagOfCode`) followed
by the payload scalars of that tag (extra results are ignored, so one import type can serve
tags with different payloads); `count : [i32] → [i32]` (unsigned), `child : [i32 i32] → [i32]`
(unsigned index), `accept : [i32] → []`. Answers that do not decode are no event (the module
learns nothing it may rely on). `moduleAstLang` is the reader language of
`Silmaril.Formats.Api.astR`, and `astISpec` its assume/guarantee specification in a fixed
environment, as for the cons and n-ary readers.

New definitions (no source).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.Ast

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game
  Silmaril.Accept.Handle Silmaril.Formats Silmaril.Formats.Api Silmaril.Wasm.Game.HandleAccept
  Silmaril.Wasm.Game.HandleAccept.Writers
open Silmaril.Wasm.Logic.Strategy (ISpec)

/-! ## Scalar payloads -/

/-- The payload value of a core value, for scalar payload types. -/
def ofVal? : (p : PTy) → Val → Option p.Val
  | .bool, .num ⟨.int .i32, b⟩ => some (decide (b ≠ 0))
  | .s32, .num ⟨.int .i32, b⟩ => some (Int32.ofBitVec b)
  | .u32, .num ⟨.int .i32, b⟩ => some (UInt32.ofBitVec b)
  | .s64, .num ⟨.int .i64, b⟩ => some (Int64.ofBitVec b)
  | .u64, .num ⟨.int .i64, b⟩ => some (UInt64.ofBitVec b)
  | _, _ => none

/-- A payload vector from a prefix of core values, with the remaining values. -/
def ofVals? : (ps : List PTy) → List Val → Option (PTy.Vals ps × List Val)
  | [], vs => some ((), vs)
  | p :: ps, v :: vs => do
      let a ← ofVal? p v
      let (as, rest) ← ofVals? ps vs
      return ((a, as), rest)
  | _ :: _, [] => none

variable {S : WitSig} {ts : List FnType}

/-! ## Writer -/

/-- Import indices of an AST writer API. -/
structure AstWImports (S : WitSig) where
  tagOf : Nat → Option S.Tag
  accept : Nat

/-- AST writer events over `i32` handles. -/
abbrev AstWEv (S : WitSig) := WEv (Σ t, S.toAstSig.Arg t) (BitVec 32)

/-- Calls of `accept(h)`. -/
def astWDecAsk (ix : AstWImports S) (e : (ifaceSig ts).Op) : Option (AstWEv S) :=
  if e.1.val = ix.accept then (i32Arg e.2.1).map .accept else none

/-- Answered calls of `t(args…, c₁, …, cₙ)` returning a handle. -/
def astWDecAns (ix : AstWImports S) (e : (ifaceSig ts).Op) (v : (ifaceSig ts).Ar e) :
    Option (AstWEv S) := do
  let r ← retI32 v
  let t ← ix.tagOf e.1.val
  let (a, rest) ← ofVals? (S.params t) e.2.1
  let cs ← i32Args rest
  return .write ⟨t, a⟩ cs r

/-- **The writer language of a module** through an AST writer API (store semantics). -/
noncomputable def moduleAstWLang (P : Profile) (m : Module) (ix : AstWImports S)
    (pol : Policy (BitVec 32)) : Set (AST S.toAstSig) :=
  writerLang (astW S.toAstSig) pol (moduleTraces P m (astWDecAsk ix) (astWDecAns ix))

/-! ## Reader -/

/-- Import indices of an AST reader API, with the tag codes. -/
structure AstRImports (S : WitSig) where
  tag : Nat
  tagOfCode : BitVec 32 → Option S.Tag
  count : Nat
  child : Nat
  accept : Nat

/-- AST reader events over `i32` handles. -/
abbrev AstEv (S : WitSig) := REv (AstQ (BitVec 32)) (AstA S.toAstSig (BitVec 32)) (BitVec 32)

/-- The tag and payload returned by `tag(h)`: a tag code, then the payload scalars. -/
def decTag (ix : AstRImports S) : List Val → Option (Σ t, S.toAstSig.Arg t)
  | .num ⟨.int .i32, c⟩ :: rest => do
      let t ← ix.tagOfCode c
      let (a, _) ← ofVals? (S.params t) rest
      return ⟨t, a⟩
  | _ => none

/-- Calls of `accept(h)`. -/
def astDecAsk (ix : AstRImports S) (e : (ifaceSig ts).Op) : Option (AstEv S) :=
  if e.1.val = ix.accept then (i32Arg e.2.1).map .accept else none

/-- The query and answer of an answered `tag`, `count` or `child` call. -/
def astDecRead (ix : AstRImports S) (e : (ifaceSig ts).Op) (v : (ifaceSig ts).Ar e) :
    Option (AstQ (BitVec 32) × AstA S.toAstSig (BitVec 32)) := do
  let vs ← ansVals v
  if e.1.val = ix.tag then return (.tag (← i32Arg e.2.1), .tag (← decTag ix vs))
  else if e.1.val = ix.count then return (.count (← i32Arg e.2.1), .count (← i32Res vs).toNat)
  else if e.1.val = ix.child then
    match e.2.1 with
    | [.num ⟨.int .i32, h⟩, .num ⟨.int .i32, i⟩] => return (.child h i.toNat, .handle (← i32Res vs))
    | _ => none
  else none

/-- Answers of `tag`, `count` and `child`, as read events. -/
def astDecAns (ix : AstRImports S) (e : (ifaceSig ts).Op) (v : (ifaceSig ts).Ar e) :
    Option (AstEv S) :=
  (astDecRead ix e v).map fun qa => .read qa.1 qa.2

/-- **The reader language of a module** through an AST reader API. -/
noncomputable def moduleAstLang (P : Profile) (m : Module) (ix : AstRImports S)
    (pol : OnBadRead (AstQ (BitVec 32)) (AstA S.toAstSig (BitVec 32))) (oa : OnInvalid)
    (Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) (AST S.toAstSig))) :
    Set (AST S.toAstSig) :=
  readerLang (astR S.toAstSig (BitVec 32)) pol oa Envs
    (handleTraces ((Verify.instOf m).strategy P (Verify.instOf m).store) (some .enter)
      (astDecAsk ix) (astDecAns ix))

/-- **The assume/guarantee specification of an AST reader checker** in the fixed environment
`ρ`: answers are correct in `ρ`; `accept` names a member of `L`. -/
def astISpec (ix : AstRImports S) (ρ : Silmaril.Accept.Handle.Env (BitVec 32) (AST S.toAstSig))
    (L : Set (AST S.toAstSig)) : ISpec (ifaceSig ts) where
  pre e := ∀ h, astDecAsk ix e = some (.accept h) → ∀ t, ρ h = some t → t ∈ L
  post e v := ∀ q a, astDecAns ix e v = some (.read q a) →
    (astR S.toAstSig (BitVec 32)).valid ρ q ∧ (astR S.toAstSig (BitVec 32)).ok ρ q a

end Silmaril.Wasm.Game.HandleAccept.Ast

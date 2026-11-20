module

public import Silmaril.Wasm.Game.HandleAccept.Writer.Defs

/-!
# Binary-tree (`Tree2`) APIs of core Wasm modules

Binary trees `Silmaril.Formats.Tree2 (BitVec 64)`: atoms (`i64` words) and `cons` pairs, with
no distinguished `nil`.

## Writer

The writer `Silmaril.Formats.Api.pairW` (cons without `nil`). Imports (`PairWImports`):
`word : [i64] → [i32]`, `cons : [i32 i32] → [i32]`, `accept : [i32] → []` and optionally
`accept_all : [] → []`. Events are decoded as for the cons writer
(`Silmaril.Wasm.Game.HandleAccept.Writers.consWDecAns`): an answered call returning one `i32`
is a write, `accept(h)` and `accept_all()` are observed when asked. `moduleTree2WLang` and
`moduleTree2WFixedLang` are the writer languages (store semantics and fixed environments).

## Reader

`Silmaril.Formats.Api` has no reader for `Tree2`; `tree2R` is one, in the style of
`Silmaril.Formats.Api.consR`: `isAtom(h)` (a boolean), `word(h)` (the atom of a handle),
`left(h)` and `right(h)` (handles denoting the two halves of a pair). Imports (`T2RImports`):
`isAtom : [i32] → [i32]` (`0` pair, `1` atom; any other code is an ill-typed answer, decoded as
an answer that is never correct for `isAtom`), `left`, `right : [i32] → [i32]`,
`word : [i32] → [i64]` and `accept : [i32] → []`. `moduleTree2Lang` is the reader language of a
module, and `tree2ISpec ix ρ L` its assume/guarantee specification in the fixed environment `ρ`,
as for the cons and n-ary readers.

New definitions (no source).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.Tree2

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game
  Silmaril.Accept.Handle Silmaril.Formats Silmaril.Formats.Api Silmaril.Wasm.Game.HandleAccept
  Silmaril.Wasm.Game.HandleAccept.Writers
open Silmaril.Wasm.Logic.Strategy (ISpec)

/-! ## Writer -/

/-- Import indices of the binary-tree writer API. -/
structure PairWImports where
  word : Nat
  cons : Nat
  accept : Nat
  acceptAll : Option Nat := none

/-- Binary-tree writer events over `i32` handles and `i64` words. -/
abbrev PairWEv := WEv (PairOp (BitVec 64)) (BitVec 32)

variable {ts : List FnType}

/-- Calls of `accept(h)` and `accept_all()`. -/
def pairWDecAsk (ix : PairWImports) (e : (ifaceSig ts).Op) : Option PairWEv :=
  if e.1.val = ix.accept then (i32Arg e.2.1).map .accept
  else if ix.acceptAll = some e.1.val then some .acceptAll
  else none

/-- Answered calls of `word(x)` and `cons(a, b)` returning a handle. -/
def pairWDecAns (ix : PairWImports) (e : (ifaceSig ts).Op) (v : (ifaceSig ts).Ar e) :
    Option PairWEv := do
  let r ← retI32 v
  if e.1.val = ix.word then return .write (.atom (← i64Arg e.2.1)) [] r
  else if e.1.val = ix.cons then return .write .cons (← i32Pair e.2.1) r
  else none

/-- **The writer language of a module** through the binary-tree API (store semantics). -/
noncomputable def moduleTree2WLang (P : Profile) (m : Module) (ix : PairWImports)
    (pol : Policy (BitVec 32)) : Set (Tree2 (BitVec 64)) :=
  writerLang (pairW (BitVec 64)) pol (moduleTraces P m (pairWDecAsk ix) (pairWDecAns ix))

/-- The writer language through the binary-tree API over the fixed environments `Envs`. -/
noncomputable def moduleTree2WFixedLang (P : Profile) (m : Module) (ix : PairWImports)
    (pol : Policy (BitVec 32)) (Envs : Set (Env (BitVec 32) (Tree2 (BitVec 64)))) :
    Set (Tree2 (BitVec 64)) :=
  fixedLang (pairW (BitVec 64)) pol Envs (moduleTraces P m (pairWDecAsk ix) (pairWDecAns ix))

/-! ## Reader -/

/-- Binary-tree queries. -/
inductive T2Q (H : Type) where
  | isAtom (h : H)
  | word (h : H)
  | left (h : H)
  | right (h : H)

/-- Binary-tree answers. -/
inductive T2A (α : Type) (H : Type) where
  | isAtom (b : Bool)
  | word (a : α)
  | handle (h : H)

/-- Whether a binary tree is an atom. -/
def isAtom {α : Type} : Tree2 α → Bool
  | .atom _ => true
  | .cons _ _ => false

/-- **The binary-tree reader.** -/
def tree2R (α : Type) (H : Type) : Reader (T2Q H) (T2A α H) H (Tree2 α) where
  valid ρ
    | .isAtom h => ∃ x, ρ h = some x
    | .word h => ∃ a, ρ h = some (.atom a)
    | .left h => ∃ x y, ρ h = some (.cons x y)
    | .right h => ∃ x y, ρ h = some (.cons x y)
  ok ρ q a := match q, a with
    | .isAtom h, .isAtom b => ∃ x, ρ h = some x ∧ b = isAtom x
    | .word h, .word a => ρ h = some (.atom a)
    | .left h, .handle h' => ∃ x y, ρ h = some (.cons x y) ∧ ρ h' = some x
    | .right h, .handle h' => ∃ x y, ρ h = some (.cons x y) ∧ ρ h' = some y
    | _, _ => False

/-- Import indices of the binary-tree reader API. -/
structure T2RImports where
  isAtom : Nat
  left : Nat
  right : Nat
  word : Nat
  accept : Nat

/-- Binary-tree reader events over `i32` handles and `i64` words. -/
abbrev T2Ev := REv (T2Q (BitVec 32)) (T2A (BitVec 64) (BitVec 32)) (BitVec 32)

/-- The answer of `isAtom`: `0` pair, `1` atom; other codes are ill-typed answers. -/
def isAtomAns (k : BitVec 32) : T2A (BitVec 64) (BitVec 32) :=
  if k = 0 then .isAtom false else if k = 1 then .isAtom true else .handle k

/-- Calls of `accept(h)`. -/
def t2DecAsk (ix : T2RImports) (e : (ifaceSig ts).Op) : Option T2Ev :=
  if e.1.val = ix.accept then (i32Arg e.2.1).map .accept else none

/-- The query and answer of an answered `isAtom`, `left`, `right` or `word` call. -/
def t2DecRead (ix : T2RImports) (e : (ifaceSig ts).Op) (v : (ifaceSig ts).Ar e) :
    Option (T2Q (BitVec 32) × T2A (BitVec 64) (BitVec 32)) := do
  let h ← i32Arg e.2.1
  let vs ← ansVals v
  if e.1.val = ix.isAtom then return (.isAtom h, isAtomAns (← i32Res vs))
  else if e.1.val = ix.left then return (.left h, .handle (← i32Res vs))
  else if e.1.val = ix.right then return (.right h, .handle (← i32Res vs))
  else if e.1.val = ix.word then return (.word h, .word (← i64Res vs))
  else none

/-- Answers of `isAtom`, `left`, `right` and `word`, as read events. -/
def t2DecAns (ix : T2RImports) (e : (ifaceSig ts).Op) (v : (ifaceSig ts).Ar e) :
    Option T2Ev :=
  (t2DecRead ix e v).map fun qa => .read qa.1 qa.2

/-- **The reader language of a module** through the binary-tree API. -/
noncomputable def moduleTree2Lang (P : Profile) (m : Module) (ix : T2RImports)
    (pol : OnBadRead (T2Q (BitVec 32)) (T2A (BitVec 64) (BitVec 32))) (oa : OnInvalid)
    (Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) (Tree2 (BitVec 64)))) :
    Set (Tree2 (BitVec 64)) :=
  readerLang (tree2R (BitVec 64) (BitVec 32)) pol oa Envs
    (handleTraces ((Verify.instOf m).strategy P (Verify.instOf m).store) (some .enter)
      (t2DecAsk ix) (t2DecAns ix))

/-- **The assume/guarantee specification of a binary-tree reader checker** in the fixed
environment `ρ`: answers are correct in `ρ`; `accept` names a member of `L`. -/
def tree2ISpec (ix : T2RImports)
    (ρ : Silmaril.Accept.Handle.Env (BitVec 32) (Tree2 (BitVec 64)))
    (L : Set (Tree2 (BitVec 64))) : ISpec (ifaceSig ts) where
  pre e := ∀ h, t2DecAsk ix e = some (.accept h) → ∀ t, ρ h = some t → t ∈ L
  post e v := ∀ q a, t2DecAns ix e v = some (.read q a) →
    (tree2R (BitVec 64) (BitVec 32)).valid ρ q ∧ (tree2R (BitVec 64) (BitVec 32)).ok ρ q a

end Silmaril.Wasm.Game.HandleAccept.Tree2

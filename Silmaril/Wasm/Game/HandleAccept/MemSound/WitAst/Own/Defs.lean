module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Defs
public import Silmaril.Wasm.Resource.Handle.Defs

/-!
# Owned resource handles as typed AST payloads: definitions

A payload field of type `own<r>` (`PTy.own r`) carries a **resource handle** that the module
**moves** into the tree. Its meaning in the tree is the resource's **representation** (`Nat`,
`Wit.storedEnv`), read from an **explicit resource table**; the handle index itself is never a
semantic value. A `borrow<r>` field is **rejected** (a borrow cannot outlive the call that lent
it: `PTy.Val (.borrow r) = Empty`, so such a payload has no value and its call no event);
`future`, `stream` and `error-context` are not payload types (pending async semantics).

## The resource table

* `ResEntry`: an entry `(ty, rep, live)`: its resource type number, its representation and
  whether the module still owns it (REF `ResourceHandle`, `own = True`, in a `Table`);
* `RT := BitVec 32 → Option ResEntry`: the table of the module, by `i32` handle index;
* `RT.lookup rt r h`: the representation of `h` when it is a **live** handle **of resource type
  `r`** (a dead, missing or foreign-type handle has none: REF `lift_own`
  `trap_if(h.rt is not rt)`, and a removed handle is not in the table);
* `RT.killAll rt hs`: the table after moving the handles `hs` (REF `lift_own` removes the
  handle: here its entry is kept, dead);
* `RT.Le rt rt₀`: every live handle of `rt` is live in `rt₀` with the same type and
  representation (a table reached by moves only).

## Raw and resolved payloads

The decoder `Callout.witNode` reads memory only, and memory gives a handle no meaning. A
signature `S` is therefore read through its **raw signature** `rawSig S`: every **top-level**
`own r` field of a payload vector becomes `u32` (`ownRaw`), the `i32` table index of the
canonical ABI. The raw payload is then resolved in a table:

* `resolve1 rt t v`, `resolveVals rt ps vs`: every `own r` field looked up (`RT.lookup`); other
  fields unchanged. An `own` nested inside a list, option, record, … is not resolved.
  `resolveOp` checks the entire original schema, including inactive cases and empty lists;
* `movedVals ps vs`: the handles a raw payload moves, in field order;
* `resolveOp S rt op`: the resolved operation and the table after the move; none when a handle
  does not resolve or **the payload moves the same handle twice** (the canonical ABI lifts the
  fields in order and the second lift of a removed handle traps).

## The resource-table writer host

`ownHost W S pol rt₀` runs a **raw** writer trace (`WEv` over the raw operations of `S`): its
state `OwnState` is the resource table and the writer state of `W` (`WState`). A raw write is
resolved in the **current** table (`OwnStep.move`): its handles are consumed and the resolved
write is answered as `WStep W pol none` answers it. A write that does not resolve (a dead,
missing or foreign-type handle, in particular **a handle moved before**, or a double move inside
one payload) is an **invalid write**, following `pol.onWrite` as every other invalid write:
`trap` (no answer, no step), `fail` (the sentinel, `OwnStep.badFail`), `ub` (`OwnStep.badChaos`).
Other events (`accept`, `enter`, …) are answered by `WStep` with the table unchanged.
`ownLang W S pol rt₀ T` is its language: acceptance is **trace-dependent** (the table at a call
is `rt₀` with every earlier move consumed) and depends on `rt₀` only through the moved handles
(`Own.run_congr`).

`viaRT W S rt₀` is the **stateless** reading: a raw write denotes what its operation resolved in
the *initial* table `rt₀` builds. It agrees with `ownHost` on traces that move no handle twice
(`Own.ownLang_eq_of_linear`), and bounds it for policies without undefined writes
(`Own.ownLang_subset_via`), which is how module proofs reuse the stateless writer contracts.

## Ownership protocol

`tmoved es` lists the handles moved along a raw trace; `ownGives es` reads them as `give`
events of the ownership protocol `Silmaril.Wasm.Resource.obProto` (the program transfers an
owned handle away), after the `take` events of the handles it owns initially
(`Own.linear_of_ob`: a trace accepted by the protocol moves no handle twice).

## The examples `ownMod`, `twiceMod`

`ownSig`: one tag `res` (tag `0`) with one `own<0>` payload and no children; its raw form reads a
`u32`. Imports `0 wit.node : [i32 i32 i32 i32] → [i32]`, `1 wit.accept : [i32] → []`; one page;
export `run : [] → []`. The handle `1` is owned by the module **in the resource table**: it is
the explicit environment `rt₀` (e.g. received by an earlier call), not a constant of the tree.

```wat
(func $run (local $a i32) (local $b i32)                ;; ownMod
  (i32.store (i32.const 16) (i32.const 1))               ;; the handle 1 at [16, 20)
  (call $accept (call $node (i32.const 0) (i32.const 16) (i32.const 0) (i32.const 0))))
```

It builds `res(rep)` (`resTree rep`) where `rep` is the representation of the live `own<0>`
handle `1` of `rt₀`, and nothing when `rt₀` has none. `twiceMod` moves the same handle twice
(two `node(0, 16, 0, 0)` calls, the first result in `$a`) and accepts the second result: the
second move is an invalid write.

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Accept.Handle Silmaril.Formats
  Silmaril.Formats.Api Silmaril.Wasm.Game.HandleAccept.MemSound.Hi

/-! ## The resource table -/

/-- **An entry of the resource table**: the resource type number, the representation, and
whether the module still owns the handle. -/
structure ResEntry where
  ty : Nat
  rep : Nat
  live : Bool
  deriving DecidableEq, Repr

/-- The entry after its handle moved out of the module. -/
def ResEntry.kill (e : ResEntry) : ResEntry := { e with live := false }

/-- **A resource table**: the entry of each `i32` handle index. -/
abbrev RT := BitVec 32 → Option ResEntry

/-- **The representation of a live handle of resource type `r`.** -/
def RT.lookup (rt : RT) (r : Nat) (h : BitVec 32) : Option Nat :=
  (rt h).bind fun e => if e.live = true ∧ e.ty = r then some e.rep else none

/-- The table after moving the handles `hs` out of the module. -/
def RT.killAll (rt : RT) (hs : List (BitVec 32)) : RT :=
  fun h => if h ∈ hs then (rt h).map ResEntry.kill else rt h

/-- `rt` is reached from `rt₀` by moves: its live handles are live in `rt₀`, with the same type
and representation. -/
def RT.Le (rt rt₀ : RT) : Prop := ∀ r h rep, rt.lookup r h = some rep → rt₀.lookup r h = some rep

/-- `h` is not a live handle of `rt` (of any resource type). -/
def RT.Dead (rt : RT) (h : BitVec 32) : Prop := ∀ r, rt.lookup r h = none

/-- A table with the single live handle `h` of type `r` and representation `rep`. -/
def RT.single (h : BitVec 32) (r rep : Nat) : RT :=
  fun h' => if h' = h then some ⟨r, rep, true⟩ else none

/-! ## Raw payloads -/

/-- **The raw form of a payload type**: a top-level owned handle is read as its `u32` table
index. -/
def ownRaw : PTy → PTy
  | .own _ => .u32
  | t => t

/-- **The raw signature**: every top-level `own` payload field read as `u32`. -/
abbrev rawSig (S : WitSig) : WitSig := ⟨S.Tag, fun t => (S.params t).map ownRaw, S.arity⟩

/-- **A raw payload value resolved in the table**: an owned handle is the representation of its
live entry of the right resource type; other values are unchanged. -/
def resolve1 (rt : RT) : (t : PTy) → (ownRaw t).Val → Option t.Val
  | .own r, i => rt.lookup r (UInt32.toBitVec i)
  | .bool, v | .s32, v | .u32, v | .s64, v | .u64, v | .string, v | .list _, v | .s8, v
  | .u8, v | .s16, v | .u16, v | .f32, v | .f64, v | .char, v | .fixedList _ _, v
  | .record _, v | .tuple _, v | .variant _, v | .enum _, v | .option _, v | .result _ _, v
  | .flags _, v | .borrow _, v => some v

/-- The handle a raw payload value moves, if it is a top-level owned handle. -/
def moved1 : (t : PTy) → (ownRaw t).Val → List (BitVec 32)
  | .own _, i => [UInt32.toBitVec i]
  | _, _ => []

/-- **A raw payload vector resolved in the table.** -/
def resolveVals (rt : RT) : (ps : List PTy) → PTy.Vals (ps.map ownRaw) → Option (PTy.Vals ps)
  | [], _ => some ()
  | t :: ps, (v, vs) => (resolve1 rt t v).bind fun a => (resolveVals rt ps vs).map fun as => (a, as)

/-- **The handles a raw payload vector moves**, in field order. -/
def movedVals : (ps : List PTy) → PTy.Vals (ps.map ownRaw) → List (BitVec 32)
  | [], _ => []
  | t :: ps, (v, vs) => moved1 t v ++ movedVals ps vs

variable (S : WitSig)

/-- Raw operations of `S`: a tag with its raw payload (the operations of `rawSig S`). -/
abbrev ROp := Σ t : S.Tag, PTy.Vals ((S.params t).map ownRaw)

/-- Resolved operations of `S` (the operations of `S`). -/
abbrev Op := Σ t : S.Tag, PTy.Vals (S.params t)

/-- The handles a raw operation moves. -/
def movedOp (op : ROp S) : List (BitVec 32) := movedVals (S.params op.1) op.2

/-- **A raw operation resolved in the table**, with the table after the move: none when the
schema is unsupported, a handle does not resolve, or the payload moves a handle twice.
`Checked.Defs` exposes typed errors for these cases. -/
def resolveOp (rt : RT) (op : ROp S) : Option (Op S × RT) :=
  if checkPTys .ownFields (S.params op.1) = .ok () ∧ (movedOp S op).Nodup then
    (resolveVals rt (S.params op.1) op.2).map fun a => (⟨op.1, a⟩, rt.killAll (movedOp S op))
  else none

/-- The handles moved along a raw writer trace (by every write, valid or not). -/
def tmoved : List (WEv (ROp S) (BitVec 32)) → List (BitVec 32)
  | [] => []
  | .write op _ _ :: es => movedOp S op ++ tmoved es
  | _ :: es => tmoved es

/-- The moves of a raw trace as ownership-protocol events: each moved handle is given away. -/
def ownGives (es : List (WEv (ROp S) (BitVec 32))) : List (Silmaril.Wasm.Resource.OEv (BitVec 32)) :=
  (tmoved S es).map .give

/-! ## The resource-table writer host -/

/-- The control events of a writer trace in another operation type (none for writes). -/
def WEv.ctl {Op₁ Op₂ H : Type} : WEv Op₁ H → Option (WEv Op₂ H)
  | .write _ _ _ => none
  | .accept h => some (.accept h)
  | .acceptErr h b => some (.acceptErr h b)
  | .acceptAll => some .acceptAll
  | .acceptBatch k => some (.acceptBatch k)
  | .enter => some .enter

/-- The state of the resource-table writer host: the table and the writer state. -/
structure OwnState (X : Type) where
  rt : RT
  w : WState (BitVec 32) X

variable {S} {X : Type}

/-- **The resource-table writer response relation** (store semantics, no fixed environment). -/
inductive OwnStep (W : Writer (Op S) X) (pol : Policy (BitVec 32)) :
    OwnState X → WEv (ROp S) (BitVec 32) → OwnState X → Set X → Prop where
  /-- A raw write resolved in the current table: its handles are consumed. -/
  | move {rt rt' : RT} {w w' : WState (BitVec 32) X} {rop : ROp S} {op : Op S}
      {args : List (BitVec 32)} {r : BitVec 32} {A : Set X} :
      resolveOp S rt rop = some (op, rt') → WStep W pol none w (.write op args r) w' A →
      OwnStep W pol ⟨rt, w⟩ (.write rop args r) ⟨rt', w'⟩ A
  /-- An unresolved write returns the sentinel (`fail`). -/
  | badFail {rt : RT} {w : WState (BitVec 32) X} {rop : ROp S} {args : List (BitVec 32)}
      {r : BitVec 32} :
      resolveOp S rt rop = none → w.phase = .live → pol.onWrite = .fail →
      pol.sentinel = some r → OwnStep W pol ⟨rt, w⟩ (.write rop args r) ⟨rt, w⟩ ∅
  /-- An unresolved write is undefined behaviour (`ub`). -/
  | badChaos {rt : RT} {w : WState (BitVec 32) X} {rop : ROp S} {args : List (BitVec 32)}
      {r : BitVec 32} :
      resolveOp S rt rop = none → w.phase = .live → pol.onWrite = .ub →
      OwnStep W pol ⟨rt, w⟩ (.write rop args r) ⟨rt, { w with phase := .chaos }⟩ Set.univ
  /-- After undefined behaviour every event is allowed and accepts everything. -/
  | chaos {rt : RT} {w : WState (BitVec 32) X} {e : WEv (ROp S) (BitVec 32)} :
      w.phase = .chaos → OwnStep W pol ⟨rt, w⟩ e ⟨rt, w⟩ Set.univ
  /-- Other events, answered by the writer host; the table is unchanged. -/
  | other {rt : RT} {w w' : WState (BitVec 32) X} {e : WEv (ROp S) (BitVec 32)}
      {e' : WEv (Op S) (BitVec 32)} {A : Set X} :
      WEv.ctl e = some e' → WStep W pol none w e' w' A → OwnStep W pol ⟨rt, w⟩ e ⟨rt, w'⟩ A

/-- **The resource-table writer host** from the initial table `rt₀`. -/
def ownHost (W : Writer (Op S) X) (pol : Policy (BitVec 32)) (rt₀ : RT) :
    Silmaril.Accept.Host (WEv (ROp S) (BitVec 32)) X (OwnState X) :=
  ⟨⟨rt₀, WState.init⟩, OwnStep W pol⟩

/-- **The resource-table writer language** of a set of raw traces. -/
def ownLang (W : Writer (Op S) X) (pol : Policy (BitVec 32)) (rt₀ : RT)
    (T : Set (List (WEv (ROp S) (BitVec 32)))) : Set X :=
  (ownHost W pol rt₀).lang T

/-- **The stateless reading** in the initial table: a raw operation builds what its resolution in
`rt₀` builds. -/
def viaRT (W : Writer (Op S) X) (rt₀ : RT) : Writer (ROp S) X :=
  ⟨fun rop ts => (resolveOp S rt₀ rop).bind fun p => W.build p.1 ts⟩

/-! ## The examples -/

/-- The tag of `ownSig`. -/
inductive OwnTag where
  | res
  deriving DecidableEq, Repr

/-- **Owned resources**: `res` carries one `own<0>` and no children. -/
def ownSig : WitSig where
  Tag := OwnTag
  params
    | .res => [.own 0]
  arity
    | .res => .fixed 0

/-- The tag numbers: `0` is `res`. -/
def ownTagOf (tg : BitVec 32) : Option ownSig.Tag := if tg = 0 then some OwnTag.res else none

/-- The tag numbers of the raw signature (the same tags). -/
def ownRawTagOf (tg : BitVec 32) : Option (rawSig ownSig).Tag := ownTagOf tg

/-- The body of `run` (`ownMod`). -/
def ownBody : List Instr :=
  [.intConst .i32 16, .intConst .i32 1, .intStore .i32 none ⟨0⟩ ⟨0, 0⟩,
   .intConst .i32 0, .intConst .i32 16, .intConst .i32 0, .intConst .i32 0, .call ⟨0⟩,
   .call ⟨1⟩]

/-- **The module `ownMod`.** -/
def ownMod : Module where
  types := [Ast.tyTag, tyAcc, tyRun]
  imports := [⟨"wit", "node", .func ⟨0⟩⟩, ⟨"wit", "accept", .func ⟨1⟩⟩]
  memories := [⟨.i32, ⟨1, none⟩⟩]
  funcs := [⟨⟨2⟩, [.i32, .i32], ownBody⟩]
  exports := [⟨"run", .func ⟨2⟩⟩]

/-- The body of `run` (`twiceMod`): the handle `1` moved twice. -/
def twiceBody : List Instr :=
  [.intConst .i32 16, .intConst .i32 1, .intStore .i32 none ⟨0⟩ ⟨0, 0⟩,
   .intConst .i32 0, .intConst .i32 16, .intConst .i32 0, .intConst .i32 0, .call ⟨0⟩,
   .localSet ⟨0⟩,
   .intConst .i32 0, .intConst .i32 16, .intConst .i32 0, .intConst .i32 0, .call ⟨0⟩,
   .call ⟨1⟩]

/-- **The module `twiceMod`.** -/
def twiceMod : Module where
  types := [Ast.tyTag, tyAcc, tyRun]
  imports := [⟨"wit", "node", .func ⟨0⟩⟩, ⟨"wit", "accept", .func ⟨1⟩⟩]
  memories := [⟨.i32, ⟨1, none⟩⟩]
  funcs := [⟨⟨2⟩, [.i32, .i32], twiceBody⟩]
  exports := [⟨"run", .func ⟨2⟩⟩]

/-- **The resource node `res(rep)`**: the tree holding the resource's representation. -/
def resTree (rep : Nat) : AST ownSig.toAstSig :=
  AST.node (S := ownSig.toAstSig) OwnTag.res (rep, ()) []

/-- The raw operation `res` with the handle `h`. -/
def rawRes (h : UInt32) : ROp ownSig := ⟨OwnTag.res, (h, ())⟩

/-- **The trees `ownMod` may accept** in the table `rt₀`: `res(rep)` for the representation of
the live `own<0>` handle `1`. -/
def ownL (rt₀ : RT) : Set (AST ownSig.toAstSig) := {t | ∃ rep, rt₀.lookup 0 1 = some rep ∧ t = resTree rep}

end Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own

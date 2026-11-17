module

public import Silmaril.Wasm.Examples.MemberCheck.Defs
public import Silmaril.Wasm.Logic.Words.Defs
public import Silmaril.Logic.SAT.Carrier.Defs
public import Silmaril.Wasm.Verify.FnSpec.Defs
public import Silmaril.Wasm.Logic.VC.Defs
public import Silmaril.Wasm.Acceptor.Alloc.Defs
public import Silmaril.Wasm.Acceptor.Abi.Defs

/-!
# The SAT model-witness acceptor as a core Wasm module: definitions

`prog` is a Core 3.0 module meant to be wrapped as a component whose exports take their lists
through the canonical ABI (`(canon lift … (memory 0) (realloc …))`):

| export | type | meaning |
|---|---|---|
| `memory` | memory, 16 pages (1 MiB), maximum 16 | the canonical-ABI memory |
| `cabi_realloc(old, old_size, align, new_size) -> ptr` | `[i32 i32 i32 i32] → [i32]` | bump allocator |
| `check-stream(pp, pl, mp, ml) -> i32` | `[i32 i32 i32 i32] → [i32]` | `satStream` of the words `[pp, pp + 4 pl)` with the model words `[mp, mp + 4 ml)` |
| `check-nested(pp, pl, mp, ml) -> i32` | `[i32 i32 i32 i32] → [i32]` | `satNested` of the `pl` pairs `(ptr, len)` at `pp`, with the model words `[mp, mp + 4 ml)` |

**The allocator** is the acceptor kit's `Silmaril.Wasm.Acceptor.reallocFunc` (shared with
`LratAccept` and `FarkasAccept`). It keeps a heap pointer `top` (global `0`, initially
`heapBase = 16`) below `memBytes = 2²⁰`. `cabi_realloc` ignores the old block (the canonical ABI
only allocates fresh lists) and returns `p = align_up(top, align)`; when `top ≤ p ≤ memBytes` and
`new_size ≤ memBytes - p` it sets `top := p + new_size`, otherwise it sets `top := memBytes` and returns
`memBytes`, so a nonempty list then fails the canonical ABI's bounds check (a trap) and an empty one
sits at the end of memory. It never traps and never lowers `top`, so the blocks it returns within
memory are disjoint and lie above every earlier block. Both checks reset `top` to `heapBase` before
returning: the arguments of a call are dead after it.

**The checks** decide `satStream` and `satNested` (`Silmaril.Logic.SAT.Carrier`) of the words
in memory: literal words are those other than `0` and `Int32.MIN`; the model must consist of
literal words whose negations it does not contain; every clause must contain a model word. They
scan each clause literal against every model word, `O(|problem| · |model|)` loads. Within the
bounds of their preconditions they never trap.

**The specifications** (`Silmaril.Wasm.Verify.FnSpec`, proved in
`Silmaril.Wasm.Examples.SatAccept.Thms`):

* `reallocSpec`: `cabi_realloc` returns `(reallocRes t al n).1` and only sets the heap pointer,
  to `(reallocRes t al n).2`; `ReallocOk` is the non-overlap property of the result;
* `streamSpec`, `nestedSpec`: the checks answer `satStream`/`satNested` of the words in
  memory (`checkPost`), with the loop invariants `streamInv`, `nestedInv` stated with the loops'
  running values `modelPre`, `streamRun`, `clauseOk`;
* `specMT`, `specPrep`, `specInst`: the validated type, the allocation and the instance.

New code (no source).
-/

@[expose] public section

namespace Silmaril.Wasm.Examples.SatAccept

open Silmaril.Wasm Silmaril.Wasm.Logic.Words

/-- The memory size in bytes (16 pages). -/
abbrev memBytes : Nat := 1048576

/-- The initial (and reset) value of the heap pointer. -/
abbrev heapBase : Nat := 16

/-- The two checks, with the memory and the heap pointer (global `0`), as text; the allocator
is added by `prog`. -/
def checks : Module := wat3! r#"
(module
  (memory (export "memory") 16 16)
  (global $top (mut i32) (i32.const 16))
  (func $checkStream (export "check-stream")
    (param $pp i32) (param $pl i32) (param $mp i32) (param $ml i32) (result i32)
    (local $i i32) (local $j i32) (local $r i32) (local $hit i32) (local $x i32) (local $y i32)
    (local $has i32)
    (local.set $r (i32.const 1))
    ;; the model: literal words, no word with its negation
    (block $mdone (loop $mnext
      (br_if $mdone (i32.eq (local.get $i) (local.get $ml)))
      (local.set $x (i32.load (i32.add (local.get $mp) (i32.shl (local.get $i) (i32.const 2)))))
      (local.set $r (i32.and (local.get $r)
        (i32.and (i32.ne (local.get $x) (i32.const 0))
                 (i32.ne (local.get $x) (i32.const 0x80000000)))))
      (local.set $y (i32.sub (i32.const 0) (local.get $x)))
      (local.set $has (i32.const 0))
      (local.set $j (i32.const 0))
      (block $ndone (loop $nnext
        (br_if $ndone (i32.eq (local.get $j) (local.get $ml)))
        (local.set $has (i32.or (local.get $has)
          (i32.eq (i32.load (i32.add (local.get $mp) (i32.shl (local.get $j) (i32.const 2))))
                  (local.get $y))))
        (local.set $j (i32.add (local.get $j) (i32.const 1)))
        (br $nnext)))
      (local.set $r (i32.and (local.get $r) (i32.eqz (local.get $has))))
      (local.set $i (i32.add (local.get $i) (i32.const 1)))
      (br $mnext)))
    ;; the stream: no Int32.MIN, every terminated clause hit by the model
    (local.set $i (i32.const 0))
    (block $sdone (loop $snext
      (br_if $sdone (i32.eq (local.get $i) (local.get $pl)))
      (local.set $x (i32.load (i32.add (local.get $pp) (i32.shl (local.get $i) (i32.const 2)))))
      (if (i32.eqz (local.get $x))
        (then
          (local.set $r (i32.and (local.get $r) (local.get $hit)))
          (local.set $hit (i32.const 0)))
        (else
          (local.set $r (i32.and (local.get $r) (i32.ne (local.get $x) (i32.const 0x80000000))))
          (local.set $j (i32.const 0))
          (block $hdone (loop $hnext
            (br_if $hdone (i32.eq (local.get $j) (local.get $ml)))
            (local.set $hit (i32.or (local.get $hit)
              (i32.eq (i32.load (i32.add (local.get $mp) (i32.shl (local.get $j) (i32.const 2))))
                      (local.get $x))))
            (local.set $j (i32.add (local.get $j) (i32.const 1)))
            (br $hnext)))))
      (local.set $i (i32.add (local.get $i) (i32.const 1)))
      (br $snext)))
    ;; terminated: empty, or the last word is 0
    (if (i32.ne (local.get $pl) (i32.const 0))
      (then (local.set $r (i32.and (local.get $r)
        (i32.eqz (i32.load (i32.add (local.get $pp)
          (i32.shl (i32.sub (local.get $pl) (i32.const 1)) (i32.const 2)))))))))
    (global.set $top (i32.const 16))
    (local.get $r))
  (func $checkNested (export "check-nested")
    (param $pp i32) (param $pl i32) (param $mp i32) (param $ml i32) (result i32)
    (local $i i32) (local $j i32) (local $k i32) (local $r i32) (local $hit i32) (local $x i32)
    (local $y i32) (local $has i32) (local $cp i32) (local $cl i32)
    (local.set $r (i32.const 1))
    ;; the model: literal words, no word with its negation
    (block $mdone (loop $mnext
      (br_if $mdone (i32.eq (local.get $i) (local.get $ml)))
      (local.set $x (i32.load (i32.add (local.get $mp) (i32.shl (local.get $i) (i32.const 2)))))
      (local.set $r (i32.and (local.get $r)
        (i32.and (i32.ne (local.get $x) (i32.const 0))
                 (i32.ne (local.get $x) (i32.const 0x80000000)))))
      (local.set $y (i32.sub (i32.const 0) (local.get $x)))
      (local.set $has (i32.const 0))
      (local.set $j (i32.const 0))
      (block $ndone (loop $nnext
        (br_if $ndone (i32.eq (local.get $j) (local.get $ml)))
        (local.set $has (i32.or (local.get $has)
          (i32.eq (i32.load (i32.add (local.get $mp) (i32.shl (local.get $j) (i32.const 2))))
                  (local.get $y))))
        (local.set $j (i32.add (local.get $j) (i32.const 1)))
        (br $nnext)))
      (local.set $r (i32.and (local.get $r) (i32.eqz (local.get $has))))
      (local.set $i (i32.add (local.get $i) (i32.const 1)))
      (br $mnext)))
    ;; the clauses: literal words only, each hit by the model
    (local.set $i (i32.const 0))
    (block $cdone (loop $cnext
      (br_if $cdone (i32.eq (local.get $i) (local.get $pl)))
      (local.set $cp (i32.load (i32.add (local.get $pp) (i32.shl (local.get $i) (i32.const 3)))))
      (local.set $cl (i32.load (i32.add (local.get $pp)
        (i32.add (i32.shl (local.get $i) (i32.const 3)) (i32.const 4)))))
      (local.set $hit (i32.const 0))
      (local.set $k (i32.const 0))
      (block $ldone (loop $lnext
        (br_if $ldone (i32.eq (local.get $k) (local.get $cl)))
        (local.set $x (i32.load (i32.add (local.get $cp) (i32.shl (local.get $k) (i32.const 2)))))
        (local.set $r (i32.and (local.get $r)
          (i32.and (i32.ne (local.get $x) (i32.const 0))
                   (i32.ne (local.get $x) (i32.const 0x80000000)))))
        (local.set $j (i32.const 0))
        (block $hdone (loop $hnext
          (br_if $hdone (i32.eq (local.get $j) (local.get $ml)))
          (local.set $hit (i32.or (local.get $hit)
            (i32.eq (i32.load (i32.add (local.get $mp) (i32.shl (local.get $j) (i32.const 2))))
                    (local.get $x))))
          (local.set $j (i32.add (local.get $j) (i32.const 1)))
          (br $hnext)))
        (local.set $k (i32.add (local.get $k) (i32.const 1)))
        (br $lnext)))
      (local.set $r (i32.and (local.get $r) (local.get $hit)))
      (local.set $i (i32.add (local.get $i) (i32.const 1)))
      (br $cnext)))
    (global.set $top (i32.const 16))
    (local.get $r)))
"#

/-- **The SAT acceptor module**: the acceptor kit's allocator
(`Silmaril.Wasm.Acceptor.reallocFunc`, on global `0` for `memBytes` bytes) as function `0`,
then the two checks of `checks` as functions `1` and `2`. -/
def prog : Module where
  types := checks.types
  globals := checks.globals
  memories := checks.memories
  funcs := Silmaril.Wasm.Acceptor.reallocFunc ⟨0⟩ 0 memBytes :: checks.funcs
  exports := [⟨"memory", .memory ⟨0⟩⟩, ⟨"cabi_realloc", .func ⟨0⟩⟩, ⟨"check-stream", .func ⟨1⟩⟩,
    ⟨"check-nested", .func ⟨2⟩⟩]

/-! ## What the checks compute -/

open Silmaril.Logic.SAT.Carrier

/-- The `n` words at byte `p` (`Silmaril.Wasm.Logic.Words.words`). -/
abbrev wordsAt (B : ByteArray) (p n : Nat) : List (BitVec 32) := words B p n

/-- The nested input of `n` pairs `(ptr, len)` at byte `p`: the words of each pair's block (the
acceptor kit's `list<list<s32>>` reader `Silmaril.Wasm.Acceptor.nestedAt`). -/
abbrev nestedAt (B : ByteArray) (p n : Nat) : Nested := Silmaril.Wasm.Acceptor.nestedAt B p n

/-- Every block of the nested input lies in memory (`Silmaril.Wasm.Acceptor.NestedIn`). -/
abbrev NestedIn (B : ByteArray) (p n : Nat) : Prop := Silmaril.Wasm.Acceptor.NestedIn B p n

/-! ## The loops' running values

What the loops of the checks compute after reading a prefix: `modelPre M n` (the model loop,
after `n` model words), `streamRun M xs` (the stream loop, the running result and the running
clause hit after the words `xs`), `clauseOk M c` (one clause of the nested loop). -/

/-- The model loop after its first `n` words: each is a literal word whose negation (`0 - x`)
is not among the model words. -/
def modelPre (M : List S32) (n : Nat) : Bool :=
  (M.take n).all fun x => LitWord x && !M.contains (-x)

/-- One word of the stream loop, on the running result and the running clause hit: `0` closes
the clause (it must be hit), any other word must not be `Int32.MIN` and is a literal of the
clause (a hit when it is a model word). -/
def streamStep (M : List S32) : Bool × Bool → S32 → Bool × Bool
  | (r, hit), x => if x = 0 then (r && hit, false) else (r && x != BitVec.intMin 32, hit || M.contains x)

/-- The stream loop after the words `xs`, from the result `true` and no hit. -/
def streamRun (M : List S32) (xs : List S32) : Bool × Bool := xs.foldl (streamStep M) (true, false)

/-- One clause of the nested loop: literal words only, one of them a model word. -/
def clauseOk (M : List S32) (c : List S32) : Bool := c.all LitWord && c.any M.contains

/-! ## The specifications -/

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Verify
open Silmaril.Wasm.Logic.VC (globalVal setGlobalIdx)
open Silmaril.Wasm.Numerics (bool32)

/-- `align_up(top, align)` as `cabi_realloc` computes it: `(top + (align - 1)) & -align`
(modulo `2³²`, for every `align`, including `0` and non-powers of two). -/
def alignUp (t al : BitVec 32) : BitVec 32 := (t + (al - 1)) &&& (0 - al)

/-- **What `cabi_realloc` returns and leaves in `top`**, from `top = t`, alignment `al` and size
`n`: the aligned pointer `p = alignUp t al` and `top := p + n` when `t ≤ p` and `p + n ≤ memBytes`
(as naturals), otherwise `memBytes` and `top := memBytes`. -/
def reallocRes (t al n : BitVec 32) : BitVec 32 × BitVec 32 :=
  if t.toNat ≤ (alignUp t al).toNat ∧ (alignUp t al).toNat + n.toNat ≤ memBytes then
    (alignUp t al, alignUp t al + n)
  else (BitVec.ofNat 32 memBytes, BitVec.ofNat 32 memBytes)

/-- The non-overlap property of an allocation from `top = t` of `n` bytes returning `p` and
leaving `top = t'` (as naturals): either the block `[p, p + n)` lies in memory above `t` and
`t' = p + n`, or `p = t' = memBytes`. -/
def ReallocOk (t n p t' : BitVec 32) : Prop :=
  (t.toNat ≤ p.toNat ∧ p.toNat + n.toNat ≤ memBytes ∧ t'.toNat = p.toNat + n.toNat) ∨
    (p.toNat = memBytes ∧ t'.toNat = memBytes)

/-- **The specification of `cabi_realloc`**, on the input `(old, old_size, align, new_size, t)`
with `t` the value of the heap pointer (global `0`): it returns `(reallocRes t al n).1` and the
store changes only in global `0`, which becomes `(reallocRes t al n).2`. -/
def reallocSpec : FnSpec (BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32) where
  args := fun (o, os, al, n, _) => [.i32 o, .i32 os, .i32 al, .i32 n]
  pre := fun (_, _, _, _, t) mi s => globalVal s mi 0 = some (.i32 t)
  post := fun (_, _, al, n, t) mi s res s' =>
    res = [.i32 (reallocRes t al n).1] ∧ s' = setGlobalIdx s mi 0 (.i32 (reallocRes t al n).2)

/-- The precondition of the checks: memory `0` holds `memBytes` bytes `B` meeting `pre B`, and
global `0` exists. -/
def checkPre (pre : ByteArray → Prop) (mi : ModuleInst) (s : Store Nat) : Prop :=
  (∃ ma mt B, MemAt s mi ma mt B ∧ B.size = memBytes ∧ pre B) ∧ (globalVal s mi 0).isSome

/-- The postcondition of the checks: global `0` (the heap pointer) is reset to `heapBase`, the
rest of the store is unchanged, and the result is `1` when `ans B` holds and `0` otherwise. -/
def checkPost (ans : ByteArray → Bool) (mi : ModuleInst) (s : Store Nat) (res : List Val)
    (s' : Store Nat) : Prop :=
  s' = setGlobalIdx s mi 0 (.i32 (BitVec.ofNat 32 heapBase)) ∧
    ∀ ma mt B, MemAt s mi ma mt B → res = [.i32 (if ans B then 1 else 0)]

/-- The bytes of memory `0` of the instance `mi` in the store `s` (empty when there is none). -/
def mem0 (s : Store Nat) (mi : ModuleInst) : ByteArray :=
  match (mi.mems[0]?).bind fun a => s.mems[a]? with
  | some m => m.bytes
  | none => ByteArray.empty

/-- The locals of the checks, as `i32` values. -/
def locs (L : List (BitVec 32)) : List (Option Val) := L.map fun v => some (.i32 v)

/-- The loop invariants of `check-stream` (in pre-order: the model loop, its scan, the stream
loop, its scan). The store is unchanged, there are no loop parameters, and the locals
`pp pl mp ml i j r hit x y has` hold the running values of `modelPre` and `streamRun` on the
words `P` of the stream and `M` of the model. -/
def streamInv (x : BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32) (mi : ModuleInst)
    (s₀ : Store Nat) : Silmaril.Wasm.Logic.VC.Invs Nat := fun k s f a =>
  let (pp, pl, mp, ml) := x
  s = s₀ ∧ a = [] ∧ f.module = mi ∧ ∃ i j r hit x y has : BitVec 32,
    f.locals = locs [pp, pl, mp, ml, i, j, r, hit, x, y, has] ∧
      let B := mem0 s₀ mi
      let P := wordsAt B pp.toNat pl.toNat
      let M := wordsAt B mp.toNat ml.toNat
      match k with
      | 0 => i.toNat ≤ ml.toNat ∧ hit = 0 ∧ r = bool32 (modelPre M i.toNat)
      | 1 => i.toNat < ml.toNat ∧ j.toNat ≤ ml.toNat ∧ hit = 0 ∧ x = M.getD i.toNat 0 ∧
          y = -x ∧ r = bool32 (modelPre M i.toNat && LitWord x) ∧
          has = bool32 ((M.take j.toNat).contains y)
      | 2 => i.toNat ≤ pl.toNat ∧ r = bool32 (modelPre M ml.toNat && (streamRun M (P.take i.toNat)).1) ∧
          hit = bool32 (streamRun M (P.take i.toNat)).2
      | _ => i.toNat < pl.toNat ∧ j.toNat ≤ ml.toNat ∧ x = P.getD i.toNat 0 ∧ x ≠ 0 ∧
          r = bool32 (modelPre M ml.toNat && (streamRun M (P.take i.toNat)).1 &&
            x != BitVec.intMin 32) ∧
          hit = bool32 ((streamRun M (P.take i.toNat)).2 || (M.take j.toNat).contains x)

/-- **The specification of `check-stream`**: with the stream words `[pp, pp + 4 pl)` and the
model words `[mp, mp + 4 ml)` in memory, it answers `satStream` and resets the heap pointer. -/
def streamSpec : FnSpec (BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32) where
  args := fun (pp, pl, mp, ml) => [.i32 pp, .i32 pl, .i32 mp, .i32 ml]
  pre := fun (pp, pl, mp, ml) => checkPre fun B =>
    pp.toNat + 4 * pl.toNat ≤ B.size ∧ mp.toNat + 4 * ml.toNat ≤ B.size
  post := fun (pp, pl, mp, ml) => checkPost fun B =>
    satStream (wordsAt B pp.toNat pl.toNat) (wordsAt B mp.toNat ml.toNat)
  inv := streamInv

/-- The loop invariants of `check-nested` (in pre-order: the model loop, its scan, the clause
loop, the literal loop, its scan). The locals are `pp pl mp ml i j k r hit x y has cp cl`; `N`
is the nested input and `C` the words of clause `i`. -/
def nestedInv (x : BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32) (mi : ModuleInst)
    (s₀ : Store Nat) : Silmaril.Wasm.Logic.VC.Invs Nat := fun n s f a =>
  let (pp, pl, mp, ml) := x
  s = s₀ ∧ a = [] ∧ f.module = mi ∧ ∃ i j k r hit x y has cp cl : BitVec 32,
    f.locals = locs [pp, pl, mp, ml, i, j, k, r, hit, x, y, has, cp, cl] ∧
      let B := mem0 s₀ mi
      let N := nestedAt B pp.toNat pl.toNat
      let M := wordsAt B mp.toNat ml.toNat
      let C := wordsAt B cp.toNat cl.toNat
      match n with
      | 0 => i.toNat ≤ ml.toNat ∧ r = bool32 (modelPre M i.toNat)
      | 1 => i.toNat < ml.toNat ∧ j.toNat ≤ ml.toNat ∧ x = M.getD i.toNat 0 ∧
          y = -x ∧ r = bool32 (modelPre M i.toNat && LitWord x) ∧
          has = bool32 ((M.take j.toNat).contains y)
      | 2 => i.toNat ≤ pl.toNat ∧ r = bool32 (modelPre M ml.toNat && (N.take i.toNat).all (clauseOk M))
      | 3 => i.toNat < pl.toNat ∧ cp = wd B (pp.toNat + 8 * i.toNat) ∧
          cl = wd B (pp.toNat + 8 * i.toNat + 4) ∧ k.toNat ≤ cl.toNat ∧
          r = bool32 (modelPre M ml.toNat && (N.take i.toNat).all (clauseOk M) &&
            (C.take k.toNat).all LitWord) ∧
          hit = bool32 ((C.take k.toNat).any M.contains)
      | _ => i.toNat < pl.toNat ∧ cp = wd B (pp.toNat + 8 * i.toNat) ∧
          cl = wd B (pp.toNat + 8 * i.toNat + 4) ∧ k.toNat < cl.toNat ∧ j.toNat ≤ ml.toNat ∧
          x = C.getD k.toNat 0 ∧
          r = bool32 (modelPre M ml.toNat && (N.take i.toNat).all (clauseOk M) &&
            (C.take (k.toNat + 1)).all LitWord) ∧
          hit = bool32 ((C.take k.toNat).any M.contains || (M.take j.toNat).contains x)

/-- **The specification of `check-nested`**: with the nested input of `pl` pairs at `pp` in
memory (`NestedIn`) and the model words `[mp, mp + 4 ml)`, it answers `satNested` and resets
the heap pointer. -/
def nestedSpec : FnSpec (BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32) where
  args := fun (pp, pl, mp, ml) => [.i32 pp, .i32 pl, .i32 mp, .i32 ml]
  pre := fun (pp, pl, mp, ml) => checkPre fun B =>
    NestedIn B pp.toNat pl.toNat ∧ mp.toNat + 4 * ml.toNat ≤ B.size
  post := fun (pp, pl, mp, ml) => checkPost fun B =>
    satNested (nestedAt B pp.toNat pl.toNat) (wordsAt B mp.toNat ml.toNat)
  inv := nestedInv

/-! ## The instance -/

open Silmaril.Wasm.Validation Silmaril.Wasm.Game

/-- The validated type of `prog`. -/
def specMT : CModuleType := (validate? prog).getD ⟨[], []⟩

/-- The spec's allocation of `prog`. -/
def specPrep : Config Nat × Option FuncIdx :=
  (prepare? evalConst? (importStore (CExternType.funcs specMT.imports)) prog
    (importAddrs specMT)).getD (⟨{}, {}, []⟩, none)

/-- The function type `[i32 i32 i32 i32] → [i32]` of the three exports. -/
def fnType4 : FnType :=
  ⟨[.num (.int .i32), .num (.int .i32), .num (.int .i32), .num (.int .i32)], [.num (.int .i32)]⟩

/-- The scalar instance of `prog`: the exports `cabi_realloc`, `check-stream`, `check-nested` at
function addresses `0`, `1`, `2`. -/
def specInst : ScalarInstance where
  imports := []
  exports := [fnType4, fnType4, fnType4]
  addrs := [0, 1, 2]
  store := specPrep.1.store

end Silmaril.Wasm.Examples.SatAccept

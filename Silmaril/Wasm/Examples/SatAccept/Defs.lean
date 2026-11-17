module

public import Silmaril.Wasm.Examples.MemberCheck.Defs
public import Silmaril.Wasm.Logic.Words.Defs
public import Silmaril.Logic.SAT.Carrier.Defs

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

**The allocator** keeps a heap pointer `top` (global `0`, initially `heapBase = 16`) below
`memBytes = 2²⁰`. `cabi_realloc` ignores the old block (the canonical ABI only allocates fresh
lists) and returns `p = align_up(top, align)`; when `top ≤ p ≤ memBytes` and `new_size ≤
memBytes - p` it sets `top := p + new_size`, otherwise it sets `top := memBytes` and returns
`memBytes`, so a nonempty list then fails the canonical ABI's bounds check (a trap) and an
empty one sits at the end of memory. It never traps and never lowers `top`, so the blocks it
returns within memory are disjoint and lie above every earlier block. Both checks reset `top`
to `heapBase` before returning: the arguments of a call are dead after it.

**The checks** decide `satStream` and `satNested` (`Silmaril.Logic.SAT.Carrier`) of the words
in memory: literal words are those other than `0` and `Int32.MIN`; the model must consist of
literal words whose negations it does not contain; every clause must contain a model word. They
scan each clause literal against every model word, `O(|problem| · |model|)` loads. Within the
bounds of their preconditions they never trap.

New code (no source).
-/

@[expose] public section

namespace Silmaril.Wasm.Examples.SatAccept

open Silmaril.Wasm Silmaril.Wasm.Logic.Words

/-- The memory size in bytes (16 pages). -/
abbrev memBytes : Nat := 1048576

/-- The initial (and reset) value of the heap pointer. -/
abbrev heapBase : Nat := 16

/-- **The SAT acceptor module.** -/
def prog : Module := wat3! r#"
(module
  (memory (export "memory") 16 16)
  (global $top (mut i32) (i32.const 16))
  (func $realloc (export "cabi_realloc")
    (param $old i32) (param $osz i32) (param $al i32) (param $nsz i32) (result i32)
    (local $p i32)
    (local.set $p
      (i32.and (i32.add (global.get $top) (i32.sub (local.get $al) (i32.const 1)))
               (i32.sub (i32.const 0) (local.get $al))))
    (if (i32.and (i32.and (i32.ge_u (local.get $p) (global.get $top))
                          (i32.le_u (local.get $p) (i32.const 1048576)))
                 (i32.le_u (local.get $nsz) (i32.sub (i32.const 1048576) (local.get $p))))
      (then (global.set $top (i32.add (local.get $p) (local.get $nsz))))
      (else (global.set $top (i32.const 1048576))
            (local.set $p (i32.const 1048576))))
    (local.get $p))
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

/-! ## What the checks compute -/

open Silmaril.Logic.SAT.Carrier

/-- The `n` words at byte `p` (`Silmaril.Wasm.Logic.Words.words`). -/
abbrev wordsAt (B : ByteArray) (p n : Nat) : List (BitVec 32) := words B p n

/-- The nested input of `n` pairs `(ptr, len)` at byte `p`: the words of each pair's block. -/
def nestedAt (B : ByteArray) (p n : Nat) : Nested :=
  (List.range n).map fun i => wordsAt B (wd B (p + 8 * i)).toNat (wd B (p + 8 * i + 4)).toNat

/-- Every block of the nested input lies in memory. -/
def NestedIn (B : ByteArray) (p n : Nat) : Prop :=
  p + 8 * n ≤ B.size ∧ ∀ i < n,
    (wd B (p + 8 * i)).toNat + 4 * (wd B (p + 8 * i + 4)).toNat ≤ B.size

end Silmaril.Wasm.Examples.SatAccept

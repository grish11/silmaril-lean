module

public import Silmaril.Formats.JsonBytes.Defs
public import Silmaril.Wasm.Examples.Verified.Defs

/-! # A concrete Wasm acceptor for a JSON subset: definitions

`prog` is a core Wasm module (quoted with `wat3!`, so it is silmaril-lean's `Module` AST) with
one exported function `accept(ptr: i32, len: i32) -> i32`. It scans the bytes
`[ptr, ptr + len)` of memory `0` once (`i32.load8_u` in a loop) and runs a six-state automaton
with no data-dependent branches: each byte is classified arithmetically (whitespace, `-`, `0`,
`1`–`9`, other), and the next state is read out of three packed `i32` constants. It returns `1`
iff the final state is accepting.

**The language it decides is a subset of JSON, not all of JSON**: `intText`, the JSON texts that
are a single integer, `ws* -? (0 | [1-9][0-9]*) ws*` (RFC 8259 §2 whitespace, §6 `int` with an
optional minus sign), with no fraction, exponent, string, literal, array or object.

* `cls`, `tbl`, `stepN`, `runN`: the automaton, as a Lean function on byte values.
* `IntLex`, `NumLex`, `intText`: the subset, as a Mathlib `Language UInt8`; `Rest q` is what
  remains to be read from state `q`.
* `bd B a`: the byte at `a` of a memory `B` (Core's one-byte `Memory.load`); `bytesN` and
  `segment` are the bytes `[ptr, ptr + len)`.
* `spec`: the `FnSpec` of `accept`: on in-bounds arguments it returns `1` iff the automaton
  accepts the segment, and memory is unchanged (`FnSpec.mem`).

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasm.Examples.JsonAccept

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Verify Silmaril.Wasm.Logic.Words
open Silmaril.Formats.JsonBytes

/-! ## The automaton and the subset -/

/-- Byte classes: whitespace `0`, `-` `1`, `0` `2`, `1`–`9` `3`, other `4`. -/
def cls (b : Nat) : Nat :=
  if b = 32 ∨ b = 9 ∨ b = 10 ∨ b = 13 then 0 else if b = 45 then 1 else if b = 48 then 2
  else if 49 ≤ b ∧ b ≤ 57 then 3 else 4

/-- The transitions. States: `0` leading whitespace, `1` after `-`, `2` after the integer
`0`, `3` inside `[1-9][0-9]*`, `4` trailing whitespace, `5` dead. -/
def tbl : Nat → Nat → Nat
  | 0, 0 => 0 | 0, 1 => 1 | 0, 2 => 2 | 0, 3 => 3
  | 1, 2 => 2 | 1, 3 => 3
  | 2, 0 => 4
  | 3, 0 => 4 | 3, 2 => 3 | 3, 3 => 3
  | 4, 0 => 4
  | _, _ => 5

/-- One step on a byte value. -/
def stepN (q b : Nat) : Nat := tbl q (cls b)

/-- A run on byte values. -/
def runN (q : Nat) (bs : List Nat) : Nat := bs.foldl stepN q

/-- `0`–`9`. -/
def IsDigit (b : UInt8) : Prop := 0x30 ≤ b ∧ b ≤ 0x39

/-- `1`–`9`. -/
def IsDigit19 (b : UInt8) : Prop := 0x31 ≤ b ∧ b ≤ 0x39

/-- RFC 8259 `int`: `0`, or a nonzero digit followed by digits. -/
def IntLex (i : List UInt8) : Prop :=
  i = [0x30] ∨ ∃ d ds, i = d :: ds ∧ IsDigit19 d ∧ ∀ x ∈ ds, IsDigit x

/-- An optional minus sign, then an `int`. -/
def NumLex (v : List UInt8) : Prop := ∃ m i, v = m ++ i ∧ (m = [] ∨ m = [0x2D]) ∧ IntLex i

/-- **The subset**: JSON texts that are one integer, with surrounding whitespace. -/
def intText : Language UInt8 :=
  {w | ∃ a v c, w = a ++ v ++ c ∧ (∀ x ∈ a, IsWsByte x) ∧ NumLex v ∧ (∀ x ∈ c, IsWsByte x)}

/-- What remains to be read from each state. -/
def Rest : Nat → List UInt8 → Prop
  | 0, w => w ∈ intText
  | 1, w => ∃ i c, w = i ++ c ∧ IntLex i ∧ ∀ x ∈ c, IsWsByte x
  | 2, w => ∀ x ∈ w, IsWsByte x
  | 3, w => ∃ ds c, w = ds ++ c ∧ (∀ x ∈ ds, IsDigit x) ∧ ∀ x ∈ c, IsWsByte x
  | 4, w => ∀ x ∈ w, IsWsByte x
  | _, _ => False

/-! ## The module -/

/-- **The acceptor module.** The step reads three packed transition rows: row `r` holds states
`2r` and `2r + 1`, each entry three bits at `3 * (5 * (q mod 2) + class)`. -/
def prog : Module := wat3! r#"
(module
  (memory 1)
  (func $accept (export "accept") (param $p i32) (param $n i32) (result i32)
    (local $i i32) (local $q i32) (local $b i32) (local $c i32)
    (block $done
      (loop $next
        (br_if $done (i32.eq (local.get $i) (local.get $n)))
        (local.set $b (i32.load8_u (i32.add (local.get $p) (local.get $i))))
        (local.set $c
          (i32.sub (i32.const 4)
            (i32.add
              (i32.add
                (i32.mul (i32.or (i32.or (i32.eq (local.get $b) (i32.const 32))
                                         (i32.eq (local.get $b) (i32.const 9)))
                                 (i32.or (i32.eq (local.get $b) (i32.const 10))
                                         (i32.eq (local.get $b) (i32.const 13))))
                         (i32.const 4))
                (i32.mul (i32.eq (local.get $b) (i32.const 45)) (i32.const 3)))
              (i32.add
                (i32.mul (i32.eq (local.get $b) (i32.const 48)) (i32.const 2))
                (i32.lt_u (i32.sub (local.get $b) (i32.const 49)) (i32.const 9))))))
        (local.set $q
          (i32.and
            (i32.shr_u
              (i32.add
                (i32.add
                  (i32.mul (i32.const 727111304) (i32.lt_u (local.get $q) (i32.const 2)))
                  (i32.mul (i32.const 729176940)
                    (i32.sub (i32.lt_u (local.get $q) (i32.const 4))
                             (i32.lt_u (local.get $q) (i32.const 2)))))
                (i32.mul (i32.const 766958444)
                  (i32.sub (i32.const 1) (i32.lt_u (local.get $q) (i32.const 4)))))
              (i32.mul (i32.add (i32.mul (i32.and (local.get $q) (i32.const 1)) (i32.const 5))
                                (local.get $c))
                       (i32.const 3)))
            (i32.const 7)))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $next)))
    (i32.lt_u (i32.sub (local.get $q) (i32.const 2)) (i32.const 3))))
"#

/-- The byte at `a` of the memory `B` (Core's one-byte load). -/
def bd (B : ByteArray) (a : Nat) : BitVec 8 := (Execution.Memory.load B a 1).getD 0

/-- The byte values `[a, a + k)` of `B`. -/
def bytesN (B : ByteArray) (a k : Nat) : List Nat := (List.range k).map fun j => (bd B (a + j)).toNat

/-- The bytes `[a, a + k)` of the memory `B`. -/
def segment (B : ByteArray) (a k : Nat) : List UInt8 := (bytesN B a k).map UInt8.ofNat

/-- **The specification of `accept`**: on in-bounds, non-wrapping arguments, it returns `1` iff
the automaton accepts the segment, else `0`, and leaves memory unchanged. The loop invariant:
the store is unchanged, the locals are `p, n, i, q, b, c`, `i ≤ n`, and `q` is the state after
the first `i` bytes. -/
def spec : FnSpec (BitVec 32 × BitVec 32) :=
  .mem (fun (p, n) => [.i32 p, .i32 n])
    (pre := fun (p, n) B => p.toNat + n.toNat ≤ B.size ∧ p.toNat + n.toNat < 2 ^ 32)
    (fun (p, n) B res =>
      res = [.i32 (if 2 ≤ runN 0 (bytesN B p.toNat n.toNat) ∧ runN 0 (bytesN B p.toNat n.toNat) ≤ 4
        then 1 else 0)])
    (inv := fun (p, n) _ s₀ _ s f a => s = s₀ ∧ a = [] ∧ ∃ i q b c : BitVec 32,
      f.locals = [some (.i32 p), some (.i32 n), some (.i32 i), some (.i32 q), some (.i32 b),
        some (.i32 c)] ∧
      i.toNat ≤ n.toNat ∧
      ∀ ma mt B, MemAt s f.module ma mt B →
        q = BitVec.ofNat 32 (runN 0 (bytesN B p.toNat i.toNat)))

end Silmaril.Wasm.Examples.JsonAccept

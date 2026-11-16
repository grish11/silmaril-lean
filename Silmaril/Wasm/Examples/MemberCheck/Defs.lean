module

public import Silmaril.Wasm.Examples.JsonAccept.Defs
public import Silmaril.Wasm.Game.SpecInst.Defs
public import Silmaril.Wasm.Game.Accept.Export.Defs

/-! # The finite membership checker as a core Wasm module: definitions

`prog` is a core Wasm module with one memory and one exported function
`check(ptr: i32, len: i32) -> i32`. The segment `[ptr, ptr + len)` holds a query: its first byte is
the statement `c`, and the remaining bytes are the assumptions `as`. `check` returns `1` iff
`c ∈ as`, which is the membership (assumption) rule over finite lists of bytes. It scans the
segment once, with no data-dependent branch: at `i = 0` it records `c`, and afterwards it ORs
`byte = c` into the result.

* `memberLang`: the accepted byte strings, `c :: as` with `c ∈ as`.
* `memb`: the same as a Boolean function on byte values.
* `bytes`: its 108-byte binary.
* `spec`: the `FnSpec` of `check`, with its loop invariant.
* `specMT`, `specPrep`, `specInst`: the validated type, the allocation and the instance.

New definitions (no source). `bd`, `bytesN` and `segment` are those of
`Silmaril.Wasm.Examples.JsonAccept`.
-/

@[expose] public section

namespace Silmaril.Wasm.Examples.MemberCheck

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Verify Silmaril.Wasm.Validation
  Silmaril.Wasm.Game Silmaril.Wasm.Logic.Words
open Silmaril.Wasm.Examples.JsonAccept (bd bytesN segment)

/-- The accepted inputs: a statement byte followed by assumption bytes that contain it. -/
def memberLang : Language UInt8 := {w | ∃ c as, w = c :: as ∧ c ∈ as}

instance (w : List UInt8) : Decidable (w ∈ memberLang) :=
  match w with
  | [] => isFalse fun ⟨_, _, h, _⟩ => List.cons_ne_nil _ _ h.symm
  | c :: as => decidable_of_iff (c ∈ as)
      ⟨fun h => ⟨c, as, rfl, h⟩, fun ⟨_, _, h, hm⟩ => by cases h; exact hm⟩

/-- Membership on byte values: the head is among the rest. -/
def memb : List Nat → Bool
  | [] => false
  | c :: as => as.contains c

/-- **The membership checker module.** -/
def prog : Module := wat3! r#"
(module
  (memory 1)
  (func $check (export "check") (param $p i32) (param $n i32) (result i32)
    (local $i i32) (local $c i32) (local $r i32) (local $b i32)
    (block $done
      (loop $next
        (br_if $done (i32.eq (local.get $i) (local.get $n)))
        (local.set $b (i32.load8_u (i32.add (local.get $p) (local.get $i))))
        (local.set $r
          (i32.or (local.get $r)
            (i32.and (i32.ne (local.get $i) (i32.const 0))
                     (i32.eq (local.get $b) (local.get $c)))))
        (local.set $c
          (i32.add (local.get $c) (i32.mul (i32.eq (local.get $i) (i32.const 0)) (local.get $b))))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $next)))
    (local.get $r)))
"#

/-- **The bytes of `prog`**, as silmaril-lean's encoder produces them (`encodeModule_eq`). -/
def bytes : List UInt8 :=
  [0, 97, 115, 109, 1, 0, 0, 0, 1, 7, 1, 96, 2, 127, 127, 1, 127, 3, 2, 1, 0, 5, 3, 1, 0, 1, 7, 9,
    1, 5, 99, 104, 101, 99, 107, 0, 0, 10, 69, 1, 67, 1, 4, 127, 2, 64, 3, 64, 32, 2, 32, 1, 70, 13,
    1, 32, 0, 32, 2, 106, 45, 0, 0, 33, 5, 32, 4, 32, 2, 65, 0, 71, 32, 5, 32, 3, 70, 113, 114, 33,
    4, 32, 3, 32, 2, 65, 0, 70, 32, 5, 108, 106, 33, 3, 32, 2, 65, 1, 106, 33, 2, 12, 0, 11, 11, 32,
    4, 11]

/-- **The specification of `check`**: on in-bounds, non-wrapping arguments it returns `1` iff
the segment's first byte occurs among the rest, else `0`, and leaves memory unchanged. The loop
invariant: the store is unchanged, the locals are `p, n, i, c, r, b`, `i ≤ n`, `c` is the first
byte read (or `0`), and `r` is membership on the first `i` bytes. -/
def spec : FnSpec (BitVec 32 × BitVec 32) :=
  .mem (fun (p, n) => [.i32 p, .i32 n])
    (pre := fun (p, n) B => p.toNat + n.toNat ≤ B.size ∧ p.toNat + n.toNat < 2 ^ 32)
    (fun (p, n) B res => res = [.i32 (if memb (bytesN B p.toNat n.toNat) then 1 else 0)])
    (inv := fun (p, n) _ s₀ _ s f a => s = s₀ ∧ a = [] ∧ ∃ i c r b : BitVec 32,
      f.locals = [some (.i32 p), some (.i32 n), some (.i32 i), some (.i32 c), some (.i32 r),
        some (.i32 b)] ∧
      i.toNat ≤ n.toNat ∧
      ∀ ma mt B, MemAt s f.module ma mt B →
        c = BitVec.ofNat 32 ((bytesN B p.toNat i.toNat).headD 0) ∧
        r = (if memb (bytesN B p.toNat i.toNat) then 1 else 0))

/-- The validated type of `prog`. -/
def specMT : CModuleType := (validate? prog).getD ⟨[], []⟩

/-- The spec's allocation of `prog`. -/
def specPrep : Config Nat × Option FuncIdx :=
  (prepare? evalConst? (importStore (CExternType.funcs specMT.imports)) prog
    (importAddrs specMT)).getD (⟨{}, {}, []⟩, none)

/-- The scalar instance of `prog`. -/
def specInst : ScalarInstance where
  imports := []
  exports := [⟨[.num (.int .i32), .num (.int .i32)], [.num (.int .i32)]⟩]
  addrs := [0]
  store := specPrep.1.store

end Silmaril.Wasm.Examples.MemberCheck

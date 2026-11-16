module

public import Silmaril.Wasm.Wat
public import Silmaril.Wasm.Execution.Core.Exec.InstantiateOnce
public import Silmaril.Wasm.Logic.Words.Defs

/-!
# `is_sorted`: is an `i32` array segment sorted? (program and specification)

`program` is a Core 3.0 module written with silmaril-lean's `wat3!` quotation; its one
function `is_sorted(p, n)` returns `1` if the `n` words at `p, p + 4, …` of memory `0` are
sorted in signed order, else `0`, comparing adjacent words in one loop:

```wat
(func $is_sorted (export "is_sorted") (param $p i32) (param $n i32) (result i32)
  (local $i i32)
  (local.set $i (i32.const 1))
  (block $done
    (loop $top
      (br_if $done (i32.ge_u (local.get $i) (local.get $n)))
      (br_if $done (i32.gt_s (i32.load (p + 4 (i - 1))) (i32.load (p + 4 i))))
      (local.set $i (i32.add (local.get $i) (i32.const 1)))
      (br $top)))
  (i32.ge_u (local.get $i) (local.get $n)))
```

`isSortedSpec a fi` is its total-correctness specification
(`Silmaril.Wasm.Logic.Hoare.TFSpecAt`): if the function instance `fi` is at address `a`, the
arguments are `p, n`, memory `0` of `fi`'s module holds the bytes `B` with
`p + 4 n ≤ |B|` and `p + 4 n < 2^32`, then the call terminates in every run, returns
`1` iff `words B p n` is sorted (`Silmaril.Wasm.Logic.Words.SortedS`) and `0` otherwise, and leaves
the store unchanged. Proofs in `Silmaril.Proofs.WasmSpec.IsSorted`.

The loop shape is the usual adjacent-comparison scan, with an early exit and signed
order. A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.WasmSpec.IsSorted

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Logic.Words
open Silmaril.Wasm.Logic.Hoare (FSpec)

/-- **The module.** -/
def program := wat3! r#"
(module
  (memory (export "memory") 1)
  (func $is_sorted (export "is_sorted") (param $p i32) (param $n i32) (result i32)
    (local $i i32)
    (local.set $i (i32.const 1))
    (block $done
      (loop $top
        (br_if $done (i32.ge_u (local.get $i) (local.get $n)))
        (br_if $done (i32.gt_s
          (i32.load (i32.add (local.get $p)
            (i32.mul (i32.sub (local.get $i) (i32.const 1)) (i32.const 4))))
          (i32.load (i32.add (local.get $p) (i32.mul (local.get $i) (i32.const 4))))))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $top)))
    (i32.ge_u (local.get $i) (local.get $n))))
"#

/-- The store after instantiating the module against no imports (silmaril-lean's
`instantiateOnce?`); `is_sorted` is its function `0`. -/
def store₀ : Store Nat :=
  match instantiateOnce? ({} : Store Nat) program [] with
  | some (s, _, _) => s
  | none => {}

/-- The function `is_sorted`. -/
def isSortedFunc : Func := program.funcs[0]

/-- The loop test: leave when `i ≥ n`. -/
def loopTest : List Instr := [lget 2, lget 1, igeu, brIf 1]

/-- The comparison: leave when `a[i - 1] > a[i]`; else `i := i + 1` and repeat. -/
def loopCmp : List Instr :=
  [lget 0, lget 2, c32 1, isub, c32 4, imul, iadd, iload,
   lget 0, lget 2, c32 4, imul, iadd, iload, igts, brIf 1,
   lget 2, c32 1, iadd, lset 2, br 0]

/-- The loop body, as abstract syntax (checked equal to the quoted one by `rfl`). -/
def loopBody : List Instr := loopTest ++ loopCmp

/-- The function body, as abstract syntax. -/
def body : List Instr := [c32 1, lset 2, while_ loopBody, lget 2, lget 1, igeu]

/-- The answer: `1` if sorted, else `0`. -/
def answer (l : List (BitVec 32)) : BitVec 32 := if SortedS l then 1 else 0

variable {H : Type}

/-- The precondition on the store and the arguments: `fi` is at `a`; the arguments are
`p, n`; memory `0` of `fi`'s module holds `B`, which contains the segment, and the segment's
addresses do not wrap. -/
def Pre (a : Nat) (fi : FuncInst H) (s : Store H) (args : List Val) : Prop :=
  s.funcs[a]? = some fi ∧ ∃ (p n : BitVec 32) (ma : Nat) (mt : MemoryType) (B : ByteArray),
    args = [.i32 p, .i32 n] ∧ MemAt s fi.module ma mt B ∧ p.toNat + 4 * n.toNat ≤ B.size ∧
    p.toNat + 4 * n.toNat < 2 ^ 32

/-- **The specification of `is_sorted`**: the store is unchanged and the result is
`answer (words B p n)`. -/
def isSortedSpec (a : Nat) (fi : FuncInst H) : FSpec H where
  pre := Pre a fi
  post s args s' o := s' = s ∧ ∀ (p n : BitVec 32) (ma : Nat) (mt : MemoryType) (B : ByteArray),
    args = [.i32 p, .i32 n] → MemAt s fi.module ma mt B →
    o = .normal [.i32 (answer (words B p.toNat n.toNat))]

open Silmaril.Wasm.Numerics Silmaril.Wasm.Validation in
/-- **Specification**: every function instance running `is_sorted` (with two parameters and
one result), at any address, meets `isSortedSpec` for total correctness, at every profile and
for every host relation. -/
def Spec : Prop :=
  ∀ {H : Type} (P : Profile) (host : HostSemantics H) (a : Nat) (fi : FuncInst H)
    (ps rs : Ty (.list .val)), fi.code = .wasm isSortedFunc → Expand fi.type (.func ps rs) →
    ps.length = 2 → rs.length = 1 → Silmaril.Wasm.Logic.Hoare.TFSpecAt P host a (isSortedSpec a fi)

open Silmaril.Wasm.Numerics in
/-- **The instantiated program**: function `0` of `store₀` meets `isSortedSpec`. -/
def SpecStore : Prop :=
  ∃ fi : FuncInst Nat, store₀.funcs[0]? = some fi ∧
    ∀ (P : Profile) (host : HostSemantics Nat), Silmaril.Wasm.Logic.Hoare.TFSpecAt P host 0 (isSortedSpec 0 fi)

end Silmaril.WasmSpec.IsSorted

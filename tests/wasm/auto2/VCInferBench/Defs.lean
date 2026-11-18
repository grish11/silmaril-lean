module

public import Silmaril.Wasm.Wat

/-!
# Programs of the `vcinfer` benchmark (round 2, summaries, pass 3)

Program shapes that no hand-written contract of `Silmaril.Wasm.Auto2.VCEquiv.eqFuns` covers, so
stage `vcequiv` alone leaves them unknown. Their contracts are inferred
(`Silmaril.Wasm.Auto2.VCInfer`): the WAT texts are those of `benchmarks/wasm-auto-verify/summaries3`
(`check-inputs.sh` checks that they are quoted verbatim).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.VCInferBench

open Silmaril.Wasm

/-- The sum loop with a scratch local: the accumulator is local 2 (`benchmarks/wasm-auto-verify/summaries3/sum-tmp.wat`). -/
def sumTmp := wat3! r#"
(module
 (func $sum (export "sum") (param $n i32) (result i32) (local $t i32) (local $acc i32)
  (block $done
   (loop $again
    (br_if $done (i32.eqz (local.get $n)))
    (local.set $t (i32.add (local.get $acc) (local.get $n)))
    (local.set $acc (local.get $t))
    (local.set $n (i32.sub (local.get $n) (i32.const 1)))
    (br $again)))
  (local.get $acc)))
"#

/-- Its function. -/
def sumTmpFunc : Func := sumTmp.funcs[0]

/-- The sum loop that decrements `n` before adding (`acc + (n - 1) + 1`) (`benchmarks/wasm-auto-verify/summaries3/sum-decfirst.wat`). -/
def sumDecFirst := wat3! r#"
(module
 (func $sum (export "sum") (param $n i32) (result i32) (local $acc i32)
  (block $done
   (loop $again
    (br_if $done (i32.eqz (local.get $n)))
    (local.set $n (i32.sub (local.get $n) (i32.const 1)))
    (local.set $acc (i32.add (i32.add (local.get $acc) (local.get $n)) (i32.const 1)))
    (br $again)))
  (local.get $acc)))
"#

/-- Its function. -/
def sumDecFirstFunc : Func := sumDecFirst.funcs[0]

/-- A guarded `do … while` over a copy `i` of `n` (accumulator local 1, counter local 2), the test on a `local.tee` (`benchmarks/wasm-auto-verify/summaries3/sum-copy.wat`). -/
def sumCopy := wat3! r#"
(module
 (func $sum (export "sum") (param $n i32) (result i32) (local $acc i32) (local $i i32)
  (local.set $i (local.get $n))
  (if (local.get $i)
   (then
    (loop $again
     (local.set $acc (i32.add (local.get $i) (local.get $acc)))
     (br_if $again (local.tee $i (i32.sub (local.get $i) (i32.const 1)))))))
  (local.get $acc)))
"#

/-- Its function. -/
def sumCopyFunc : Func := sumCopy.funcs[0]

/-- Binaryen `version_123` `-O3` of `sum-decfirst` (`benchmarks/wasm-auto-verify/summaries3/sum-decfirst.binaryen-O3.wat`). -/
def sumDecFirstO3 := wat3! r#"
(module
 (type $0 (func (param i32) (result i32)))
 (export "sum" (func $sum))
 (func $sum (param $0 i32) (result i32)
  (local $1 i32)
  (loop $again
   (if
    (local.get $0)
    (then
     (local.set $1
      (i32.add
       (i32.add
        (local.get $1)
        (local.tee $0
         (i32.sub
          (local.get $0)
          (i32.const 1)
         )
        )
       )
       (i32.const 1)
      )
     )
     (br $again)
    )
   )
  )
  (local.get $1)
 )
)
"#

/-- Its function. -/
def sumDecFirstO3Func : Func := sumDecFirstO3.funcs[0]

/-- Binaryen `version_123` `-O3` of `sum-copy` (`benchmarks/wasm-auto-verify/summaries3/sum-copy.binaryen-O3.wat`). -/
def sumCopyO3 := wat3! r#"
(module
 (type $0 (func (param i32) (result i32)))
 (export "sum" (func $sum))
 (func $sum (param $0 i32) (result i32)
  (local $1 i32)
  (if
   (local.get $0)
   (then
    (loop $again
     (local.set $1
      (i32.add
       (local.get $0)
       (local.get $1)
      )
     )
     (br_if $again
      (local.tee $0
       (i32.sub
        (local.get $0)
        (i32.const 1)
       )
      )
     )
    )
   )
  )
  (local.get $1)
 )
)
"#

/-- Its function. -/
def sumCopyO3Func : Func := sumCopyO3.funcs[0]

/-- A counting-up loop (`i = 1 … n`), for the second template of `sumI` (`benchmarks/wasm-auto-verify/summaries3/sum-up.wat`). -/
def sumUp := wat3! r#"
(module
 (func $sum (export "sum") (param $n i32) (result i32) (local $acc i32) (local $i i32)
  (block $done
   (loop $again
    (br_if $done (i32.ge_u (local.get $i) (local.get $n)))
    (local.set $i (i32.add (local.get $i) (i32.const 1)))
    (local.set $acc (i32.add (local.get $acc) (local.get $i)))
    (br $again)))
  (local.get $acc)))
"#

/-- Its function. -/
def sumUpFunc : Func := sumUp.funcs[0]

/-- The signed maximum by `select` (`benchmarks/wasm-auto-verify/summaries3/max-select.wat`). -/
def maxSelect := wat3! r#"
(module
 (func $max (export "max") (param $x i32) (param $y i32) (result i32)
  (select (local.get $x) (local.get $y) (i32.gt_s (local.get $x) (local.get $y)))))
"#

/-- Its function. -/
def maxSelectFunc : Func := maxSelect.funcs[0]

/-- The signed maximum by `if` on `x ≤ y` (`benchmarks/wasm-auto-verify/summaries3/max-le.wat`). -/
def maxLe := wat3! r#"
(module
 (func $max (export "max") (param $x i32) (param $y i32) (result i32)
  (if (result i32) (i32.le_s (local.get $x) (local.get $y))
   (then (local.get $y))
   (else (local.get $x)))))
"#

/-- Its function. -/
def maxLeFunc : Func := maxLe.funcs[0]

end Silmaril.Wasm.Auto2.VCInferBench

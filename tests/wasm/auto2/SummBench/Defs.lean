module

public import tests.wasm.auto.FrontBench.Defs

/-!
# Pinned inputs of the summaries benchmark (round 2 of the summaries track)

Copies of the files in `benchmarks/wasm-auto-verify/summaries/` (`check-inputs.sh` keeps them
equal; `gen.sh` regenerates the Binaryen outputs with the pinned `version_123` and the pinned
binaries in `bin/`): loops with constant trip counts (unrolled by `Silmaril.Wasm.Auto2.Summ`) and
internal calls (inlined by `Silmaril.Wasm.Auto2.Calls`), each against Binaryen `-O3`, a hand-written
equivalent and a mutant. Theorems: `tests.wasm.auto2.SummBench.Thms`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.SummBench

open Silmaril.Wasm

/-- `sum8`: `x * 0 + … + x * 7` by a `do … while` loop with a constant trip count (`benchmarks/wasm-auto-verify/summaries/sum8.wat`). -/
def sum8 := wat3! r#"
(module
  (func $sum8 (export "sum8") (param $x i32) (result i32) (local $i i32) (local $acc i32)
    ;; acc = x*0 + x*1 + ... + x*7, as a do-while loop with a constant trip count
    (loop $l
      (local.set $acc (i32.add (local.get $acc) (i32.mul (local.get $x) (local.get $i))))
      (local.set $i (i32.add (local.get $i) (i32.const 1)))
      (br_if $l (i32.lt_u (local.get $i) (i32.const 8))))
    (local.get $acc)))
"#

/-- `sum8`, Binaryen `version_123` `-O3` (the loop kept, its counter update moved into the condition) (`benchmarks/wasm-auto-verify/summaries/sum8.binaryen-O3.wat`). -/
def sum8O3 := wat3! r#"
(module
 (type $0 (func (param i32) (result i32)))
 (export "sum8" (func $sum8))
 (func $sum8 (param $0 i32) (result i32)
  (local $1 i32)
  (local $2 i32)
  (loop $l
   (local.set $2
    (i32.add
     (local.get $2)
     (i32.mul
      (local.get $0)
      (local.get $1)
     )
    )
   )
   (br_if $l
    (i32.lt_u
     (local.tee $1
      (i32.add
       (local.get $1)
       (i32.const 1)
      )
     )
     (i32.const 8)
    )
   )
  )
  (local.get $2)
 )
)
"#

/-- the closed form of `sum8`: `x * 28` (`benchmarks/wasm-auto-verify/summaries/sum8-closed.wat`). -/
def sum8Closed := wat3! r#"
(module
  (func $sum8 (export "sum8") (param $x i32) (result i32)
    ;; the closed form of sum8: x * (0 + 1 + ... + 7)
    (i32.mul (local.get $x) (i32.const 28))))
"#

/-- `sum8` with one iteration missing (`benchmarks/wasm-auto-verify/summaries/sum8-mutant.wat`). -/
def sum8Mutant := wat3! r#"
(module
  (func $sum8 (export "sum8") (param $x i32) (result i32) (local $i i32) (local $acc i32)
    ;; sum8 with one iteration missing (i < 7)
    (loop $l
      (local.set $acc (i32.add (local.get $acc) (i32.mul (local.get $x) (local.get $i))))
      (local.set $i (i32.add (local.get $i) (i32.const 1)))
      (br_if $l (i32.lt_u (local.get $i) (i32.const 7))))
    (local.get $acc)))
"#

/-- `x ^ 4` (`i64`) by a loop of four multiplications (`benchmarks/wasm-auto-verify/summaries/pow4.wat`). -/
def pow4 := wat3! r#"
(module
  (func $pow4 (export "pow4") (param $x i64) (result i64) (local $i i32) (local $acc i64)
    ;; x^4 by a loop of four multiplications
    (local.set $acc (i64.const 1))
    (loop $l
      (local.set $acc (i64.mul (local.get $acc) (local.get $x)))
      (local.set $i (i32.add (local.get $i) (i32.const 1)))
      (br_if $l (i32.ne (local.get $i) (i32.const 4))))
    (local.get $acc)))
"#

/-- `x ^ 4` as `(x * x) * (x * x)` (`benchmarks/wasm-auto-verify/summaries/pow4-straight.wat`). -/
def pow4Straight := wat3! r#"
(module
  (func $pow4 (export "pow4") (param $x i64) (result i64) (local $y i64)
    ;; x^4 as (x * x) * (x * x)
    (local.set $y (i64.mul (local.get $x) (local.get $x)))
    (i64.mul (local.get $y) (local.get $y))))
"#

/-- `x / (y + 0) + … + x / (y + 3)` by a loop: four trap guards (`benchmarks/wasm-auto-verify/summaries/divsum4.wat`). -/
def divSum4 := wat3! r#"
(module
  (func $divsum4 (export "divsum4") (param $x i32) (param $y i32) (result i32)
    (local $i i32) (local $acc i32)
    ;; acc = x / (y + 0) + x / (y + 1) + x / (y + 2) + x / (y + 3): traps when some y + i is 0
    (loop $l
      (local.set $acc
        (i32.add (local.get $acc) (i32.div_u (local.get $x) (i32.add (local.get $y) (local.get $i)))))
      (local.set $i (i32.add (local.get $i) (i32.const 1)))
      (br_if $l (i32.lt_u (local.get $i) (i32.const 4))))
    (local.get $acc)))
"#

/-- `divsum4`, Binaryen `version_123` `-O3` (`benchmarks/wasm-auto-verify/summaries/divsum4.binaryen-O3.wat`). -/
def divSum4O3 := wat3! r#"
(module
 (type $0 (func (param i32 i32) (result i32)))
 (export "divsum4" (func $divsum4))
 (func $divsum4 (param $0 i32) (param $1 i32) (result i32)
  (local $2 i32)
  (local $3 i32)
  (loop $l
   (local.set $3
    (i32.add
     (local.get $3)
     (i32.div_u
      (local.get $0)
      (i32.add
       (local.get $1)
       (local.get $2)
      )
     )
    )
   )
   (br_if $l
    (i32.lt_u
     (local.tee $2
      (i32.add
       (local.get $2)
       (i32.const 1)
      )
     )
     (i32.const 4)
    )
   )
  )
  (local.get $3)
 )
)
"#

/-- the sum of four bytes of memory `0` by a loop (a data segment, four in-bounds guards) (`benchmarks/wasm-auto-verify/summaries/memsum4.wat`). -/
def memSum4 := wat3! r#"
(module
  (memory 1)
  (data (i32.const 0) "\01\02\03\04\05\06\07\08")
  (func $memsum4 (export "memsum4") (param $p i32) (result i32) (local $i i32) (local $acc i32)
    ;; the sum of the four bytes at p, p + 1, p + 2, p + 3 (each load traps out of bounds)
    (loop $l
      (local.set $acc
        (i32.add (local.get $acc) (i32.load8_u (i32.add (local.get $p) (local.get $i)))))
      (local.set $i (i32.add (local.get $i) (i32.const 1)))
      (br_if $l (i32.lt_u (local.get $i) (i32.const 4))))
    (local.get $acc)))
"#

/-- `memsum4`, Binaryen `version_123` `-O3` (`benchmarks/wasm-auto-verify/summaries/memsum4.binaryen-O3.wat`). -/
def memSum4O3 := wat3! r#"
(module
 (type $0 (func (param i32) (result i32)))
 (memory $0 1)
 (data $0 (i32.const 0) "\01\02\03\04\05\06\07\08")
 (export "memsum4" (func $memsum4))
 (func $memsum4 (param $0 i32) (result i32)
  (local $1 i32)
  (local $2 i32)
  (loop $l
   (local.set $2
    (i32.add
     (local.get $2)
     (i32.load8_u
      (i32.add
       (local.get $0)
       (local.get $1)
      )
     )
    )
   )
   (br_if $l
    (i32.lt_u
     (local.tee $1
      (i32.add
       (local.get $1)
       (i32.const 1)
      )
     )
     (i32.const 4)
    )
   )
  )
  (local.get $2)
 )
)
"#

/-- three exports through internal calls: `sumsq` (a callee that updates a global), `mean` and `ratio` (a callee that divides) (`benchmarks/wasm-auto-verify/summaries/calls.wat`). -/
def calls := wat3! r#"
(module
  (global $count (mut i32) (i32.const 0))
  (func $sq (param $x i32) (result i32)
    ;; x * x, counting the calls in a global
    (global.set $count (i32.add (global.get $count) (i32.const 1)))
    (i32.mul (local.get $x) (local.get $x)))
  (func $quot (param $x i32) (param $y i32) (result i32)
    ;; traps when y is 0
    (i32.div_u (local.get $x) (local.get $y)))
  (func $sumsq (export "sumsq") (param $a i32) (param $b i32) (result i32)
    ;; a * a + b * b through two calls, and the call count
    (i32.add (i32.add (call $sq (local.get $a)) (call $sq (local.get $b))) (global.get $count)))
  (func $mean (export "mean") (param $a i32) (param $b i32) (result i32)
    ;; (a + b) / 2 through a call that may trap (it does not: the divisor is 2)
    (call $quot (i32.add (local.get $a) (local.get $b)) (i32.const 2)))
  (func $ratio (export "ratio") (param $a i32) (param $b i32) (result i32)
    ;; a / b + 1 through a call that traps when b is 0
    (i32.add (call $quot (local.get $a) (local.get $b)) (i32.const 1))))
"#

/-- `calls`, Binaryen `version_123` `-O3` (every call inlined) (`benchmarks/wasm-auto-verify/summaries/calls.binaryen-O3.wat`). -/
def callsO3 := wat3! r#"
(module
 (type $0 (func (param i32 i32) (result i32)))
 (global $count (mut i32) (i32.const 0))
 (export "sumsq" (func $sumsq))
 (export "mean" (func $mean))
 (export "ratio" (func $ratio))
 (func $sumsq (param $0 i32) (param $1 i32) (result i32)
  (global.set $count
   (i32.add
    (global.get $count)
    (i32.const 1)
   )
  )
  (global.set $count
   (i32.add
    (global.get $count)
    (i32.const 1)
   )
  )
  (i32.add
   (global.get $count)
   (i32.add
    (i32.mul
     (local.get $0)
     (local.get $0)
    )
    (i32.mul
     (local.get $1)
     (local.get $1)
    )
   )
  )
 )
 (func $mean (param $0 i32) (param $1 i32) (result i32)
  (i32.shr_u
   (i32.add
    (local.get $0)
    (local.get $1)
   )
   (i32.const 1)
  )
 )
 (func $ratio (param $0 i32) (param $1 i32) (result i32)
  (i32.add
   (i32.div_u
    (local.get $0)
    (local.get $1)
   )
   (i32.const 1)
  )
 )
)
"#

/-- `calls` with the calls inlined by hand (`benchmarks/wasm-auto-verify/summaries/calls-inlined.wat`). -/
def callsInlined := wat3! r#"
(module
  (global $count (mut i32) (i32.const 0))
  (func $sumsq (export "sumsq") (param $a i32) (param $b i32) (result i32)
    ;; sumsq of calls.wat with both calls inlined by hand
    (global.set $count (i32.add (global.get $count) (i32.const 2)))
    (i32.add (i32.add (i32.mul (local.get $a) (local.get $a)) (i32.mul (local.get $b) (local.get $b)))
      (global.get $count)))
  (func $mean (export "mean") (param $a i32) (param $b i32) (result i32)
    (i32.shr_u (i32.add (local.get $a) (local.get $b)) (i32.const 1)))
  (func $ratio (export "ratio") (param $a i32) (param $b i32) (result i32)
    (i32.add (i32.div_u (local.get $a) (local.get $b)) (i32.const 1))))
"#

/-- `calls` with one call not counted, a signed shift, and a division that cannot trap (`benchmarks/wasm-auto-verify/summaries/calls-mutant.wat`). -/
def callsMutant := wat3! r#"
(module
  (global $count (mut i32) (i32.const 0))
  (func $sumsq (export "sumsq") (param $a i32) (param $b i32) (result i32)
    ;; sumsq counting one call only
    (global.set $count (i32.add (global.get $count) (i32.const 1)))
    (i32.add (i32.add (i32.mul (local.get $a) (local.get $a)) (i32.mul (local.get $b) (local.get $b)))
      (global.get $count)))
  (func $mean (export "mean") (param $a i32) (param $b i32) (result i32)
    (i32.shr_s (i32.add (local.get $a) (local.get $b)) (i32.const 1)))
  (func $ratio (export "ratio") (param $a i32) (param $b i32) (result i32)
    ;; does not trap when b is 0
    (i32.add (i32.div_u (local.get $a) (i32.or (local.get $b) (i32.const 1))) (i32.const 1))))
"#

end Silmaril.Wasm.Auto2.SummBench

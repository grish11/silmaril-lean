module

public import Silmaril.Wasm.Auto2.Wat.Defs
public import Silmaril.Wasm.Auto2.KernelU.Thms
public import Silmaril.Wasm.Auto2.Valid2.Thms
public import Silmaril.Wasm.Auto2.Calls.Thms

/-!
# `tuple.extract` of calls and blocks: a kernel-checked Binaryen run

`pair2Src` has a two-result function `$pair`, a three-result `$tri` and four callers that use
one component of a multi-value call or of a multi-value `if`. Binaryen `version_123` `-Os`,
printed from its optimised IR (`wasm-opt --all-features pair2.wasm -Os -S`, `pair2Os` below),
reads components with `tuple.extract` of a `call` directly, which `wat3b!` did not read before
pass 3 of the kernel track (only `tuple.extract` of a tuple local's `local.get`/`local.tee`).
Printing a *binary* gives the tuple-local form instead (Binaryen's binary reader introduces
scratch tuple locals), so the certificates of `wasm-check pass --wat` did not need this;
prints of Binaryen's IR do.

* `pair2Os_lowered`: `wat3b!`'s lowering is, by `rfl`, the standard WAT `pair2OsStd`
  (`tuple.extract 2 0 (call …)` is the call and a `drop`; `tuple.extract 2 1 (call …)` the call,
  a `local.set` of the scratch local `$__tx.i64`, a `drop` and its `local.get`);
* `pair2Os_equiv_first`, `_second`, `_mid`: three exports are equivalent to the source at every
  profile, by the `equivc` stage (calls inlined) decided in the kernel over `instK?`, both modules
  validated by `validG?`. The fourth, `blk` (a multi-value `if` kept in a tuple local), is read
  (`pair2Os_lowered`) and validated, but the summaries do not prove it (`checkAmongC` gives
  `false` for it: multi-value blocks are outside the summaries).

Provenance (2026-11-11): `pair2.wat` (sha256 `fe9f916b…0d70`) assembled by wasm-tools 1.262.0
(`wasm-tools parse`, sha256 of the binary `fe6a056d…b211`) to `pair2.wasm` (`96b282d5…0610`);
`wasm-opt` of Binaryen `version_123` (sha256 `d66c6724…9c4a`, as `combined/gen-wat.sh`) printed
`pair2Os` (`02c02bbc…f6`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto2.KernelBench

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Auto.Front

/-- The source (standard WAT). -/
def pair2Src : Module := wat3! r#"
(module
 (func $pair (param i32 i64) (result i32 i64)
  local.get 0
  i32.const 1
  i32.add
  local.get 1
  i64.const 2
  i64.mul)
 (func $tri (param i32) (result i32 i64 i32)
  local.get 0
  local.get 0
  i64.extend_i32_s
  local.get 0
  i32.const 3
  i32.mul)
 (func (export "first") (param i32 i64) (result i32)
  local.get 0
  local.get 1
  call $pair
  drop)
 (func (export "second") (param i32 i64) (result i64)
  (local i64)
  local.get 0
  local.get 1
  call $pair
  local.set 2
  drop
  local.get 2)
 (func (export "mid") (param i32) (result i64)
  (local i64)
  local.get 0
  call $tri
  drop
  local.set 1
  drop
  local.get 1)
 (func (export "blk") (param i32) (result i32)
  (local i32)
  local.get 0
  local.get 0
  i64.extend_i32_u
  call $pair
  drop
  local.get 0
  if (param i32) (result i32 i32)
   i32.const 7
  else
   i32.const 9
  end
  local.set 1
  local.get 1
  i32.add
  local.get 1
  i32.mul)
)
"#

/-- Binaryen `-Os`, printed from its IR (`tuple.extract` of calls and of a `local.tee`). -/
def pair2Os : Module := wat3b! r#"
(module
 (type $0 (func (result i32 i32)))
 (type $1 (func (param i32 i64) (result i32 i64)))
 (type $2 (func (param i32 i64) (result i32)))
 (type $3 (func (param i32 i64) (result i64)))
 (type $4 (func (param i32) (result i64)))
 (type $5 (func (param i32) (result i32)))
 (export "first" (func $2))
 (export "second" (func $3))
 (export "mid" (func $4))
 (export "blk" (func $5))
 (func $pair (type $1) (param $0 i32) (param $1 i64) (result i32 i64)
  (tuple.make 2
   (i32.add
    (local.get $0)
    (i32.const 1)
   )
   (i64.shl
    (local.get $1)
    (i64.const 1)
   )
  )
 )
 (func $2 (type $2) (param $0 i32) (param $1 i64) (result i32)
  (tuple.extract 2 0
   (call $pair
    (local.get $0)
    (local.get $1)
   )
  )
 )
 (func $3 (type $3) (param $0 i32) (param $1 i64) (result i64)
  (tuple.extract 2 1
   (call $pair
    (local.get $0)
    (local.get $1)
   )
  )
 )
 (func $4 (type $4) (param $0 i32) (result i64)
  (local $1 i64)
  (local.set $1
   (i64.extend_i32_s
    (local.get $0)
   )
  )
  (local.get $1)
 )
 (func $5 (type $5) (param $0 i32) (result i32)
  (local $1 i32)
  (local $2 (tuple i32 i32))
  (local.set $1
   (tuple.extract 2 0
    (call $pair
     (local.get $0)
     (i64.extend_i32_u
      (local.get $0)
     )
    )
   )
  )
  (i32.mul
   (i32.add
    (tuple.extract 2 0
     (local.tee $2
      (if (type $0) (result i32 i32)
       (local.get $0)
       (then
        (tuple.make 2
         (local.get $1)
         (i32.const 7)
        )
       )
       (else
        (tuple.make 2
         (local.get $1)
         (i32.const 9)
        )
       )
      )
     )
    )
    (local.tee $0
     (tuple.extract 2 1
      (local.get $2)
     )
    )
   )
   (local.get $0)
  )
 )
)
"#

/-- The same module lowered by hand. -/
def pair2OsStd : Module := wat3! r#"
(module
 (type $0 (func (result i32 i32)))
 (type $1 (func (param i32 i64) (result i32 i64)))
 (type $2 (func (param i32 i64) (result i32)))
 (type $3 (func (param i32 i64) (result i64)))
 (type $4 (func (param i32) (result i64)))
 (type $5 (func (param i32) (result i32)))
 (export "first" (func $2))
 (export "second" (func $3))
 (export "mid" (func $4))
 (export "blk" (func $5))
 (func $pair (type $1) (param $0 i32) (param $1 i64) (result i32 i64)
  (i32.add (local.get $0) (i32.const 1))
  (i64.shl (local.get $1) (i64.const 1)))
 (func $2 (type $2) (param $0 i32) (param $1 i64) (result i32)
  (call $pair (local.get $0) (local.get $1))
  drop)
 (func $3 (type $3) (param $0 i32) (param $1 i64) (result i64)
  (local $__tx.i64 i64)
  (call $pair (local.get $0) (local.get $1))
  (local.set $__tx.i64)
  drop
  (local.get $__tx.i64))
 (func $4 (type $4) (param $0 i32) (result i64)
  (local $1 i64)
  (local.set $1 (i64.extend_i32_s (local.get $0)))
  (local.get $1))
 (func $5 (type $5) (param $0 i32) (result i32)
  (local $1 i32)
  (local $2.0 i32) (local $2.1 i32)
  (call $pair (local.get $0) (i64.extend_i32_u (local.get $0)))
  drop
  (local.set $1)
  (if (type $0) (result i32 i32) (local.get $0)
   (then (local.get $1) (i32.const 7))
   (else (local.get $1) (i32.const 9)))
  (local.set $2.1)
  (local.set $2.0)
  (local.get $2.0)
  (local.get $2.1)
  (local.tee $0)
  i32.add
  (local.get $0)
  i32.mul)
)"#

theorem pair2Os_lowered : pair2Os = pair2OsStd := rfl

theorem pair2Src_valid : (validate? pair2Src).isSome = true := by
  rw [← Silmaril.Proofs.Wasm.Auto2.Valid2.validG?_eq]
  decide +kernel

theorem pair2Os_valid : (validate? pair2Os).isSome = true := by
  rw [← Silmaril.Proofs.Wasm.Auto2.Valid2.validG?_eq]
  decide +kernel

theorem pair2_chunk :
    Silmaril.Wasm.Auto2.Calls.checkAmongC Silmaril.Wasm.Auto2.Summ.defFuel pair2Src pair2Os
      [0, 1, 2] = [true, true, true] := by
  rw [Silmaril.Proofs.Wasm.Auto2.KernelU.checkAmongC_eq_K pair2Src_valid pair2Os_valid]
  decide +kernel

/-- **Export `first` of Binaryen's `-Os` output is equivalent to the source.** -/
theorem pair2Os_equiv_first (P : Numerics.Profile) :
    ModEquiv Rel.eq.toProp P pair2Src pair2Os 0 :=
  Silmaril.Wasm.Auto2.Calls.modEquiv_of_checkAmongC (js := [0, 1, 2]) (i := 0)
    (Silmaril.Wasm.Auto.Bridge.rel_refl _) rfl (by rw [pair2_chunk]; rfl)

/-- **Export `second`** (`tuple.extract 2 1` of a call). -/
theorem pair2Os_equiv_second (P : Numerics.Profile) :
    ModEquiv Rel.eq.toProp P pair2Src pair2Os 1 :=
  Silmaril.Wasm.Auto2.Calls.modEquiv_of_checkAmongC (js := [0, 1, 2]) (i := 1)
    (Silmaril.Wasm.Auto.Bridge.rel_refl _) rfl (by rw [pair2_chunk]; rfl)

/-- **Export `mid`** (`$tri` inlined by Binaryen). -/
theorem pair2Os_equiv_mid (P : Numerics.Profile) :
    ModEquiv Rel.eq.toProp P pair2Src pair2Os 2 :=
  Silmaril.Wasm.Auto2.Calls.modEquiv_of_checkAmongC (js := [0, 1, 2]) (i := 2)
    (Silmaril.Wasm.Auto.Bridge.rel_refl _) rfl (by rw [pair2_chunk]; rfl)

end Silmaril.Proofs.Wasm.Auto2.KernelBench

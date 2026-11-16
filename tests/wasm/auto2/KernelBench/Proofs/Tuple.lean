module

public import Silmaril.Wasm.Auto2.Wat.Defs
public import Silmaril.Wasm.Auto2.KernelU.Thms
public import Silmaril.Wasm.Auto2.Valid.Thms
public import Silmaril.Wasm.Auto2.Calls.Thms

/-!
# Tuple-typed locals and `tuple.extract`: a kernel-checked Binaryen run

`pairSrc` is a module with a two-result function `$pair` and two callers that keep its results
in locals. Binaryen `version_123` `-O2` (`wasm-opt --all-features -O2 -S`, the printing below)
keeps each pair in a tuple-typed local and reads it with `tuple.extract`; `wat3b!` lowers those
to scalar locals (`Silmaril.Wasm.Auto2.Wat.lowerFunc`, pass 2 of the kernel track).

* `pairO2_lowered`: the lowering is, by `rfl`, the standard WAT `pairO2Std` (component locals
  `$2.0`, `$2.1`; `local.tee` as `local.set`s then `local.get`s);
* `pairO2_equiv_use`, `pairO2_equiv_swap`: both exports are equivalent to the source at every
  profile, by the `equivc` stage (calls inlined) decided in the kernel over `instK?`, with the
  modules validated through `validK?`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto2.KernelBench

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Auto.Front

/-- The source (standard WAT). -/
def pairSrc : Module := wat3! r#"
(module
 (func $pair (param i32 i64) (result i32 i64)
  local.get 0
  i32.const 1
  i32.add
  local.get 1
  i64.const 2
  i64.mul)
 (func (export "use") (param i32 i64) (result i64)
  (local i32 i64)
  local.get 0
  local.get 1
  call $pair
  local.set 3
  local.set 2
  local.get 3
  local.get 2
  i64.extend_i32_u
  i64.add)
 (func (export "swap") (param i32 i64) (result i64 i32)
  (local i32 i64)
  local.get 0
  local.get 1
  call $pair
  local.set 3
  local.set 2
  local.get 3
  local.get 2)
)
"#

/-- Binaryen `-O2`'s printing (tuple-typed locals, `tuple.extract`, `tuple.make`). -/
def pairO2 : Module := wat3b! r#"
(module
 (type $0 (func (result i64 i32)))
 (type $1 (func (param i32 i64) (result i32 i64)))
 (type $2 (func (param i32 i64) (result i64)))
 (type $3 (func (param i32 i64) (result i64 i32)))
 (export "use" (func $0))
 (export "swap" (func $1))
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
 (func $0 (type $2) (param $0 i32) (param $1 i64) (result i64)
  (local $2 (tuple i32 i64))
  (i64.add
   (i64.extend_i32_u
    (tuple.extract 2 0
     (local.tee $2
      (call $pair
       (local.get $0)
       (local.get $1)
      )
     )
    )
   )
   (tuple.extract 2 1
    (local.get $2)
   )
  )
 )
 (func $1 (type $3) (param $0 i32) (param $1 i64) (result i64 i32)
  (local $2 (tuple i32 i64))
  (local.set $0
   (tuple.extract 2 0
    (local.tee $2
     (call $pair
      (local.get $0)
      (local.get $1)
     )
    )
   )
  )
  (tuple.make 2
   (tuple.extract 2 1
    (local.get $2)
   )
   (local.get $0)
  )
 )
)
"#

/-- The same module with the tuple local lowered by hand. -/
def pairO2Std : Module := wat3! r#"
(module
 (type $0 (func (result i64 i32)))
 (type $1 (func (param i32 i64) (result i32 i64)))
 (type $2 (func (param i32 i64) (result i64)))
 (type $3 (func (param i32 i64) (result i64 i32)))
 (export "use" (func $0))
 (export "swap" (func $1))
 (func $pair (type $1) (param $0 i32) (param $1 i64) (result i32 i64)
  (i32.add (local.get $0) (i32.const 1))
  (i64.shl (local.get $1) (i64.const 1)))
 (func $0 (type $2) (param $0 i32) (param $1 i64) (result i64)
  (local $2.0 i32) (local $2.1 i64)
  (call $pair (local.get $0) (local.get $1))
  (local.set $2.1)
  (local.set $2.0)
  (local.get $2.0)
  i64.extend_i32_u
  (local.get $2.1)
  i64.add)
 (func $1 (type $3) (param $0 i32) (param $1 i64) (result i64 i32)
  (local $2.0 i32) (local $2.1 i64)
  (call $pair (local.get $0) (local.get $1))
  (local.set $2.1)
  (local.set $2.0)
  (local.get $2.0)
  (local.set $0)
  (local.get $2.1)
  (local.get $0))
)"#

theorem pairO2_lowered : pairO2 = pairO2Std := rfl

theorem pairSrc_valid : (validate? pairSrc).isSome = true := by
  rw [← Silmaril.Proofs.Wasm.Auto2.Valid.validK?_eq]
  decide +kernel

theorem pairO2_valid : (validate? pairO2).isSome = true := by
  rw [← Silmaril.Proofs.Wasm.Auto2.Valid.validK?_eq]
  decide +kernel

theorem pair_chunk :
    Silmaril.Wasm.Auto2.Calls.checkAmongC Silmaril.Wasm.Auto2.Summ.defFuel pairSrc pairO2 [0, 1] =
      [true, true] := by
  rw [Silmaril.Proofs.Wasm.Auto2.KernelU.checkAmongC_eq_K pairSrc_valid pairO2_valid]
  decide +kernel

/-- **Export `use` of Binaryen's `-O2` output is equivalent to the source.** -/
theorem pairO2_equiv_use (P : Numerics.Profile) : ModEquiv Rel.eq.toProp P pairSrc pairO2 0 :=
  Silmaril.Wasm.Auto2.Calls.modEquiv_of_checkAmongC (js := [0, 1]) (i := 0)
    (Silmaril.Wasm.Auto.Bridge.rel_refl _) rfl (by rw [pair_chunk]; rfl)

/-- **Export `swap` of Binaryen's `-O2` output is equivalent to the source.** -/
theorem pairO2_equiv_swap (P : Numerics.Profile) : ModEquiv Rel.eq.toProp P pairSrc pairO2 1 :=
  Silmaril.Wasm.Auto2.Calls.modEquiv_of_checkAmongC (js := [0, 1]) (i := 1)
    (Silmaril.Wasm.Auto.Bridge.rel_refl _) rfl (by rw [pair_chunk]; rfl)

end Silmaril.Proofs.Wasm.Auto2.KernelBench

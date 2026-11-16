module

public import Silmaril.Wasm.Auto2.Kernel.Thms
public import Silmaril.Wasm.Auto2.Wat.Defs

/-!
# An element segment, instantiated in the kernel

A module with a 256-entry function table and an active element segment of 40 functions at
offset 10 (a dispatch function `call` through `call_indirect`). `instK?` initialises the segment
by `tableInitLoopK` (one `writeL` of the references, `tableInitLoopK_eq`) instead of one
`List.set` per element; the theorems below are decided by kernel evaluation of that instance.
Pass 2 of the kernel track: on a 1024-entry table with a 200-function segment, the instance took
1.5 s of kernel time against 3.6 s for the byte-wise (here: reference-wise) loop.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto2.KernelBench

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Auto2.Kernel

/-- The module (WAT text, `wat3b!`). -/
def elemTable : Module := wat3b! r#"
(module
 (type $t (func (result i32)))
 (table 256 funcref)
 (elem (i32.const 10) func $f0 $f1 $f2 $f3 $f4 $f5 $f6 $f7 $f8 $f9 $f10 $f11 $f12 $f13 $f14 $f15 $f16 $f17 $f18 $f19 $f20 $f21 $f22 $f23 $f24 $f25 $f26 $f27 $f28 $f29 $f30 $f31 $f32 $f33 $f34 $f35 $f36 $f37 $f38 $f39)
 (func $f0 (result i32) i32.const 0)
 (func $f1 (result i32) i32.const 1)
 (func $f2 (result i32) i32.const 2)
 (func $f3 (result i32) i32.const 3)
 (func $f4 (result i32) i32.const 4)
 (func $f5 (result i32) i32.const 5)
 (func $f6 (result i32) i32.const 6)
 (func $f7 (result i32) i32.const 7)
 (func $f8 (result i32) i32.const 8)
 (func $f9 (result i32) i32.const 9)
 (func $f10 (result i32) i32.const 10)
 (func $f11 (result i32) i32.const 11)
 (func $f12 (result i32) i32.const 12)
 (func $f13 (result i32) i32.const 13)
 (func $f14 (result i32) i32.const 14)
 (func $f15 (result i32) i32.const 15)
 (func $f16 (result i32) i32.const 16)
 (func $f17 (result i32) i32.const 17)
 (func $f18 (result i32) i32.const 18)
 (func $f19 (result i32) i32.const 19)
 (func $f20 (result i32) i32.const 20)
 (func $f21 (result i32) i32.const 21)
 (func $f22 (result i32) i32.const 22)
 (func $f23 (result i32) i32.const 23)
 (func $f24 (result i32) i32.const 24)
 (func $f25 (result i32) i32.const 25)
 (func $f26 (result i32) i32.const 26)
 (func $f27 (result i32) i32.const 27)
 (func $f28 (result i32) i32.const 28)
 (func $f29 (result i32) i32.const 29)
 (func $f30 (result i32) i32.const 30)
 (func $f31 (result i32) i32.const 31)
 (func $f32 (result i32) i32.const 32)
 (func $f33 (result i32) i32.const 33)
 (func $f34 (result i32) i32.const 34)
 (func $f35 (result i32) i32.const 35)
 (func $f36 (result i32) i32.const 36)
 (func $f37 (result i32) i32.const 37)
 (func $f38 (result i32) i32.const 38)
 (func $f39 (result i32) i32.const 39)
 (func (export "call") (param i32) (result i32) local.get 0 call_indirect (type $t))
)
"#

/-- The table after instantiation: 256 entries, 10 null, 40 function references, 206 null. -/
theorem elemTable_refs :
    ((instK? elemTable).map fun I =>
      (I.store.tables.map fun t =>
        ((t.refs.take 10).all (· == .null), ((t.refs.drop 10).take 40).all (· != .null),
          (t.refs.drop 50).all (· == .null), t.refs.length))) =
      some [(true, true, true, 256)] := by
  decide +kernel

/-- The same fact about `instance?`, the specification's instance (`instK?_eq`). -/
theorem elemTable_refs_spec :
    ((Silmaril.Wasm.Verify.instance? elemTable).map fun I =>
      (I.2.store.tables.map fun t => t.refs.length)) = some [256] := by
  have hv : (Silmaril.Wasm.Validation.validate? elemTable).isSome = true := by decide +kernel
  have h := Silmaril.Proofs.Wasm.Auto2.Kernel.instK?_eq hv
  have hk : ((instK? elemTable).map fun I => (I.store.tables.map fun t => t.refs.length)) =
      some [256] := by
    decide +kernel
  rw [h, Option.map_map] at hk
  exact hk

end Silmaril.Proofs.Wasm.Auto2.KernelBench

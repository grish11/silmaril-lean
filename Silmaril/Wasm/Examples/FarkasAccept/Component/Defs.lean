module

public import Silmaril.Wasm.Examples.FarkasAccept.Defs
public import Silmaril.Wasm.Component.Reference.ListLift.Defs
public import Silmaril.Wasm.Component.Binary.Encode.Defs
public import Silmaril.Wasm.Binaryen.Exe.Encode

/-!
# The Farkas acceptor as a component: the component and its binary

`farkasComp` is the list-taking component (`Silmaril.Wasm.Component.Reference.ListLift.ListComp`)
of one instance of `prog`: memory `memory` (the module's memory `1`, `memIdx := 1`), allocator
`cabi_realloc`, and the export

```wit
record ineq { coeffs: list<tuple<u32, s64>>, bound: s64 }
check: func(system: list<ineq>, y: list<s64>) -> bool
```

the `canon lift … (memory 0) (realloc 0)` of the core export `check`, the component's core
memory `0` being the alias of the core export `memory`. Its reference component is
`farkasComp.toRef` and its binary `farkasComp.toAst coreBytes` (the generic emitter
`ListComp.toAst`, with the definitions of `toRef` in the same order):

```wat
(component
  (core module $m …)                                   ;; core module 0: `prog`
  (core instance $i (instantiate $m))                  ;; core instance 0
  (alias core export $i "memory" (core memory))        ;; core memory 0 (prog's memory 1)
  (alias core export $i "cabi_realloc" (core func))    ;; core func 0
  (alias core export $i "check" (core func))           ;; core func 1
  (type (tuple u32 s64))                               ;; type 0
  (type (list 0))                                      ;; type 1: list<tuple<u32, s64>>
  (type (record (field "coeffs" 1) (field "bound" s64)))   ;; type 2
  (export "ineq" (type 2))                             ;; type 3: the named record `ineq`
  (type (list 3))                                      ;; type 4: list<ineq>
  (type (list s64))                                    ;; type 5
  (type (func (param "system" 4) (param "y" 5) (result bool)))   ;; type 6
  (func (canon lift (core func 1) (memory 0) (realloc 0) (type 6)))  ;; func 0
  (export "check" (func 0)))
```

The record is exported as the type `ineq` because an exported function may only mention
records through named types (`LTy.emit`, `LTy.emitB`).

The canonical-ABI layout (`LTy.layout`) is the one `prog` reads: an `ineq` takes 16 bytes
(alignment 8), the `coeffs` pair at `+0` and `bound` at `+8`; a `tuple<u32, s64>` 16 bytes
(alignment 8), the `u32` at `+0` and the `s64` at `+8`; an `s64` 8 bytes.

* `ofSystem S`, `ofS64s y`: the values of the parameters for a system `S : SystemW` and
  multipliers `y : List S64` (`Silmaril.Logic.LinArith.Carrier`).
* `FInv s t`: the store invariant under which `cabi_realloc` is a bump allocator for memory
  address `1` (`Silmaril.Wasm.Component.Reference.ListLift.BumpAlloc`): a store of the acceptor
  (`AccStore`: the instance's functions, any checker state, the 1 MiB ABI memory) whose heap
  pointer is `t ≤ memBytes`.

`coreBytes` is silmaril-lean's encoding of `prog` (`Binaryen.Exe.encodeModule?`) and `bytes` the
component's (`Binary.encode`); `examples/wasm-acceptors/farkas_accept.wasm` holds them. What the
export computes is stated in `Silmaril.Wasm.Examples.FarkasAccept.Component.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Examples.FarkasAccept

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Component.Reference.ListLift
open Silmaril.Logic.LinArith.Carrier (IneqW SystemW U32 S64)

/-- `tuple<u32, s64>`: a coefficient `(variable, value)`. -/
def coeffTy : LTy := .tuple .u32 [.s64]

/-- `record ineq { coeffs: list<tuple<u32, s64>>, bound: s64 }`. -/
def ineqTy : LTy := .record "ineq" "coeffs" (.list coeffTy) [("bound", .s64)]

/-- **The Farkas acceptor component.** -/
def farkasComp : ListComp where
  mod := prog
  memName := "memory"
  memIdx := 1
  reallocName := "cabi_realloc"
  exports := [
    { name := "check", params := [("system", .list ineqTy), ("y", .list .s64)],
      core := "check" }]

/-- The value of a coefficient. -/
def ofCoeff (c : U32 × S64) : LVal := .fields [.u32 c.1, .s64 c.2]

/-- The value of an inequality. -/
def ofIneq (r : IneqW) : LVal := .fields [.list (r.coeffs.map ofCoeff), .s64 r.bound]

/-- The `list<ineq>` value of a system. -/
def ofSystem (S : SystemW) : LVal := .list (S.map ofIneq)

/-- The `list<s64>` value of the multipliers. -/
def ofS64s (y : List S64) : LVal := .list (y.map .s64)

/-- The store invariant of the lowering with heap pointer `t`: a store of the acceptor (any
checker state, any ABI memory of `memBytes` bytes) with the heap pointer `t ≤ memBytes`. -/
def FInv (s : Silmaril.Wasm.Execution.Core.Store Nat) (t : Nat) : Prop :=
  (∃ B₁, AccStore s (BitVec.ofNat 32 t) B₁) ∧ t ≤ memBytes

/-- The core module bytes: silmaril-lean's encoding of `prog`. -/
def coreBytes : ByteArray :=
  match Silmaril.Wasm.Binaryen.Exe.encodeModule? prog with
  | .ok bs => ⟨bs.toArray⟩
  | .error _ => .empty

/-- The component bytes. -/
def bytes : ByteArray := (encode (farkasComp.toAst coreBytes)).getD .empty

end Silmaril.Wasm.Examples.FarkasAccept

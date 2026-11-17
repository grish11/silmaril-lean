module

public import Silmaril.Wasm.Examples.SatAccept.Defs
public import Silmaril.Wasm.Component.Reference.ListLift.Defs
public import Silmaril.Wasm.Component.Binary.Encode.Defs
public import Silmaril.Wasm.Binaryen.Exe.Encode
public import Silmaril.Wasm.Verify.Checker.Defs

/-!
# The SAT model-witness acceptor as a component: the component and its binary

`satComp` is the list-taking component (`Silmaril.Wasm.Component.Reference.ListLift.ListComp`)
of one instance of `prog`: memory `memory`, allocator `cabi_realloc`, and the exports

* `check-stream: func(problem: list<s32>, model: list<s32>) -> bool`, the lift of the core
  export `check-stream`;
* `check-nested: func(problem: list<list<s32>>, model: list<s32>) -> bool`, the lift of the
  core export `check-nested`;

both `canon lift … (memory 0) (realloc 0)`. Its reference component is `satComp.toRef` and its
binary `satComp.toAst coreBytes` (the generic emitter `ListComp.toAst`, with the definitions of
`toRef` in the same order):

```wat
(component
  (core module $m …)                        ;; core module 0: `prog`
  (core instance $i (instantiate $m))       ;; core instance 0
  (alias core export $i "memory" (core memory))        ;; core memory 0
  (alias core export $i "cabi_realloc" (core func))    ;; core func 0
  (alias core export $i "check-stream" (core func))    ;; core func 1
  (alias core export $i "check-nested" (core func))    ;; core func 2
  (type (list s32))                                    ;; type 0
  (type (list s32))                                    ;; type 1
  (type (func (param "problem" 0) (param "model" 1) (result bool)))   ;; type 2
  (type (list s32))                                    ;; type 3
  (type (list 3))                                      ;; type 4: list<list<s32>>
  (type (list s32))                                    ;; type 5
  (type (func (param "problem" 4) (param "model" 5) (result bool)))   ;; type 6
  (func (canon lift (core func 1) (memory 0) (realloc 0) (type 2)))   ;; func 0
  (func (canon lift (core func 2) (memory 0) (realloc 0) (type 6)))   ;; func 1
  (export "check-stream" (func 0))
  (export "check-nested" (func 1)))
```

`satI` is the instance of `prog` (`Silmaril.Wasm.Verify.instOf`, the instance `IsInstance`
describes) and `SInv s t` the store invariant under which `cabi_realloc` is a bump allocator
(`Silmaril.Wasm.Component.Reference.ListLift.BumpAlloc`): the functions of `satI`, memory `0`
of `memBytes` bytes, and the heap pointer (global `0` of the functions' module instance `satM`)
equal to `t ≤ memBytes`.

`coreBytes` is silmaril-lean's encoding of `prog` (`Binaryen.Exe.encodeModule?`) and `bytes` the
component's (`Binary.encode`); `examples/wasm-acceptors/sat_accept.wasm` holds them. What the
exports compute is stated in `Silmaril.Wasm.Examples.SatAccept.Component.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Examples.SatAccept

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Component.Reference.ListLift

/-- **The SAT acceptor component.** -/
def satComp : ListComp where
  mod := prog
  memName := "memory"
  reallocName := "cabi_realloc"
  exports := [
    { name := "check-stream", params := [("problem", .list .s32), ("model", .list .s32)],
      core := "check-stream" },
    { name := "check-nested", params := [("problem", .list (.list .s32)), ("model", .list .s32)],
      core := "check-nested" }]

/-- The instance of `prog`. -/
def satI : Silmaril.Wasm.Game.ScalarInstance := Silmaril.Wasm.Verify.instOf prog

/-- The module instance of the functions of `satI`. -/
def satM : Silmaril.Wasm.Execution.Core.ModuleInst :=
  ((satI.store.funcs[0]?).map (·.module)).getD {}

/-- The store invariant of the lowering with heap pointer `t`: the functions of `satI`, memory
`0` of `memBytes` bytes, and the heap pointer `t ≤ memBytes`. -/
def SInv (s : Silmaril.Wasm.Execution.Core.Store Nat) (t : Nat) : Prop :=
  s.funcs = satI.store.funcs ∧ (∃ mt B, s.mems[0]? = some ⟨mt, B⟩ ∧ B.size = memBytes) ∧
    Silmaril.Wasm.Logic.VC.globalVal s satM 0 = some (.i32 (BitVec.ofNat 32 t)) ∧ t ≤ memBytes

/-- The core module bytes: silmaril-lean's encoding of `prog`. -/
def coreBytes : ByteArray :=
  match Silmaril.Wasm.Binaryen.Exe.encodeModule? prog with
  | .ok bs => ⟨bs.toArray⟩
  | .error _ => .empty

/-- The component bytes. -/
def bytes : ByteArray := (encode (satComp.toAst coreBytes)).getD .empty

end Silmaril.Wasm.Examples.SatAccept

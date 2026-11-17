module

public import Silmaril.Wasm.Examples.LratAccept.Defs
public import Silmaril.Wasm.Component.Reference.ListLift.Defs
public import Silmaril.Wasm.Component.Binary.Encode.Defs
public import Silmaril.Wasm.Binaryen.Exe.Encode

/-!
# The LRAT UNSAT acceptor as a component: the component and its binary

`lratComp` is the list-taking component (`Silmaril.Wasm.Component.Reference.ListLift.ListComp`)
of one instance of `prog`: memory `memory` (the module's memory `1`, `memIdx := 1`), allocator
`cabi_realloc`, and the exports

* `check-stream: func(problem: list<s32>, cert: list<s32>) -> bool`, the lift of the core
  export `check-stream`;
* `check-nested: func(problem: list<list<s32>>, cert: list<s32>) -> bool`, the lift of the
  core export `check-nested`;

both `canon lift … (memory 0) (realloc 0)`, the component's core memory `0` being the alias of
the core export `memory`. Its reference component is `lratComp.toRef` and its binary
`lratComp.toAst coreBytes` (the generic emitter `ListComp.toAst`, with the definitions of
`toRef` in the same order):

```wat
(component
  (core module $m …)                        ;; core module 0: `prog`
  (core instance $i (instantiate $m))       ;; core instance 0
  (alias core export $i "memory" (core memory))        ;; core memory 0 (prog's memory 1)
  (alias core export $i "cabi_realloc" (core func))    ;; core func 0
  (alias core export $i "check-stream" (core func))    ;; core func 1
  (alias core export $i "check-nested" (core func))    ;; core func 2
  (type (list s32))                                    ;; type 0
  (type (list s32))                                    ;; type 1
  (type (func (param "problem" 0) (param "cert" 1) (result bool)))    ;; type 2
  (type (list s32))                                    ;; type 3
  (type (list 3))                                      ;; type 4: list<list<s32>>
  (type (list s32))                                    ;; type 5
  (type (func (param "problem" 4) (param "cert" 5) (result bool)))    ;; type 6
  (func (canon lift (core func 1) (memory 0) (realloc 0) (type 2)))   ;; func 0
  (func (canon lift (core func 2) (memory 0) (realloc 0) (type 6)))   ;; func 1
  (export "check-stream" (func 0))
  (export "check-nested" (func 1)))
```

`LInvL s t` is the store invariant under which `cabi_realloc` is a bump allocator for memory
address `1` (`Silmaril.Wasm.Component.Reference.ListLift.BumpAlloc`): the store is a store of
the acceptor (`AccStore`: the instance's functions, any LRAT state, the 1 MiB ABI memory) whose
heap pointer is `t ≤ memBytes`.

`coreBytes` is silmaril-lean's encoding of `prog` (`Binaryen.Exe.encodeModule?`) and `bytes` the
component's (`Binary.encode`); `examples/wasm-acceptors/lrat_accept.wasm` holds them. What the
exports compute is stated in `Silmaril.Wasm.Examples.LratAccept.Component.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Examples.LratAccept

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Component.Reference.ListLift

/-- **The LRAT acceptor component.** -/
def lratComp : ListComp where
  mod := prog
  memName := "memory"
  memIdx := 1
  reallocName := "cabi_realloc"
  exports := [
    { name := "check-stream", params := [("problem", .list .s32), ("cert", .list .s32)],
      core := "check-stream" },
    { name := "check-nested", params := [("problem", .list (.list .s32)), ("cert", .list .s32)],
      core := "check-nested" }]

/-- The store invariant of the lowering with heap pointer `t`: a store of the acceptor (any LRAT
state, any ABI memory of `memBytes` bytes) with the heap pointer `t ≤ memBytes`. -/
def LInvL (s : Silmaril.Wasm.Execution.Core.Store Nat) (t : Nat) : Prop :=
  (∃ G B₀ B₁, AccStore s G B₀ (BitVec.ofNat 32 t) B₁) ∧ t ≤ memBytes

/-- The core module bytes: silmaril-lean's encoding of `prog`. -/
def coreBytes : ByteArray :=
  match Silmaril.Wasm.Binaryen.Exe.encodeModule? prog with
  | .ok bs => ⟨bs.toArray⟩
  | .error _ => .empty

/-- The component bytes. -/
def bytes : ByteArray := (encode (lratComp.toAst coreBytes)).getD .empty

end Silmaril.Wasm.Examples.LratAccept

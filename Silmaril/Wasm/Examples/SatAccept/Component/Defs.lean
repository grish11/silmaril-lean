module

public import Silmaril.Wasm.Examples.SatAccept.Defs
public import Silmaril.Wasm.Component.Binary.Encode.Defs
public import Silmaril.Wasm.Binaryen.Exe.Encode

/-!
# The SAT model-witness acceptor as a component: the binary

`compAst core` is the component binary (abstract syntax, `Silmaril.Wasm.Component.Binary.Ast`)
wrapping the core module bytes `core`:

```wat
(component
  (core module $m …)                        ;; core module 0: `prog`
  (core instance $i (instantiate $m))       ;; core instance 0
  (alias core export $i "memory" (core memory))        ;; core memory 0
  (alias core export $i "cabi_realloc" (core func))    ;; core func 0
  (alias core export $i "check-stream" (core func))    ;; core func 1
  (alias core export $i "check-nested" (core func))    ;; core func 2
  (type (list s32))                                    ;; type 0
  (type (list 0))                                      ;; type 1: list<list<s32>>
  (type (func (param "problem" 0) (param "model" 0) (result bool)))   ;; type 2
  (type (func (param "problem" 1) (param "model" 0) (result bool)))   ;; type 3
  (func (canon lift (core func 1) (memory 0) (realloc 0) (type 2)))   ;; func 0
  (func (canon lift (core func 2) (memory 0) (realloc 0) (type 3)))   ;; func 1
  (export "check-stream" (func 0))
  (export "check-nested" (func 1)))
```

`coreBytes` is silmaril-lean's encoding of `prog` (`Binaryen.Exe.encodeModule?`) and `bytes` the
component's (`Binary.encode`); `examples/wasm-acceptors/sat_accept.wasm` holds them.

This file only defines the binary. What its exports compute is the subject of the core-level
specifications of `prog` and of the component-level soundness development; until those are in
place nothing here is a theorem about the binary's behaviour.
-/

@[expose] public section

namespace Silmaril.Wasm.Examples.SatAccept

open Silmaril.Wasm.Component.Binary

/-- **The component binary** around the core module bytes `core`. -/
def compAst (core : ByteArray) : Ast := .mk [
  .coreModule core,
  .coreInstances [.instantiate 0 []],
  .aliases [⟨.core .memory, .coreExport 0 "memory"⟩,
            ⟨.core .func, .coreExport 0 "cabi_realloc"⟩,
            ⟨.core .func, .coreExport 0 "check-stream"⟩,
            ⟨.core .func, .coreExport 0 "check-nested"⟩],
  .types [.val (.list (.prim .s32)),
          .val (.list (.idx 0)),
          .func ⟨[("problem", .idx 0), ("model", .idx 0)], some (.prim .bool), false⟩,
          .func ⟨[("problem", .idx 1), ("model", .idx 0)], some (.prim .bool), false⟩],
  .canons [.lift 1 [.memory 0, .realloc 0] 2, .lift 2 [.memory 0, .realloc 0] 3],
  .exports [⟨↑"check-stream", ⟨.func, 0⟩, none⟩, ⟨↑"check-nested", ⟨.func, 1⟩, none⟩]]

/-- The core module bytes: silmaril-lean's encoding of `prog`. -/
def coreBytes : ByteArray :=
  match Silmaril.Wasm.Binaryen.Exe.encodeModule? prog with
  | .ok bs => ⟨bs.toArray⟩
  | .error _ => .empty

/-- The component bytes. -/
def bytes : ByteArray := (encode (compAst coreBytes)).getD .empty

end Silmaril.Wasm.Examples.SatAccept

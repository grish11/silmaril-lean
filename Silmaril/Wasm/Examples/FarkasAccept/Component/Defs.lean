module

public import Silmaril.Wasm.Examples.FarkasAccept.Defs
public import Silmaril.Wasm.Component.Binary.Encode.Defs
public import Silmaril.Wasm.Binaryen.Exe.Encode

/-!
# The Farkas acceptor as a component: the binary

`compAst core` is the component binary (abstract syntax, `Silmaril.Wasm.Component.Binary.Ast`)
wrapping the core module bytes `core`:

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
records through named (exported or imported) types.

`coreBytes` is silmaril-lean's encoding of `prog` (`Binaryen.Exe.encodeModule?`) and `bytes` the
component's (`Binary.encode`); `examples/wasm-acceptors/farkas_accept.wasm` holds them.

This file only defines the binary. What its export computes is the subject of the core-level
specifications of `prog` (`Silmaril.Wasm.Examples.FarkasAccept.Thms`); no theorem here is about
the binary's behaviour.
-/

@[expose] public section

namespace Silmaril.Wasm.Examples.FarkasAccept

open Silmaril.Wasm.Component.Binary

/-- **The component binary** around the core module bytes `core`. -/
def compAst (core : ByteArray) : Ast := .mk [
  .coreModule core,
  .coreInstances [.instantiate 0 []],
  .aliases [⟨.core .memory, .coreExport 0 "memory"⟩,
            ⟨.core .func, .coreExport 0 "cabi_realloc"⟩,
            ⟨.core .func, .coreExport 0 "check"⟩],
  .types [.val (.tuple [.prim .u32, .prim .s64]),
          .val (.list (.idx 0)),
          .val (.record [("coeffs", .idx 1), ("bound", .prim .s64)])],
  .exports [⟨↑"ineq", ⟨.type, 2⟩, none⟩],
  .types [.val (.list (.idx 3)),
          .val (.list (.prim .s64)),
          .func ⟨[("system", .idx 4), ("y", .idx 5)], some (.prim .bool), false⟩],
  .canons [.lift 1 [.memory 0, .realloc 0] 6],
  .exports [⟨↑"check", ⟨.func, 0⟩, none⟩]]

/-- The core module bytes: silmaril-lean's encoding of `prog`. -/
def coreBytes : ByteArray :=
  match Silmaril.Wasm.Binaryen.Exe.encodeModule? prog with
  | .ok bs => ⟨bs.toArray⟩
  | .error _ => .empty

/-- The component bytes. -/
def bytes : ByteArray := (encode (compAst coreBytes)).getD .empty

end Silmaril.Wasm.Examples.FarkasAccept

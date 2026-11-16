module

public import Silmaril.Wasi.Component.Accept.Ref.Thms
public import Silmaril.Wasi.Component.Accept.Consequence.Defs
public meta import Silmaril.Wasi.Component.Accept.Ref.Defs

/-! # Component acceptors on the reference machine: examples

`acceptHiBytes` is a component binary (assembled and validated with upstream `wasm-tools`
1.263.0, custom sections stripped) of

```wat
(component
  (import "accept" (func $accept (param "bs" (list u8))))
  (core module $Libc (memory (export "mem") 1) (data (i32.const 1) "hi!"))
  (core instance $libc (instantiate $Libc))
  (core func $acc (canon lower (func $accept) (memory (core memory $libc "mem"))))
  (core module $M
    (import "env" "accept" (func $acc (param i32 i32)))
    (func (export "run") (call $acc (i32.const 1) (i32.const 3))))
  (core instance $m (instantiate $M (with "env" (instance (export "accept" (func $acc))))))
  (func $run (canon lift (core func $m "run")))
  (export "run" (func $run)))
```

It is a typical `accept(list<u8>)` component: the core code passes `(ptr, len)` and the
canonical ABI lifts the bytes `68 69 21` from linear memory.

* **Kernel-checked** (`decide +kernel`): it decodes and validates on the reference machine
  (`decodeValid_acceptHi`), while the component IR rejects it
  (`decodeBinary_acceptHi`: `list<u8>` does not lower).
* **Executable** (`#guard`, the native evaluator, not a kernel proof): instantiating it and
  invoking `run` on the Core 3.0 interpreter records `[list<u8> "hi!"]` (`runHi`).
* `hi_mem_of_runHi`: given that run, `"hi!"` is in `refBytesSystem` (by `refBytesSystem_of_run`,
  a kernel-checked soundness theorem). The hypothesis is exactly the `#guard`ed run. Kernel
  evaluation of this run needs a 64 KiB linear memory in the kernel, which exceeds kernel
  recursion depth today (`Wasm.KernelEval` memory representations are the pending remedy).
-/

@[expose] public section

namespace Silmaril.Wasi.Accept.Ref.Examples

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Engine

/-- The `accept(list<u8>)` component binary described above. -/
def acceptHiBytes : ByteArray := ⟨#[0, 97, 115, 109, 13, 0, 1, 0, 7, 11, 2, 112, 125, 64, 1, 2,
  98, 115, 0, 1, 0, 10, 11, 1, 0, 6, 97, 99, 99, 101, 112, 116, 1, 1, 1, 33, 0, 97, 115, 109, 1,
  0, 0, 0, 5, 3, 1, 0, 1, 7, 7, 1, 3, 109, 101, 109, 2, 0, 11, 9, 1, 0, 65, 1, 11, 3, 104, 105,
  33, 2, 4, 1, 0, 0, 0, 6, 9, 1, 0, 2, 1, 0, 3, 109, 101, 109, 8, 7, 1, 1, 0, 0, 1, 3, 0, 1, 60, 0,
  97, 115, 109, 1, 0, 0, 0, 1, 9, 2, 96, 2, 127, 127, 0, 96, 0, 0, 2, 14, 1, 3, 101, 110, 118, 6,
  97, 99, 99, 101, 112, 116, 0, 0, 3, 2, 1, 1, 7, 7, 1, 3, 114, 117, 110, 0, 1, 10, 10, 1, 8, 0,
  65, 1, 65, 3, 16, 0, 11, 2, 21, 2, 1, 1, 6, 97, 99, 99, 101, 112, 116, 0, 0, 0, 1, 1, 3, 101,
  110, 118, 18, 1, 7, 5, 1, 64, 0, 1, 0, 6, 9, 1, 0, 0, 1, 2, 3, 114, 117, 110, 8, 6, 1, 0, 0, 1,
  0, 2, 11, 9, 1, 0, 3, 114, 117, 110, 1, 1, 0]⟩

/-- The deterministic first-alternative oracle over the Core 3.0 engine. -/
abbrev first : Oracle Eng := Oracle.first

/-- `"hi!"`. -/
def hi : List UInt8 := [0x68, 0x69, 0x21]

theorem decodeValid_acceptHi : (decodeValid (prof := first.prof) acceptHiBytes).isSome = true := by
  decide +kernel

/-- The component IR cannot read it: `list<u8>` does not lower. -/
theorem decodeBinary_acceptHi : Silmaril.Wasi.Accept.ComponentAcceptor.decodeBinary acceptHiBytes = none := by
  decide +kernel

/-- Instantiate, invoke `run` once, and check that `accept` recorded `"hi!"`. -/
def runHi : Bool :=
  match decodeValid (prof := first.prof) acceptHiBytes with
  | none => false
  | some a =>
    match acceptRun (core3Exec Silmaril.Wasm.SingleThreaded.neverFail) first 4000 a.comp
        [("run", [])] with
    | none => false
    | some st => st.any fun args => Value.Val.beqList args [bytesVal hi]

#guard runHi

/-- **`"hi!"` is accepted by the binary**, given the executable run that `#guard runHi` checks. -/
theorem hi_mem_of_runHi
    (h : ∃ a st, decodeValid (prof := first.prof) acceptHiBytes = some a ∧
      acceptRun (core3Exec Silmaril.Wasm.SingleThreaded.neverFail) first 4000 a.comp
        [("run", [])] = some st ∧ [bytesVal hi] ∈ st) :
    refBytesSystem first.prof acceptHiBytes hi :=
  let ⟨_, _, hd, hr, hw⟩ := h
  refBytesSystem_of_run first hd hr hw

end Silmaril.Wasi.Accept.Ref.Examples

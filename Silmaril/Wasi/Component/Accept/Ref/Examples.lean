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
* **Kernel-checked end to end** (`decide +kernel`): instantiating it and invoking `run` on the
  Core 3.0 interpreter records `[list<u8> "hi!"]` (`hiRecorded_records`), so `"hi!"` is in
  `bytesSystemUntyped` (`hi_mem_direct`). The run uses a 64 KiB linear memory with a data segment. The
  kernel evaluates it because Core's memory writes go through `Memory.writeSlice`, which shares
  the memory after the written range (`ByteArray.copySlice` rebuilds it and exceeds the
  kernel's recursion depth). `#guard runHi` keeps a native regression check.
* **Exported shape** (`exportLen3Bytes`, `accept: func(list<u8>) -> bool` returning
  `len == 3`): it decodes and validates in the kernel. The kernel evaluates calls returning
  `true` on `"hi!"` and `false` on `"hi"` (`exportCall_hi`, `exportCall_hi2`), with the
  argument stored at address 1024 by `realloc`. `acceptedExport_of_run` turns such a run into
  `AcceptedExport`.
* `hi_mem_of_runHi` and `hi_mem_typed_of_run` (`Typed/Examples.lean`) are the
  untyped and typed soundness results given their respective runs.
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

/-- The run of `runHi`, kept as data: the decoded acceptor and the recorded argument lists. -/
def hiRecorded : Option (RefAcceptor first.prof × AcceptSt) :=
  (decodeValid (prof := first.prof) acceptHiBytes).bind fun a =>
    (acceptRun (core3Exec Silmaril.Wasm.SingleThreaded.neverFail) first 4000 a.comp
      [("run", [])]).map fun st => (a, st)

/-- **The kernel evaluates the whole run**: decoding, validation, linking, instantiation with a
64 KiB linear memory and its data segment, the call, the core code's `accept(1, 3)` and the
canonical-ABI lift of `list<u8>` from memory (`decide +kernel`; Core's memory writes are
`Memory.writeSlice`, which the kernel evaluates without rebuilding the memory). -/
theorem hiRecorded_records :
    hiRecorded.any (fun p => decide ([bytesVal hi] ∈ p.2)) = true := by
  decide +kernel

/-- **`"hi!"` is accepted by the binary** (kernel-checked end to end). -/
theorem hi_mem_direct : bytesSystemUntyped first.prof acceptHiBytes hi := by
  have h := hiRecorded_records
  unfold hiRecorded at h
  obtain ⟨⟨a, st⟩, hp, hm⟩ := (Option.any_eq_true _ _).mp h
  obtain ⟨a', ha, hr⟩ := Option.bind_eq_some_iff.mp hp
  obtain ⟨st', hst, he⟩ := Option.map_eq_some_iff.mp hr
  cases he
  exact bytesSystemWith_of_run EnvPolicy.untyped first ha hst (of_decide_eq_true hm)

/-- Given the executable run that `#guard runHi` checks, `"hi!"` is in `bytesSystemUntyped`
(`hi_mem_direct` now proves it outright). -/
theorem hi_mem_of_runHi
    (h : ∃ a st, decodeValid (prof := first.prof) acceptHiBytes = some a ∧
      acceptRun (core3Exec Silmaril.Wasm.SingleThreaded.neverFail) first 4000 a.comp
        [("run", [])] = some st ∧ [bytesVal hi] ∈ st) :
    bytesSystemUntyped first.prof acceptHiBytes hi :=
  let ⟨_, _, hd, hr, hw⟩ := h
  bytesSystemWith_of_run _ first hd hr hw

/-! ## Exported `accept: func(list<u8>) -> bool`

`exportLen3Bytes` (assembled and validated with `wasm-tools` 1.263.0, stripped) has no imports. It
exports `accept: func(bs: list<u8>) -> bool`, lifted with a memory and a bump-allocator
`realloc`, and its core function returns `len == 3`. -/

/-- The exported-`accept` component binary. -/
def exportLen3Bytes : ByteArray := ⟨#[0, 97, 115, 109, 13, 0, 1, 0, 1, 101, 0, 97, 115, 109, 1,
  0, 0, 0, 1, 15, 2, 96, 4, 127, 127, 127, 127, 1, 127, 96, 2, 127, 127, 1, 127, 3, 3, 2, 0, 1, 5,
  3, 1, 0, 1, 6, 7, 1, 127, 1, 65, 128, 8, 11, 7, 26, 3, 3, 109, 101, 109, 2, 0, 7, 114, 101, 97,
  108, 108, 111, 99, 0, 0, 6, 97, 99, 99, 101, 112, 116, 0, 1, 10, 27, 2, 17, 1, 1, 127, 35, 0, 33,
  4, 35, 0, 32, 3, 106, 36, 0, 32, 4, 11, 7, 0, 32, 1, 65, 3, 70, 11, 2, 4, 1, 0, 0, 0, 7, 11, 2,
  112, 125, 64, 1, 2, 98, 115, 0, 0, 127, 6, 32, 3, 0, 0, 1, 0, 6, 97, 99, 99, 101, 112, 116, 0, 2,
  1, 0, 3, 109, 101, 109, 0, 0, 1, 0, 7, 114, 101, 97, 108, 108, 111, 99, 8, 10, 1, 0, 0, 0, 2, 3,
  0, 4, 1, 1, 11, 12, 1, 0, 6, 97, 99, 99, 101, 112, 116, 1, 0, 0]⟩

theorem decodeValid_exportLen3 :
    (decodeValid (prof := first.prof) exportLen3Bytes).isSome = true := by
  decide +kernel

/-- Instantiate with no imports, call `accept` on `w`, and read the `bool` it returns. -/
def exportCall (w : List UInt8) : Option Bool :=
  match decodeValid (prof := first.prof) exportLen3Bytes with
  | none => none
  | some a =>
    match (emb (core3Exec Silmaril.Wasm.SingleThreaded.neverFail)).instantiateRun first 4000
        a.comp [] (Silmaril.Wasm.Component.Reference.initConfig []) with
    | none => none
    | some (r₁, _, es) =>
      match es.lookup "accept" with
      | none => none
      | some f =>
        match (emb (core3Exec Silmaril.Wasm.SingleThreaded.neverFail)).callTop first 4000 ⟨0⟩ f
            [bytesVal w] r₁.config with
        | none => none
        | some r =>
          match callOutcome? ⟨0⟩ r with
          | some (.resolved (some [.bool b])) => some b
          | _ => none

#guard exportCall hi == some true
#guard exportCall [0x68, 0x69] == some false

/-- The exported acceptor returns `true` on `"hi!"` and `false` on `"hi"`, evaluated by the kernel:
`realloc` places the argument at address 1024 of a 64 KiB memory and the canonical ABI stores it
there (`Memory.writeSlice`). -/
theorem exportCall_hi : exportCall hi = some true := by decide +kernel
theorem exportCall_hi2 : exportCall [0x68, 0x69] = some false := by decide +kernel

end Silmaril.Wasi.Accept.Ref.Examples

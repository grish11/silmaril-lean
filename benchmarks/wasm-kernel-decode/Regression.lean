module

import Quote
import Window

open Silmaril Silmaril.Wasm.Binary.Core WasmKernelBench

wasm_bench_defs embedded expected from "../../examples/wasm-acceptors/empty_check.wasm"

theorem agreed : decode? embedded.toByteArray = some expected := by wasm_check_source

example : (expected.funcs.head?.map (·.body)).isSome = true := rfl

private def header : List UInt8 := [0, 97, 115, 109, 1, 0, 0, 0]

private def malformed (tail : List UInt8) : ByteArray := ⟨⟨header ++ tail⟩⟩

example : decode? (malformed [1, 4, 1, 96]) = none := by wasm_check_source
example : decode? (malformed [1, 128, 128, 128, 128, 128, 0]) = none := by wasm_check_source
example : decode? (malformed [1, 4, 1, 96, 0, 0, 3, 2, 1, 0, 10, 4, 1, 1, 0, 11]) = none := by
  wasm_check_source
example : decode? (malformed [11, 4, 1, 1, 2, 42]) = none := by wasm_check_source
example : decode? ⟨⟨[0, 97, 115, 109, 2, 0, 0, 0]⟩⟩ = none := by wasm_check_source

kbytes_def spanSource of_chunks 2 4 [513, 1027]
kbytes_def spanExpected of_chunks 2 2 [770]

example : checkWindow spanSource 1 spanExpected = true := rfl
example : checkWindow spanSource 2 spanExpected = false := rfl
example : checkWindow spanSource 3 spanExpected = false := rfl

theorem spanAgreed : (Decode.readBytes 2).run ⟨spanSource.toByteArray, 1⟩ =
    .ok (spanExpected.toByteArray, ⟨spanSource.toByteArray, 3⟩) :=
  checkWindow_sound spanSource spanExpected 1 spanSource.wf_true spanExpected.wf_true rfl

#print axioms agreed
#print axioms spanAgreed
#print axioms Silmaril.Wasm.Perf.CoreDecode.decodeF_eq

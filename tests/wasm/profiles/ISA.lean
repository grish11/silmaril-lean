module

import Silmaril.Wasm.Profiles.ISA.Binary
import Silmaril.Wasm.Profiles.ISA.Versions

open Silmaril.Wasm Silmaril.Wasm.Validation
open Silmaril.Wasm.Profiles (Wasm1 Wasm2 Wasm3 Strict)
open Silmaril.Wasm.Profiles.ISA

example : Flat.lookup? (.primary 0x6d) = some .divS32 := rfl
example : Flat.lookup? (.primary 0x6e) = some .divU32 := rfl
example : Flat.lookup? (.primary 0xff) = none := rfl
example : Flat.lookup? (.primary 0xfc) = none := rfl
example : Flat.lookup? (.prefixed .misc 10) = none := rfl
example : Flat.lookup? (.prefixed .simd 128) = none := rfl
example : (Opcode.prefixed .simd 128).bytes = [0xfd, 0x80, 0x01] := by decide +kernel
example : (Opcode.prefixed .atomic 0x100).bytes = [0xfe, 0x80, 0x02] := by decide +kernel

example : (Admitted.lookup? Wasm1 (.primary 0xc4)).isSome = false := by decide +kernel
example : (Admitted.lookup? Wasm2 (.primary 0xc4)).isSome = true := by decide +kernel
example : (Admitted.lookup? Wasm1 (.prefixed .misc 0)).isSome = false := by decide +kernel
example : (Admitted.lookup? Wasm2 (.prefixed .misc 0)).isSome = true := by decide +kernel
example : (Admitted.lookup? Wasm2 (.prefixed .gc 28)).isSome = false := by decide +kernel
example : (Admitted.lookup? Wasm3 (.prefixed .gc 28)).isSome = true := by decide +kernel
example : (Admitted.lookup? Strict (.prefixed .gc 28)).isSome = true := by decide +kernel

example : (Flat.divU64.typed.toV1?).map V1.Instr.toCore = some (.intBinOp .i64 (.div .unsigned)) := rfl
example : Flat.truncSatS32F32.typed.toV2?.bind V2.Instr.toCore =
    some (.convert (.truncSat .f32 .i32 .signed)) := rfl

example : IsEmpty (Op [.i32] [.i64]) := ⟨fun op => by cases op⟩
example : (Flat.factoredEquiv .divU64).erase = .intBinOp .i64 (.div .unsigned) := by
  rw [Flat.factoredEquiv_erase]; rfl
example (ctx : Context) : InstrOk ctx Flat.divS32.erase (.plain [.i32, .i32] [.i32]) := Flat.divS32.sound ctx
example : (Flat.At.equiv [.i64] [.i64]).symm ((Flat.At.equiv [.i64] [.i64]) (.exact .extend32S64)) =
    .exact .extend32S64 := (Flat.At.equiv [.i64] [.i64]).left_inv _

private def overlong : ByteArray := ⟨#[0xfc, 0x80, 0x00, 0x0b]⟩

example : readOne.run ⟨overlong, 0⟩ = .ok (Flat.truncSatS32F32.erase, ⟨overlong, 3⟩) := rfl

example : (match readOne.run ⟨⟨#[0xfc, 0x80]⟩, 0⟩ with | .error _ => true | _ => false) = true := rfl
example : (match readOne.run ⟨⟨#[0xff]⟩, 0⟩ with | .error _ => true | _ => false) = true := rfl

#print axioms Flat.equiv
#print axioms Flat.At.equiv
#print axioms Flat.factoredEquiv_erase
#print axioms Flat.lookup?_some
#print axioms Admitted.lookup?_some
#print axioms Flat.toV1_core
#print axioms Flat.toV2_core
#print axioms Op.sound
#print axioms Flat.encodes
#print axioms Flat.readOne_bytes

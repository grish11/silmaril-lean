module

public import Silmaril.Project.Formats.Wasm.Defs
public import Silmaril.Wasm.Binaryen.Exe.EncodeSound
public import Silmaril.Wasm.Binary.Core.DecodeSound

/-! # Proofs of the `wasm.binary.core` printer and certificate lemmas (restated in
`Silmaril.Project.Formats.Wasm.Thms`) -/

@[expose] public section

namespace Silmaril.Proofs.Project.Formats

open Silmaril.Wasm Silmaril.Project Silmaril.Project.Formats

theorem wasm_print_sound {p} (hp : wasm.print = some p) {m : Silmaril.Wasm.Module}
    {b : Silmaril.Formats.Bytes} (h : p m = some b) : WasmRel b m := by
  cases hp
  cases he : Binaryen.Exe.encodeModule? m with
  | error => simp [he] at h
  | ok bs =>
    simp only [he] at h
    cases h
    simpa [WasmRel, Silmaril.Formats.Bytes.toList] using Binaryen.Exe.encodeModule?_sound he

theorem wasm_is_of_encode {X : Value Silmaril.Wasm.Module} (hf : X.format = wasm)
    {m : Silmaril.Wasm.Module}
    (he : (Binaryen.Exe.encodeModule? m).toOption = some X.bytes.toList) (hp : X.Parses) :
    X.Is m := by
  obtain ⟨m', hm'⟩ := Option.isSome_iff_exists.mp hp
  have hd : wasm.parse X.bytes = some m' := hf ▸ hm'
  have he' : Binaryen.Exe.encodeModule? m = .ok X.bytes.toList := by
    revert he; cases Binaryen.Exe.encodeModule? m <;> simp [Except.toOption]
  have hr : WasmRel X.bytes m := Binaryen.Exe.encodeModule?_sound he'
  have hd' : WasmRel X.bytes m' := Binary.Core.decode?_sound hd
  have heq : m' = m := Binary.Core.functional hd' hr
  show X.format.parse X.bytes = some m
  rw [hf, hd, heq]

end Silmaril.Proofs.Project.Formats

module
public import Silmaril.Project.Formats.Wasm.Defs
public import Silmaril.Wasm.Binary.Core.DecodeSound
public import Silmaril.Wasm.Binaryen.Exe.EncodeSound
public import Silmaril.Data.IncludeBytes
import Silmaril.Proofs.Project.Formats.Wasm

/-!
# Format `wasm.binary.core`: laws and example

* `wasm_sound` (registered law `sound`): the decoder is sound for `WasmRel`, from
  silmaril-lean's `Binary.Core.decode?_sound`.
* `wasm_print_sound`, `wasm_print_parse`: the printer is sound, and parsing printed bytes
  returns the printed module or fails (from `encodeModule?_sound` and the functionality of
  the binary grammar). This is not the `roundtrip` law, which also needs the parse to succeed.
* `wasm_is_of_encode`: a module certificate for a project value. If the value's bytes parse
  and are exactly `encodeModule? m`, they parse to `m`. Both premises are kernel `Bool`
  evaluations (`silmaril_decide`), so no decidable equality of module ASTs is needed.
* An example on `examples/project-formats/example.wasm`.
-/

@[expose] public section
namespace Silmaril.Project.Formats

open Silmaril.Wasm

theorem wasm_sound : wasm.SoundFor WasmRel :=
  fun _ _ h => Binary.Core.decode?_sound h

theorem wasm_print_sound {p} (hp : wasm.print = some p) {m : Silmaril.Wasm.Module}
    {b : Silmaril.Formats.Bytes} (h : p m = some b) : WasmRel b m :=
  Silmaril.Proofs.Project.Formats.wasm_print_sound hp h

theorem wasm_print_parse {p} (hp : wasm.print = some p) {m m' : Silmaril.Wasm.Module}
    {b : Silmaril.Formats.Bytes} (h : p m = some b) (h' : wasm.parse b = some m') : m' = m :=
  Binary.Core.functional (wasm_sound _ _ h') (wasm_print_sound hp h)

/-- `examples/project-formats/example.wasm`, the binary of `example.wat`. -/
def exampleWasm : Silmaril.Formats.Bytes :=
  ⟨include_bytes "../../../../examples/project-formats/example.wasm"⟩

theorem exampleWasm_parses : (wasm.parse exampleWasm).isSome = true := by decide +kernel

/-- A certificate of a core-module value from the encoder: if the bytes parse and are
exactly `encodeModule? m`, they parse to `m` (by `decode?_sound`, `encodeModule?_sound` and
the functionality of the binary grammar). -/
theorem wasm_is_of_encode {X : Silmaril.Project.Value Silmaril.Wasm.Module} (hf : X.format = wasm)
    {m : Silmaril.Wasm.Module}
    (he : (Binaryen.Exe.encodeModule? m).toOption = some X.bytes.toList) (hp : X.Parses) :
    X.Is m :=
  Silmaril.Proofs.Project.Formats.wasm_is_of_encode hf he hp

end Silmaril.Project.Formats

silmaril format_law wasm.binary.core sound := Silmaril.Project.Formats.wasm_sound
  (rel := Silmaril.Project.Formats.WasmRel)

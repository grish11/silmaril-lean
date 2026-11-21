module

public import Silmaril.Wasm.Validation.Check.Validate

@[expose] public section

namespace WasmRawExample

open Silmaril Silmaril.Wasm Silmaril.Wasm.Validation

def signature : RecType := ⟨[⟨true, [], .func ⟨[.i32], [.i32]⟩⟩]⟩

def closed : DefType := (Context.rollGroup {} signature)[0]'(by decide +kernel)

def interface : CModuleType := ⟨[.func closed], []⟩

def raw : Wasm.Module := {
  types := [signature]
  imports := [⟨"host", "transform", .func ⟨0⟩⟩]
  funcs := [⟨⟨0⟩, [], [.block (.value .i32) [.localGet ⟨0⟩, .call ⟨0⟩]]⟩] }

end WasmRawExample

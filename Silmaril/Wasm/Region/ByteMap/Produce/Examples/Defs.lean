module

public import Silmaril.Wasm.Region.ByteMap.Produce.Thms
public import Silmaril.Wasm.Region.ByteMap.Nested.Examples.Defs

@[expose] public section
namespace Silmaril.Wasm.Region.ByteMap.Produce.Examples
open Silmaril.Wasm.Binary Silmaril.Wasm.Binary.Core

/-- One function import and one global import: function indices shift by one,
not by the total import count of two. Both definitions have identical bodies. -/
def duplicate : List UInt8 :=
  magic ++ version ++
    [1, 4, 1, 0x60, 0, 0] ++
    [2, 10, 2, 0, 0, 0, 0, 0, 0, 3, 0x7f, 0] ++
    [3, 3, 2, 0, 0] ++
    -- A custom section contains a decoy copy of the same body bytes.
    [0, 10, 0] ++ Nested.Examples.nested.bytes ++
    [10, 21, 2, 9] ++ Nested.Examples.nested.bytes ++
    [9] ++ Nested.Examples.nested.bytes

def single (body : List UInt8) : List UInt8 :=
  magic ++ version ++ [1, 4, 1, 0x60, 0, 0, 3, 2, 1, 0] ++
    [10, UInt8.ofNat (body.length + 2), 1, UInt8.ofNat body.length] ++ body

def conditional := single Nested.Examples.conditional.bytes
def handler := single Nested.Examples.handler.bytes
def prefixed := single Nested.Examples.prefixed.bytes
def noElse := single Nested.Examples.noElse.bytes

/-- Small observable projection: accepted source coordinates and raw row count,
without serializing proof fields or claiming that native evaluation is a proof. -/
def stats? (raw : List UInt8) : Option (List (Nat × Nat × Nat)) := do
  let m ← module? raw
  pure ((List.finRange m.source.layout.bodies.length).map fun i =>
    ((m.source.layout.bodies[i]).input.functionIndex, m.source.layout.bodyStart i.val,
      (m.maps i).certified.map.entries.length))

def wrongIndexRejected? : Option Bool := do
  let m ← Silmaril.Wasm.Binary.Core.decode? ⟨duplicate.toArray⟩
  let layout ← layout? duplicate m
  let first ← layout.bodies.head?
  let wrong := { first with input := { first.input with functionIndex := 0 } }
  pure (ModuleSource.validate? duplicate { layout with bodies := wrong :: layout.bodies.drop 1 }).isNone

def customSectionRejected? : Option Bool := do
  let m ← Silmaril.Wasm.Binary.Core.decode? ⟨duplicate.toArray⟩
  let layout ← layout? duplicate m
  pure (ModuleSource.validate? duplicate { layout with codeSection := 3 }).isNone

end Silmaril.Wasm.Region.ByteMap.Produce.Examples

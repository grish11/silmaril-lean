module

public import Silmaril.Wasm.Component.Reference.ListLift.Defs
public import Silmaril.Wasm.Component.Binary.Encode.Defs
public import Silmaril.Wasm.Binaryen.Exe.Encode

/-!
# The acceptor kit: the bytes of an acceptor component

An acceptor's bytes are two encodings of Lean values: the core module `m` by silmaril-lean's
encoder (`coreBytesOf m`, `Binaryen.Exe.encodeModule?`), and the component around them by the
component encoder (`ListComp.compBytes c core`, `Binary.encode` of the emitted
`ListComp.toAst c core`). The per-acceptor files (`examples/wasm-acceptors/*.wasm`) are these
bytes, written by regeneration; the generic decode and parse facts are in `Thms`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Acceptor

open Silmaril.Wasm.Component.Reference.ListLift (ListComp)

/-- The core module bytes of `m`: silmaril-lean's encoding (empty if it fails). -/
def coreBytesOf (m : Silmaril.Wasm.Module) : ByteArray :=
  match Silmaril.Wasm.Binaryen.Exe.encodeModule? m with
  | .ok bs => ⟨bs.toArray⟩
  | .error _ => .empty

/-- The component bytes of `c` around the core module bytes `core` (empty if encoding fails). -/
def compBytes (c : ListComp) (core : ByteArray) : ByteArray :=
  (Silmaril.Wasm.Component.Binary.encode (c.toAst core)).getD .empty

end Silmaril.Wasm.Acceptor

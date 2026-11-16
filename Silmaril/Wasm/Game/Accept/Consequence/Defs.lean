module

public import Silmaril.Wasm.Game.Accept.Acceptor.Defs
public import Silmaril.Logic.Consequence.Acceptor.Defs
public import Silmaril.Wasm.Binary.Core.Decode

/-! # Module acceptors as consequence systems

The three views of `Silmaril.Logic.Consequence.Acceptor`, for core modules:

* **acceptor**: `System.ofAcceptor ModuleAcceptor : System ModuleAcceptor (List UInt8)`, from the
  CSLib instance of `ModuleAcceptor` (`A ⊢ w` iff `w ∈ A.lang`);
* **module**: `A.moduleSystem : System Module (List UInt8)`, `m ⊢ w` iff `w ∈ (A.withModule m).lang`;
* **bytes**: `A.bytesSystem : System ByteArray (List UInt8)`, `b ⊢ w` iff `b` decodes
  (`Silmaril.Wasm.Binary.Core.decode?`) to a module `m` with `m ⊢ w`.

The interpreter is `A.withModule`: a template acceptor `A` fixes the profile, the `accept` and
`reject` imports, the memory, its address width and the admitted environments, and
`A.withModule m` puts the module `m` under that interpretation. The module of `A` itself is
ignored. Bytes that do not decode prove nothing: that is not a module that accepts nothing
(see `Silmaril.Wasi.Consequence.coreBytesInterp` for the `Option`-valued reading).

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasm.Game.Accept

open Silmaril.Consequence (System)

namespace ModuleAcceptor

variable (A : ModuleAcceptor)

/-- **The interpreter of a template acceptor**: the module `m` under `A`'s profile, imports,
memory and environments. -/
def withModule (m : Module) : ModuleAcceptor := { A with module := m }

/-- **Modules as a consequence system**: `m ⊢ w` iff `m`, read by `A.withModule`, accepts `w`. -/
def moduleSystem : System Module (List UInt8) := System.ofInterpreter A.withModule

/-- **Module binaries as a consequence system**: `b ⊢ w` iff `b` decodes to a module that
accepts `w`; bytes that do not decode prove nothing. -/
def bytesSystem : System ByteArray (List UInt8) :=
  System.ofDecoder Silmaril.Wasm.Binary.Core.decode? A.withModule

end ModuleAcceptor

end Silmaril.Wasm.Game.Accept

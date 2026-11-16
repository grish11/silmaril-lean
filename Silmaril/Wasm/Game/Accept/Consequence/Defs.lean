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

**Simple entry point**: `moduleBytesSystem` (optionally at a profile `P`) is the bytes view
under the default interpretation `ModuleAcceptor.default` (`env.accept(ptr: i32, len: i32)`,
memory 0, every Core host): no template is needed.

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
open Silmaril.Wasm.Numerics (Profile)

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

/-- **The default module interpretation**: `env.accept(ptr: i32, len: i32)` reading memory 0,
no `reject` import, every host meeting Core's host contract (`UEnvOk`), at the profile `P`
(the specification's by default). It is the interpretation registered as
`wasm.core.accept_bytes32`. The module field is a placeholder that `withModule` replaces. -/
def default (P : Profile := .spec) : ModuleAcceptor := { profile := P, module := {} }

/-- The module `m` under the default interpretation. -/
def ofModule (m : Module) (P : Profile := .spec) : ModuleAcceptor := (default P).withModule m

end ModuleAcceptor

/-- **Module binaries as a consequence system, default interpretation**: `b ⊢ w` iff `b` decodes
(`Binary.Core.decode?`) to a core module that passes `w` to `env.accept(ptr: i32, len: i32)`
in some run (profile `P`, every host meeting Core's contract). Component binaries and other
non-module bytes do not decode and prove nothing. For another interpretation, use
`ModuleAcceptor.bytesSystem` with a template. -/
def moduleBytesSystem (P : Profile := .spec) : System ByteArray (List UInt8) :=
  (ModuleAcceptor.default P).bytesSystem

end Silmaril.Wasm.Game.Accept

module

public import Silmaril.Wasm.Component.Binary.Lower.Sem.Defs
public import Silmaril.Wasm.Component.InstEngine.Defs
public import Silmaril.Wasm.Component.InstExport.Defs

/-! # Lowered core modules with their start functions

`Binary.coreModSem P` (`Silmaril.Wasm.Component.Binary.Lower.Sem`) runs each lowered core
module on the Core 3.0 engine through the start-free interface `CoreSem`: a module with a start
function has no instance there and traps on every question.

`coreModSemI P : CoreSemI CoreMod` is the same pipeline through the interface with an
instantiation phase: the module the bytes decode to (`coreModule`), its Core 3.0 engine
instance before its start function (`Param.instOfI`), and the engine semantics with an
instantiation phase (`Param.engineSemI`). The start function runs at instantiation, its import
calls are moves of the instantiation phase, and a trap of it fails the instantiation. Nothing
about execution is new: the construction composes the core decoder, `core3P P`, and
`engineSemI`.

* `coreModSemI P := engineSemI (core3P P) CoreMod coreModule`;
* `StartFree P cm`: the lowered module has an engine instance and no start function. On such
  modules `coreModSemI` and `coreModSem` agree after instantiation (`Binary.Lower.SemI.Thms`).

The binary entry points built on it are in `Silmaril.Wasi.Component.Accept.Inst`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Binary

open Silmaril.Wasm.Numerics (Profile)

/-- **The execution-based core semantics of lowered core modules with their start functions**,
at profile `P`: start functions run at instantiation. -/
noncomputable def coreModSemI (P : Profile) : CoreSemI CoreMod :=
  Silmaril.Wasm.Component.Param.engineSemI (Silmaril.Wasm.Component.Reference.core3P P) CoreMod
    coreModule

/-- The lowered module has a Core 3.0 engine instance at profile `P`, without a start
function. -/
def StartFree (P : Profile) (cm : CoreMod) : Prop :=
  ∃ J, Silmaril.Wasm.Component.Param.instOfI (Silmaril.Wasm.Component.Reference.core3P P)
    (coreModule cm) (CoreModule.imports cm) (CoreModule.exports cm) = some J ∧ J.start = none

end Silmaril.Wasm.Component.Binary

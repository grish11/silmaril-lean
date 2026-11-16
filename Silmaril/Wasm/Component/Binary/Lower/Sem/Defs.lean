module

public import Silmaril.Wasm.Component.Binary.Lower.Defs
public import Silmaril.Wasm.Component.Param.Defs
public import Silmaril.Wasm.Component.Param.Start.Defs
public import Silmaril.Wasm.Component.Reference.Defs

/-! # An execution-based core semantics for lowered core modules

`Binary.lower` turns a component binary into the component IR over `CoreMod`: each embedded core
module keeps its bytes and its function interface. The only core semantics of `CoreMod` in
the library was `Project.WasmComponents.topSem`, the loosest one (every core module may play
any legal play). Statements about components under it say nothing about their core code.

`coreModSem P` reads each lowered core module **by running it**. It is `Param.engineSemS`, the
game semantics of an engine instance including its start function, over the Core 3.0 engine at
profile `P`
(`Reference.core3P P`, the engine of the reference machine), applied to the module the bytes
decode to (`coreModule`). Nothing new is defined about execution. The construction composes the
existing core decoder, the existing engine and the existing engine semantics:

* `coreModule cm`: the module `cm.bytes` decodes to (`Binary.Core.decode?`). `Binary.lower` only
  builds a `CoreMod` after decoding its bytes (`Lower.coreMod`). The empty module is a fallback
  that lowered modules do not reach.
* `coreModSem P : CoreSem CoreMod := engineSemS (core3P P) CoreMod coreModule`.

Inherited from `engineSemS`, stated there: the imports of a core module are bound positionally
to host functions; a start function runs at the first export question, before it is served,
its import calls being import questions nested in that question; a trap of the start function
makes every question trap (`Param.Start`). On modules without a start function `engineSemS` is
`engineSem` (`Param.engineSemS_sem_of_noStart`).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Binary

open Silmaril.Wasm.Numerics (Profile)

/-- The Core 3.0 module a lowered core module's bytes decode to. -/
def coreModule (cm : CoreMod) : Silmaril.Wasm.Module :=
  (Silmaril.Wasm.Binary.Core.decode? cm.bytes).getD {}

/-- **The execution-based core semantics of lowered core modules** at profile `P`: the game
semantics of their Core 3.0 engine instances, start functions included. -/
noncomputable def coreModSem (P : Profile) : CoreSem CoreMod :=
  Silmaril.Wasm.Component.Param.engineSemS (Silmaril.Wasm.Component.Reference.core3P P) CoreMod
    coreModule

end Silmaril.Wasm.Component.Binary

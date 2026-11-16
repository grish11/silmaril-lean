module

public import Silmaril.Project.Shapes.Consequence.Defs
public import Silmaril.Project.Languages.WasmExport.Defs
public import Silmaril.Logic.Consequence.Accept.Defs

/-!
# Consequence systems of Wasm modules: the export `check` as a relation

Three interpretations through the same export; each is a `consequence_interpretation`:

* `wasm.core.check_acceptor`: unit contexts, `() ⊢ w` iff the module accepts `w` — the core
  adapter `liftTTC ()` of the language that `wasm.core.check_accept` reads (an acceptor);
* `wasm.core.check_rejector`: unit conclusions, `w ⊢ ()` iff the module rejects `w` —
  `liftAxFF · ()` of `wasm.core.check_reject`'s language (a rejector);
* `wasm.core.check_rel`, below.

`wasm.core.check_rel` reads a module as a consequence system between byte lists and bytes:
`as ⊢ c` iff some run of the export `check(ptr: i32, len: i32) -> i32` on the input
`c :: as` answers `1` (`Silmaril.Project.Languages.WasmExport.checkAccept`: the host writes the
input into memory 0 and invokes `check`, after spec instantiation, `Profile.spec`, every Core
host `allHosts`). The conclusion is the first byte and the assumptions the rest, the input
convention of `Silmaril.Wasm.Examples.MemberCheck.accepted`. Inputs and answers are bytes;
the ABI bounds inputs by `ptr + len < 2 ^ 32`, which the theorems about each module state.

Like the language interpretations it builds on, it reads a module AST, not bytes: a registered
artifact's system is this interpretation of the module its bytes decode to
(`Silmaril.Project.ConsequenceSystems.artifactSystem`), tied to a Lean module by the value's `.is`
certificate. That the ABI and environment occur in the definition is a check of the metadata,
not a proof that the definition models execution (the export semantics
`Silmaril.Wasm.Game.Accept.Export` is that model).
-/

@[expose] public section

namespace Silmaril.Project.ConsequenceSystems.WasmExport

open Silmaril.Project.Languages.WasmExport Silmaril.Wasm.Game Silmaril.Wasm.Game.Accept

/-- **Through the export `check`**: `as ⊢ c` iff some run answers `1` on `c :: as`. -/
def checkRel (m : Silmaril.Wasm.Module) : Silmaril.Consequence.System (List UInt8) UInt8 :=
  fun as c => c :: as ∈ exportAccepted Silmaril.Wasm.Numerics.Profile.spec allHosts m checkExport

/-- **The acceptor of the export `check`**, with unit contexts: `() ⊢ w` iff some run answers `1`
on `w` (the core adapter `liftTTC ()` of the language `WasmExport.checkAccept m`). -/
def checkAcceptor (m : Silmaril.Wasm.Module) : Silmaril.Consequence.System Unit (List UInt8) :=
  Silmaril.Consequence.liftTTC ()
    (exportAccepted Silmaril.Wasm.Numerics.Profile.spec allHosts m checkExport)

/-- **The rejector of the export `check`**, with unit conclusions: `w ⊢ ()` iff some run answers
`0` on `w` (the core adapter `liftAxFF · ()` of `WasmExport.checkReject m`). -/
def checkRejector (m : Silmaril.Wasm.Module) : Silmaril.Consequence.System (List UInt8) Unit :=
  Silmaril.Consequence.liftAxFF
    (exportRejected Silmaril.Wasm.Numerics.Profile.spec allHosts m checkExport) ()

end Silmaril.Project.ConsequenceSystems.WasmExport

silmaril consequence_interpretation wasm.core.check_rel :=
  Silmaril.Project.ConsequenceSystems.WasmExport.checkRel
  (abi := Silmaril.Project.Languages.WasmExport.checkExport)
  (environment := Silmaril.Project.Languages.WasmExport.allHosts)
  (doc := "as ⊢ c iff some run of the export check(ptr: i32, len: i32) -> i32 answers 1 on the input c :: as written into memory 0, after spec instantiation, Profile.spec, every Core host (Silmaril.Wasm.Game.Accept.exportAccepted)")

silmaril consequence_interpretation wasm.core.check_acceptor :=
  Silmaril.Project.ConsequenceSystems.WasmExport.checkAcceptor
  (abi := Silmaril.Project.Languages.WasmExport.checkExport)
  (environment := Silmaril.Project.Languages.WasmExport.allHosts)
  (doc := "() ⊢ w iff some run of the export check(ptr: i32, len: i32) -> i32 answers 1 on w: liftTTC () of the language wasm.core.check_accept reads (Profile.spec, every Core host)")

silmaril consequence_interpretation wasm.core.check_rejector :=
  Silmaril.Project.ConsequenceSystems.WasmExport.checkRejector
  (abi := Silmaril.Project.Languages.WasmExport.checkExport)
  (environment := Silmaril.Project.Languages.WasmExport.allHosts)
  (doc := "w ⊢ () iff some run of the export check(ptr: i32, len: i32) -> i32 answers 0 on w: liftAxFF · () of the language wasm.core.check_reject reads (Profile.spec, every Core host)")

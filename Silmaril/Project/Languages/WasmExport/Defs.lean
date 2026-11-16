module

public import Silmaril.Project.Shapes.Language.Defs
public import Silmaril.Wasm.Game.Accept.Defs
public import Silmaril.Wasm.Game.Accept.Reject.Defs
public import Silmaril.Wasm.Game.Accept.Export.Defs

/-!
# Languages of Wasm modules: export and combined interpretations

More interpretations for the `language` constructor `op := artifact`, beside
`wasm.core.accept_bytes32` (`Silmaril.Project.Languages.Wasm`). Each one names the execution
semantics, the ABI (how an input reaches the module and how its answer is read) and the
admitted environments; the artifact's bytes alone do not determine a language.

| interpretation | definition | ABI | environment |
|---|---|---|---|
| `wasm.core.export_accept` | `exportAccepted Profile.spec allHosts m acceptExport` | `acceptExport`: the host writes the input into memory 0 and invokes the export `accept(ptr: i32, len: i32) -> i32`; `[i32 1]` accepts | `allHosts`: every Core host relation |
| `wasm.core.export_reject` | `exportRejected Profile.spec allHosts m acceptExport` | the same export; `[i32 0]` rejects | `allHosts` |
| `wasm.core.export_accept_safely` | `exportAcceptedNotRejected Profile.spec allHosts m acceptExport` | the same export; some run answers `1` and none answers `0` | `allHosts` |
| `wasm.core.accept_bytes64` | `accepted Callout.bytes64 Profile.spec UEnvOk 0 acceptImport m` | `Callout.bytes64`: `env.accept(ptr: i64, len: i64)`, bytes of a 64-bit memory 0 | `UEnvOk`: every host meeting Core's host contract |
| `wasm.core.accept_safely_bytes32` | `acceptedNotRejected Callout.bytes32 Profile.spec UEnvOk 0 acceptImport rejectImport m` | `Callout.bytes32` at `env.accept`, and at `env.reject` (`rejectImport`, part of the definition) | `UEnvOk` |

The semantics are `Silmaril.Wasm.Game.Accept` (import callouts) and
`Silmaril.Wasm.Game.Accept.Export` (export embedding after spec instantiation). Every
interpretation reads a module AST (`Silmaril.Wasm.Module`), not bytes: an artifact's language
is the interpretation of the module its CID-pinned bytes decode to under the project's `wasm`
format. Whether those bytes decode to a given Lean module is a separate, checked claim (a
value's `.is` problem), the trust boundary between the binary and the AST the theorems are
about.

Only core modules are interpreted. Components, specification strategies and call/I-O readings
of the acceptor catalog (`Silmaril.Wasi.Accept.Catalog`) are not byte languages of a binary
here.
-/

@[expose] public section

namespace Silmaril.Project.Languages.WasmExport

open Silmaril.Wasm.Game Silmaril.Wasm.Game.Accept
open Silmaril.Wasm.Execution.Core (HostSemantics)

/-- The export ABI: the host writes the input into memory `0` and invokes the export named
`"accept"` with `[i32 ptr, i32 len]` (in bounds, `ptr + len < 2 ^ 32`); it answers `[i32 1]`
(accept) or `[i32 0]` (reject). -/
def acceptExport : String := "accept"

/-- The rejecting import: `"env" "reject"`. -/
def rejectImport : String × String := ("env", "reject")

/-- The admitted hosts of the export embedding: every Core host relation. -/
def allHosts : Set (HostSemantics Nat) := Set.univ

/-- **Accepted through the export**: some run of the embedding answers `1`. -/
def exportAccept (m : Silmaril.Wasm.Module) : Set (List UInt8) :=
  exportAccepted (Silmaril.Wasm.Numerics.Profile.spec) allHosts m acceptExport

/-- **Rejected through the export**: some run of the embedding answers `0`. -/
def exportReject (m : Silmaril.Wasm.Module) : Set (List UInt8) :=
  exportRejected (Silmaril.Wasm.Numerics.Profile.spec) allHosts m acceptExport

/-- **Accepted and never rejected through the export**, over the same runs. -/
def exportAcceptSafely (m : Silmaril.Wasm.Module) : Set (List UInt8) :=
  exportAcceptedNotRejected (Silmaril.Wasm.Numerics.Profile.spec) allHosts m acceptExport

/-- **The bytes a core module passes to `env.accept(ptr: i64, len: i64)`** (memory64). -/
def acceptBytes64 (m : Silmaril.Wasm.Module) : Set (List UInt8) :=
  accepted Callout.bytes64 (Silmaril.Wasm.Numerics.Profile.spec) UEnvOk 0 acceptImport m

/-- **Passed to `env.accept(ptr: i32, len: i32)` by some run and to `env.reject` by none.** -/
def acceptSafelyBytes32 (m : Silmaril.Wasm.Module) : Set (List UInt8) :=
  acceptedNotRejected Callout.bytes32 (Silmaril.Wasm.Numerics.Profile.spec) UEnvOk 0
    acceptImport rejectImport m

end Silmaril.Project.Languages.WasmExport

silmaril language_interpretation wasm.core.export_accept :=
  Silmaril.Project.Languages.WasmExport.exportAccept (domain := bytes)
  (abi := Silmaril.Project.Languages.WasmExport.acceptExport)
  (environment := Silmaril.Project.Languages.WasmExport.allHosts)
  (doc := "Inputs written into memory 0 on which some run of the export accept(ptr: i32, len: i32) -> i32 returns 1, after spec instantiation, Profile.spec, every Core host (Silmaril.Wasm.Game.Accept.exportAccepted)")

silmaril language_interpretation wasm.core.export_reject :=
  Silmaril.Project.Languages.WasmExport.exportReject (domain := bytes)
  (abi := Silmaril.Project.Languages.WasmExport.acceptExport)
  (environment := Silmaril.Project.Languages.WasmExport.allHosts)
  (doc := "Inputs written into memory 0 on which some run of the export accept(ptr: i32, len: i32) -> i32 returns 0, after spec instantiation, Profile.spec, every Core host (Silmaril.Wasm.Game.Accept.exportRejected)")

silmaril language_interpretation wasm.core.export_accept_safely :=
  Silmaril.Project.Languages.WasmExport.exportAcceptSafely (domain := bytes)
  (abi := Silmaril.Project.Languages.WasmExport.acceptExport)
  (environment := Silmaril.Project.Languages.WasmExport.allHosts)
  (doc := "Inputs on which some run of the export accept(ptr: i32, len: i32) -> i32 returns 1 and none returns 0, Profile.spec, every Core host (Silmaril.Wasm.Game.Accept.exportAcceptedNotRejected)")

silmaril language_interpretation wasm.core.accept_bytes64 :=
  Silmaril.Project.Languages.WasmExport.acceptBytes64 (domain := bytes)
  (abi := Silmaril.Wasm.Game.Accept.Callout.bytes64) (environment := Silmaril.Wasm.Game.UEnvOk)
  (doc := "Bytes passed to env.accept(ptr: i64, len: i64) from a 64-bit memory 0, Profile.spec, every host meeting Core's host contract (Silmaril.Wasm.Game.Accept.accepted)")

silmaril language_interpretation wasm.core.accept_safely_bytes32 :=
  Silmaril.Project.Languages.WasmExport.acceptSafelyBytes32 (domain := bytes)
  (abi := Silmaril.Wasm.Game.Accept.Callout.bytes32)
  (environment := Silmaril.Wasm.Game.UEnvOk)
  (doc := "Bytes passed to env.accept(ptr: i32, len: i32) from memory 0 by some run and to env.reject(ptr: i32, len: i32) by none, Profile.spec, every host meeting Core's host contract (Silmaril.Wasm.Game.Accept.acceptedNotRejected)")

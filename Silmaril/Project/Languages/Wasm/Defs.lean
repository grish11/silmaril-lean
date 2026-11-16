module

public import Silmaril.Project.Shapes.Language.Defs
public import Silmaril.Wasm.Game.Accept.Defs

/-!
# Languages of Wasm modules: interpretations

A Wasm binary is not a language by itself. It denotes one only under an **interpretation**:
an execution semantics (a numeric profile), an ABI that says how an accepted value is read off
an observation (which import, which arguments, which memory), and the environments the module
may run against. This module registers such interpretations for the `language` constructor
`op := artifact` (`Silmaril.Project.Registry.Language.Defs`): a language is then the
interpretation of a CID-pinned project value of format `wasm`, and its identity records the
artifact's CID *and* the interpretation.

| interpretation | definition | ABI | environment |
|---|---|---|---|
| `wasm.core.accept_bytes32` | `Silmaril.Wasm.Game.Accept.accepted Callout.bytes32 (Profile.spec) UEnvOk 0 acceptImport m` | `Callout.bytes32`: `env.accept(ptr: i32, len: i32)`, the bytes of memory 0 at `[ptr, ptr + len)` | `UEnvOk`: every host that meets Core's host contract |

The semantics is `Silmaril.Wasm.Game.Accept` (finite runs of the Core 3.0 specification
semantics, with any number of export invocations); see its module documentation for the
scope (core modules whose imports are all functions). Acceptance is existential over runs and
environments, so membership is undecidable in general: a problem about such a language is
unknown until a proof is given. Browsing a project never executes a module.
-/

@[expose] public section

namespace Silmaril.Project.Languages.Wasm

open Silmaril.Wasm.Game.Accept

/-- **The bytes a core module passes to `env.accept(ptr: i32, len: i32)`**, at the
specification's numeric profile, against every host that meets Core's host contract. -/
def acceptBytes32 (m : Silmaril.Wasm.Module) : Set (List UInt8) :=
  accepted Callout.bytes32 (Silmaril.Wasm.Numerics.Profile.spec) Silmaril.Wasm.Game.UEnvOk 0
    acceptImport m

end Silmaril.Project.Languages.Wasm

silmaril language_interpretation wasm.core.accept_bytes32 :=
  Silmaril.Project.Languages.Wasm.acceptBytes32 (domain := bytes)
  (abi := Silmaril.Wasm.Game.Accept.Callout.bytes32) (environment := Silmaril.Wasm.Game.UEnvOk)
  (doc := "Bytes passed to env.accept(ptr: i32, len: i32) from memory 0, Profile.spec, every host meeting Core's host contract (Silmaril.Wasm.Game.Accept.accepted)")

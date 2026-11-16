module

public import Silmaril.Wasm.Component.Reference.WIT.Package.Defs
public import Silmaril.Wasm.Component.Reference.WIT.Interp.Defs

/-! # WIT packages next to WIT value interpretations: a combined-import regression

Both modules declare names in `Silmaril.Wasm.Component.WIT`. The package resolution environment
is `PackageEnv` and the value environment of the interpretation is `Env`, so the two modules can
be imported together. This module imports both, so a future clash fails the build.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.WIT

/-- The package resolution environment is a list of packages. -/
example : PackageEnv = List Package := rfl

/-- The value environment is the interpretation's structure. -/
example (R : Type) : Env Empty R := Env.closed R

end Silmaril.Wasm.Component.WIT

module

public import Silmaril.Wasm.Component.DWiring.Defs

/-!
# Refinement of divergence-observing core semantics

`DCoreSem.Le C C'`: every core module of `C` refines (`≤`: fewer finite plays, divergences and
infinite plays) the one of `C'`, the divergence-observing version of `CoreSem.Le`. The
denotations of `Silmaril.Wasm.Component.DWiring` are monotone in it
(`Silmaril.Wasm.Component.DWiringMono.Thms`).
-/

@[expose] public section

namespace Silmaril.Wasm.Component

open Silmaril.Games

variable {M : Type} [CoreModule M]

/-- Pointwise refinement of divergence-observing core semantics. -/
def DCoreSem.Le (C C' : DCoreSem M) : Prop := ∀ m, C.sem m ≤ C'.sem m

end Silmaril.Wasm.Component

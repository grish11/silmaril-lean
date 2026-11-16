module

public import Silmaril.Wasm.Institution.CompGraph.Defs
public import Silmaril.Wasm.Component.Reference.Core3Sem.Defs

/-!
# The component logic graph over Core 3.0

`Silmaril.Wasm.Institution.CompGraph` builds the logics of modules, nested and flat components,
programs and games for **any** core semantics `C : CoreSem M`. This topic instantiates it at
silmaril's Core 3.0 semantics, `core3Sem P` (`Silmaril.Wasm.Component.Reference.Core3Sem`):
core modules are numeric Core 3.0 instances (`NumInstance`), and a module's meaning is the
strategy of the instance at its instantiation store, at numeric profile `P`.

* `core3Graph P`: `compGraph (core3Sem P)`;
* `fullGraph₃ P host Env`: `fullGraph₂` at `core3Sem P`, the module-level reduction graph next to
  the component graph over Core 3.0.

**Scope.** The two halves of `fullGraph₃` still have **no edges between them**: the module logics
of the reduction graph use export signatures with behaviours (`exportSig`), the component logics
use the IR's dynamically typed game signatures (`sigU`), and no translation between their
sentences is defined. Component adequacy against the reference machine is proved for `Simple`
components only (`docs/projects/component-caveats.md`).

Theorems in `Silmaril.Wasm.Institution.Core3Graph.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Institution.Core3Graph

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Institution.CompGraph Silmaril.Wasm.Component.Reference

/-- The component logic graph over Core 3.0 at numeric profile `P`. -/
noncomputable abbrev core3Graph (P : Profile) := compGraph (core3Sem P)

/-- The module-level reduction graph and the component graph over Core 3.0, side by side. -/
noncomputable abbrev fullGraph₃ {H : Type} (P : Profile) (host : HostSemantics H)
    (Env : Module → Store H → List ExternAddr → Prop) :=
  fullGraph₂ (core3Sem P) P host Env

end Silmaril.Wasm.Institution.Core3Graph

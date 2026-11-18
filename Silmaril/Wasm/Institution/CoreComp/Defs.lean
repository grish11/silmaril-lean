module

public import Silmaril.Wasm.Institution.Core3Graph.Defs
public import Silmaril.Wasm.Institution.GameInst.Defs

/-!
# Core modules and components meet in the institution of game semantics

The core-module logics of the reduction graph (`Silmaril.Wasm.Institution.GameGraph`: Wasm
instances under the Core 3.0 reduction `wasmRed P host`, at export-name interfaces) and the
component logics over Core 3.0 (`Silmaril.Wasm.Institution.Core3Graph`: numeric Core 3.0
instances and components, at export-index interfaces) have no translation between their
sentences. Both, however, are logics of strategies, and both translate into the one
institution of game semantics `Silmaril.Games.GInst` through the game reading of
`Silmaril.Wasm.Institution.GameInst`:

* `reductionToGInst P host`: a Wasm instance goes to the strategy of its reduction
  (`GameInst.redCoHom` at `exportIfaces`, no imports);
* `core3ModuleToGInst P`: a numeric Core 3.0 instance goes to its component-level strategy
  `modU (core3Sem P) m` (the module logic's edge to the component game logic,
  `Components.moduleToGame`, then `GameInst.coHom` at `compIfaces`);
* `componentToGInst P`: a component goes to `Comp.denU (core3Sem P) c` the same way.

Each is a comorphism, and each is model-expansive (`Thms`), so validity and entailment in each
source logic are equivalent to validity and entailment of the translated sentences in `GInst`.
Statements about core modules and about components can therefore be put side by side, and
checked, in one institution.

**Scope.** This is a cospan through `GInst`, not a translation between the two families: a
`GInst` signature is a game, and the games of the two families differ (behaviour-answered
export calls `exportSig` versus the IR's payload-answered calls `sigU`). No theorem here says
that a Wasm instance and a numeric instance built from it satisfy corresponding sentences;
that needs a game morphism between the two signatures and an adequacy argument (for `Simple`
components, `Silmaril.Wasm.Component.Reference.Adequacy`).

Theorems in `Silmaril.Wasm.Institution.CoreComp.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Institution.CoreComp

open Silmaril.Logic.Institution Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Institution.Games Silmaril.Wasm.Institution.Components
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference

/-- Wasm instances under the Core 3.0 reduction, into `GInst`. -/
noncomputable def reductionToGInst {H : Type} (P : Profile) (host : HostSemantics H) :
    Inst.CoHom (redSem exportIfaces Silmaril.Games.Sig.empty (wasmRed P host)).inst
      Silmaril.Games.GInst :=
  GameInst.redCoHom exportIfaces Silmaril.Games.Sig.empty (wasmRed P host)

/-- Numeric Core 3.0 instances, read as components' core modules, into `GInst`. -/
noncomputable def core3ModuleToGInst (P : Profile) :
    Inst.CoHom (moduleSem (core3Sem P)).inst Silmaril.Games.GInst :=
  (moduleToGame (core3Sem P)).coHom.comp (GameInst.coHom compIfaces sigU)

/-- Components over Core 3.0 into `GInst`. -/
noncomputable def componentToGInst (P : Profile) :
    Inst.CoHom (compSem (core3Sem P)).inst Silmaril.Games.GInst :=
  (compToGame (core3Sem P)).coHom.comp (GameInst.coHom compIfaces sigU)

end Silmaril.Wasm.Institution.CoreComp

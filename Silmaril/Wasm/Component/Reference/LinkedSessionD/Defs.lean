module

public import Silmaril.Wasm.Component.Reference.Sound.Defs
public import Silmaril.Wasm.Abstract.InstSessionD.Defs
public import Silmaril.Wasm.Component.Reference.Link.Defs
public import Silmaril.Wasm.Component.DWiringMulti.Defs

/-!
# The divergence-observing IR semantics of modules with imports: definitions

`Reference.Sound`'s `impSem P : CoreSem ImpModule` interprets a Core 3.0 module with imports by
the strategy of its instance (through `core3Sem P`), and by `trapAll` when it has none. It has
finite plays only, so `Comp.den (impSem P)` (for instance `Linked2.toComp.den (impSem P)`) does
not observe divergence or infinite plays.

This module defines its divergence-observing counterpart, the core semantics of the
divergence-aware component denotation `Comp.denD` (`Silmaril.Wasm.Component.DWiring`):

* `ImpModule.numInst m h`: the numeric Core 3.0 instance of `m` given by the instance chosen in
  `h : ∃ I, m.IsInst I`, with `m`'s imports and exports; `impSem P` interprets `m` by
  `(core3Sem P).sem (m.numInst h)` (`impSem_sem_of`);
* `impSemD P : DCoreSem ImpModule`: `(core3SemD P).sem (m.numInst h)`, the instance **session**
  `threadS (instTripleS I P) I.store` read back through the coercions of `core3Sem`
  (`Silmaril.Wasm.Abstract.InstSessionD`), and the trapping handler when `m` has no instance.

Theorems in `Silmaril.Wasm.Component.Reference.LinkedSessionD.Thms`: `(impSemD P).forget =
impSem P`, hence `(c.denD (impSemD P)).toStrategy = c.den (impSem P)` for every component, and
the consequences for `Linked2`.

For `Linked2`, the two nodes of `l.toComp` (`Linked2.expNode`, `Linked2.impNode`), its exports
(`Linked2.compExports`) and the three sources of divergence of the environment they build
(`Linked2.linkDiv`, from `DObs.ext` of `Silmaril.Wasm.Component.DWiringMulti`) are named, so that
the divergences of `l.toComp.denD C` can be stated by source (`Linked2.div_denD_sources`).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Game
open Silmaril.Wasm.Abstract.InstSession (core3SemD)
open Silmaril.Wasm.Numerics (Profile)

/-- The numeric Core 3.0 instance of a module with imports, from the instance chosen in `h`, with
the module's imports and exports (the instance `impSem` uses). -/
noncomputable def ImpModule.numInst (m : ImpModule) (h : ∃ I, m.IsInst I) : NumInstance where
  inst := h.choose
  imports := m.imports
  exports := m.exports
  imports_eq := h.choose_spec.2.1
  exports_eq := h.choose_spec.2.2

open Classical in
/-- **The divergence-observing Core 3.0 semantics of modules with imports, at profile `P`**: the
session of the module's instance (`core3SemD P`), keeping its divergences and infinite plays; a
module without an instance traps on every question. Its finite plays are `impSem P`
(`forget_impSemD`). -/
noncomputable def impSemD (P : Profile) : DCoreSem ImpModule where
  sem m :=
    if h : ∃ I, m.IsInst I then (core3SemD P).sem (m.numInst h)
    else DStrategy.ofHandler fun _ => .pure none

/-! ## The node of a simple component with imports -/

namespace SimpleI

/-- The core node of `SimpleI.toComp`: the core module, its import `k` the `canon lower` of
component import `k`. -/
def coreNode (c : SimpleI) : Node ImpModule := .core c.mod (lowerArgs c.imports)

/-- The exports of `SimpleI.toComp`: the `canon lift`s of the core exports. -/
def compExports (c : SimpleI) : List Silmaril.Wasm.Component.Export :=
  c.exports.map fun x =>
    { name := x.name, ty := x.ty, impl := ⟨[.lift x.ty], .call (x.core + c.imports.length)⟩ }

end SimpleI

/-! ## The two nodes of a linked component -/

namespace Linked2

/-- The exporter's node of `Linked2.toComp`: the nested exporter, with no imports. -/
def expNode (l : Linked2) : Node ImpModule := .inst (SimpleI.ofSimple l.exp).toComp []

/-- The importer's node of `Linked2.toComp`: the nested importer, its import `k` wired to
environment function `wire[k]` (the exporter's export `wire[k]`). -/
def impNode (l : Linked2) : Node ImpModule :=
  .inst l.imp.toComp (l.wire.map fun w => ⟨[], .call w⟩)

/-- The exports of `Linked2.toComp`: the importer's exports, environment functions
`exp.exports.length + i`. -/
def compExports (l : Linked2) : List Silmaril.Wasm.Component.Export :=
  l.imp.exports.mapIdx fun i x =>
    { name := x.name, ty := x.ty, impl := ⟨[], .call (l.exp.exports.length + i)⟩ }

/-- **The divergences of the linked environment, by source**, under the core semantics `C`: the
environment `dA` is the exporter's node above `maskH 0`; the importer's node `NB` is added on top
of it (`DObs.ext`). A divergence is one of the environment's (the exporter diverging, possibly
inside a call of the importer; `EnvDiv`), one of the importer's node (`NodeDiv`), or chatter
between the two (`NodeChatter`: infinitely many calls of the importer answered by the
exporter, nothing visible). -/
def linkDiv (C : DCoreSem ImpModule) (l : Linked2) : Set (List (Move sigU sigU)) :=
  let dA := (DObs.of (DStrategy.ofHandler (maskH 0))).ext 0 (Node.denD C 0 l.expNode)
  let NB := Node.denD C l.expNode.width l.impNode
  EnvDiv l.expNode.width dA.div NB ∪ NodeDiv l.expNode.width dA.plays NB ∪
    NodeChatter l.expNode.width dA.inf NB

end Linked2

end Silmaril.Wasm.Component.Reference

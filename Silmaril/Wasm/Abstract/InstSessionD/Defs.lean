module

public import Silmaril.Wasm.Abstract.InstSession.Defs
public import Silmaril.Wasm.Component.DWiring.Defs
import Silmaril.Proofs.Wasm.Abstract.InstSessionD.Pull

/-!
# Core 3.0 instance sessions as a divergence-observing core semantics

`Silmaril.Wasm.Abstract.InstSession` reads a numeric Core 3.0 instance as the session
`instSession I P s = threadS (instTripleS I P) s`, a divergence-observing strategy
(`DStrategy`) on the session interface `ssig I.exports`, and builds the ordinary core semantics
`threadSemS` from its finite plays (`core3Sem P = threadSemS …`). This module keeps the
divergences and infinite plays: it builds the **divergence-observing core semantics**
`core3SemD P : DCoreSem NumInstance`, so that `Comp.denUD (core3SemD P)` and
`Comp.denD (core3SemD P)` (`Silmaril.Wasm.Component.DWiring`) are the divergence-aware lift of
the Core 3.0 component denotation `Comp.den (core3Sem P)`.

* `spullD σ`: the session `σ` read back on `ifaceSig ts`, the divergence-observing version of
  `spull`. Its finite plays are `spull σ.toStrategy`; its divergences and infinite plays are the
  preimages along `srelabel` of those of `σ`. This is a **concrete helper** for the injective
  answer relabelling `srelabel`, not a generic API (see below).
* `semOfSD m σ`: the coercions of `core3Sem` around `spullD σ`, by `DStrategy.comp` and
  `DStrategy.ofHandler`, as `semOfS`;
* `threadSemSD T`: the divergence-observing core semantics of the session objects `T m`;
* `core3SemD P`: the one of the instance sessions at the instantiation stores.

The finite plays agree with the existing semantics by definition
(`Silmaril.Wasm.Abstract.InstSessionD.Thms`): `(core3SemD P).forget = core3Sem P`, hence
`(c.denUD (core3SemD P)).toStrategy = c.denU (core3Sem P)`. The divergences and infinite plays
of components are computed by the `DivComp`/`DPair` laws, as collected in
`Silmaril.Wasm.Component.DWiringLaws`.

## A generic relabelling, for the `Games` owners

`spullD` is the instance at `srelabel` of a pull-back of divergence-observing strategies along
an injective move map preserving the legality automaton. The generic signature would be

```
def DStrategy.pull {E F G : Sig} (f : Move E F → Move E G) (pf : Pos E F → Pos E G)
    (hf : ∀ {x o y'}, Step (pf x) (f o) y' → ∃ y, Step x o y ∧ pf y = y')
    (σ : DStrategy E G) : DStrategy E F
```

with plays `Strategy.generate {p | p.map f ∈ σ}`, divergences `{p | p.map f ∈ σ.div}` and
infinite plays `{J | IsInfPlay J ∧ List.map f '' J ∈ σ.inf}`.

## Scope

Not claimed here: adequacy of `Comp.denUD (core3SemD P)` against the reference component
machine for general (n-ary, nested) components, which is the next step; the parser from bytes
to `Comp`; F6.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract.InstSession

open Silmaril.Games
open Silmaril.Wasm.Game Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Proofs.Wasm.Abstract.InstSessionD (mem_spull_of run_unmap)

/-- **A session read back on `ifaceSig ts`, keeping divergence** (a concrete helper for
`srelabel`): the finite plays are `spull σ.toStrategy`; a play diverges, or an infinite play is
played, when its relabelling does in `σ`. -/
def spullD {E : Sig.{0}} {ts : List FnType} (σ : DStrategy E (ssig ts)) :
    DStrategy E (ifaceSig ts) where
  toStrategy := spull σ.toStrategy
  div := {p | p.map srelabel ∈ σ.div}
  inf := {J | IsInfPlay J ∧ List.map srelabel '' J ∈ σ.inf}
  div_mem hp := by exact mem_spull_of (σ.div_mem hp)
  div_run hp := by
    obtain ⟨q, hq⟩ := σ.div_run hp
    exact ⟨q, run_unmap hq⟩
  inf_isInf hJ := hJ.1
  inf_sub hJ _ hp := by exact mem_spull_of (σ.inf_sub hJ.2 ⟨_, hp, rfl⟩)

/-- The divergence-observing strategy of a numeric Core 3.0 instance interpreted by the session
object `σ`, through the coercions of `core3Sem`; see `semOfS`. -/
noncomputable def semOfSD (m : NumInstance) (σ : DStrategy m.inst.E (ssig m.inst.exports)) :
    DStrategy (CoreIface.sig m.imports) (CoreIface.sig m.exports) :=
  (DStrategy.ofHandler (importH m)).comp ((spullD σ).comp (DStrategy.ofHandler (exportH m)))

/-- The divergence-observing core semantics interpreting each instance `m` by the session object
`T m`; see `threadSemS`. -/
noncomputable def threadSemSD
    (T : (m : NumInstance) → DStrategy m.inst.E (ssig m.inst.exports)) :
    DCoreSem NumInstance :=
  ⟨fun m => semOfSD m (T m)⟩

/-- **The divergence-observing Core 3.0 core semantics at profile `P`**: each instance is its
session `threadS (instTripleS m.inst P) m.inst.store` at its instantiation store. -/
noncomputable def core3SemD (P : Profile) : DCoreSem NumInstance :=
  threadSemSD fun m => instSession m.inst P m.inst.store

end Silmaril.Wasm.Abstract.InstSession

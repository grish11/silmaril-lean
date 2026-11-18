module

public import Silmaril.Wasm.Component.InstSem.Defs
import Silmaril.Proofs.Wasm.Component.InstSem.Plays

/-!
# The component IR with an instantiation phase: the start-free case

All proved; proofs in `Silmaril.Proofs.Wasm.Component.InstSem`.

**Comparison with `Comp.denU`.** For a start-free core semantics `C : CoreSem M`, seen through
the adapter `C.toI` (every module ready at once):

* `denIR_toI`: the instantiating denotation is the start-free one with a ready-at-once
  instantiation, `c.denIR C.toI = withReady (c.denU C)`, for every component (nested ones
  included);
* `denI_toI_iff`: after the instantiation `[inst, ready]`, the plays of `c.denI C.toI` are
  exactly the plays of `c.denU C` (lifted to export calls).

So the new denotation restricted to the post-instantiation phase is `Comp.denU`.

**Generic facts.** `mem_withReady_iff` (after `[inst, ready]`, `withReady τ` plays `τ`),
`mem_instGuard_iff` (on plays following the protocol the guard changes nothing),
`denIR_mono` (refining every core module refines every component).
-/

public section

namespace Silmaril.Wasm.Component

open Silmaril.Games Silmaril.Games.Inst
open Silmaril.Wasm.Game (liftMove)

variable {E F : Sig.{0}} {R : Type} {M : Type} [CoreModule M]

/-- **After a ready-at-once instantiation, `withReady τ` plays `τ`.** -/
theorem mem_withReady_iff (τ : Strategy E F) (p : List (Move E F)) :
    askInst :: ansInst .ready :: p.map liftMove ∈ withReady (R := R) τ ↔ p ∈ τ :=
  Silmaril.Proofs.Wasm.Component.InstSem.mem_withReady_iff τ p

/-- **On plays following the instantiation protocol, the guard changes nothing.** -/
theorem mem_instGuard_iff {σ : Strategy E (F.withInst R)} {p : List (Move E (F.withInst R))}
    (hp : InstProper p) : p ∈ instGuard σ ↔ p ∈ σ :=
  Silmaril.Proofs.Wasm.Component.InstSem.mem_instGuard_iff hp

/-- **For start-free core semantics, the instantiating denotation is `Comp.denU` with a
ready-at-once instantiation.** -/
theorem denIR_toI (C : CoreSem M) (c : Comp M) : c.denIR C.toI = withReady (c.denU C) :=
  Silmaril.Proofs.Wasm.Component.InstSem.denIR_toI C c

/-- **The restriction theorem**: for start-free core semantics, the plays of `Comp.denI` after
the instantiation `[inst, ready]` are exactly the plays of `Comp.denU`. -/
theorem denI_toI_iff (C : CoreSem M) (c : Comp M) (p : List (Move sigU sigU)) :
    askInst :: ansInst .ready :: p.map liftMove ∈ c.denI C.toI ↔ p ∈ c.denU C :=
  Silmaril.Proofs.Wasm.Component.InstSem.denI_toI_iff C c p

/-- **Refining every core module refines every component.** -/
theorem denIR_mono {C C' : CoreSemI M} (h : ∀ m, C.sem m ≤ C'.sem m) (c : Comp M) :
    c.denIR C ≤ c.denIR C' :=
  Silmaril.Proofs.Wasm.Component.InstSem.denIR_mono h c

end Silmaril.Wasm.Component

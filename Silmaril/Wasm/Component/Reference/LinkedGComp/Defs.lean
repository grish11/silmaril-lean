module

public import Silmaril.Wasm.Component.Reference.LinkedGLink.Defs
public import Silmaril.Wasm.Component.Reference.LinkedGChatter.Defs
public import Silmaril.Games.DivComp.Defs

/-!
# The canonical object of a link as a composition of sessions: definitions

**Scope.** The session objects of the two sides of a link `LinkedG` (the exporter's
`ExpSpec.session`, the importer's own session `SimpleI.impSession` over its triple
`SimpleI.impTripleS`) and of chains `chainExp e bs Is` (so `LinkedN.spec`), at a profile `P`.

## Sessions of the importers

`SimpleI.impSession P b wire I := threadS (b.impTripleS P wire I) I.store`, a divergence-observing
strategy from the exporter's session interface `sigS` to `sessSig` (the same signature).

## Determinism of an exporter's triple

`ExpSpec.TDet P e` is `ExpSpec.Det P e` on typed questions only (the triple traps every ill-typed
question). `ExpSpec.DivExcl P e`: a typed question that may diverge from a state has no step from
it. `ExpSpec.Det` does not exclude a question that both diverges and returns, and `AFun.Det` of
the exporter's triple is exactly `TDet ∧ DivExcl` (`LinkedGComp.Thms`). `cexExp` is an exporter
meeting `ExpSpec.Det` whose one typed question both traps and diverges.

## Chains

The wiring of a chain built on `e` (`ChainWire e bs Is`): each link `⟨e', b, w⟩` met while
building `chainExp e bs Is` has `LinkedG.WireTy`. It is implied by `ChainOk`, which also asks
for `Good` importers and instances of their core modules.

Three forms of the canonical object of a chain, each following the recursion of `chainExp`
(a missing instance ends the chain, as in `chainExp`):

* `linkChain P T s bs Is`: the session of the **left-nested** iterated link
  `linkS (… (linkS (linkS T u₁) u₂) …) uₙ` from `(((s, I₁.store), I₂.store), …)`, the `uₖ` the
  importers' triples `bₖ.impTripleS P wₖ Iₖ`;
* `impStackT P b w I bs Is`: the importers' triples linked **right-nested**,
  `linkS u₁ (linkS u₂ (… uₙ))`, with its store type and initial store `(I₁.store, (I₂.store, …))`;
* `sessChain P S bs Is` and `impStack P b w I bs Is`: the compositions (`DStrategy.comp`, with
  hiding) of the sessions, left-nested from `S` and right-nested among the importers.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Games.Abstract.SessionLink (linkS)
open Silmaril.Games.Abstract.StratSession (threadS)
open Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Game (ScalarInstance)
open Silmaril.Wasm.Execution.Core (Store)

/-! ## Sessions of importers -/

/-- **The session object of an importer**: the session threading of its own triple from the
store of its core instance. -/
def SimpleI.impSession (P : Profile) (b : SimpleI) (wire : List Nat) (I : ScalarInstance) :
    DStrategy sigS sessSig :=
  threadS (b.impTripleS P wire I) I.store

/-! ## Determinism of an exporter's triple -/

namespace ExpSpec

/-- `ExpSpec.Det` on typed questions. -/
def TDet (P : Profile) (e : ExpSpec) : Prop :=
  ∀ ⦃s s₁ s₂ : e.St⦄ ⦃q : sigU.Op⦄ ⦃a₁ a₂ : Option Payload⦄, e.TypedQ q →
    e.Step P s ⟨q, a₁⟩ s₁ → e.Step P s ⟨q, a₂⟩ s₂ → a₁ = a₂ ∧ s₁ = s₂

/-- **Divergence excludes a step**: a typed question that may diverge from a state has no step
from it. -/
def DivExcl (P : Profile) (e : ExpSpec) : Prop :=
  ∀ ⦃s s' : e.St⦄ ⦃q : sigU.Op⦄ ⦃R : Option Payload⦄, e.TypedQ q → e.DivStep P s q →
    ¬ e.Step P s ⟨q, R⟩ s'

end ExpSpec

/-- **An exporter meeting `ExpSpec.Det` whose triple is not `AFun.Det`**: one export (the default
one, no parameters), one state; every call traps (a unique answer and next state) and may also
diverge. -/
def cexExp : ExpSpec where
  comp := .mk [] [] [default]
  ref := []
  St := PUnit
  init := PUnit.unit
  Step _ _ r _ := r.2 = none
  DivStep _ _ _ := True

/-! ## Chains -/

/-- **The wiring of a chain** built on `e`: every link met while building `chainExp e bs Is` is
well typed. -/
def ChainWire : ExpSpec → List (SimpleI × List Nat) → List ScalarInstance → Prop
  | e, (b, w) :: bs, I :: Is =>
    (LinkedG.mk e b w).WireTy ∧ ChainWire (LinkedG.toExp ⟨e, b, w⟩ I) bs Is
  | _, _, _ => True

/-- **The session of the left-nested iterated link** of `T` (from `s`) and the importers'
triples. -/
def linkChain (P : Profile) {S : Type} (T : ObsTriple (sigN 0) S (Nat × Payload) (Payload ⊕ PUnit))
    (s : S) : List (SimpleI × List Nat) → List ScalarInstance → DStrategy (sigN 0) sessSig
  | (b, w) :: bs, I :: Is => linkChain P (linkS T (b.impTripleS P w I)) (s, I.store) bs Is
  | _, _ => threadS T s

/-- **The importers' triples linked right-nested**, `b` (at `w`, `I`) first: the store type, the
linked triple and its initial store. -/
def impStackT (P : Profile) (b : SimpleI) (w : List Nat) (I : ScalarInstance) :
    List (SimpleI × List Nat) → List ScalarInstance →
      Σ S : Type, ObsTriple sigS S (Nat × Payload) (Payload ⊕ PUnit) × S
  | (b', w') :: bs, I' :: Is =>
    ⟨Store Nat × (impStackT P b' w' I' bs Is).1,
      linkS (b.impTripleS P w I) (impStackT P b' w' I' bs Is).2.1,
      (I.store, (impStackT P b' w' I' bs Is).2.2)⟩
  | _, _ => ⟨Store Nat, b.impTripleS P w I, I.store⟩

/-- **The left-nested composition of sessions** of `S` and the importers' sessions. -/
def sessChain (P : Profile) (S : DStrategy (sigN 0) sessSig) :
    List (SimpleI × List Nat) → List ScalarInstance → DStrategy (sigN 0) sessSig
  | (b, w) :: bs, I :: Is => sessChain P (S.comp (b.impSession P w I)) bs Is
  | _, _ => S

/-- **The right-nested composition of the importers' sessions**, `b` (at `w`, `I`) first. -/
def impStack (P : Profile) (b : SimpleI) (w : List Nat) (I : ScalarInstance) :
    List (SimpleI × List Nat) → List ScalarInstance → DStrategy sigS sessSig
  | (b', w') :: bs, I' :: Is => (b.impSession P w I).comp (impStack P b' w' I' bs Is)
  | _, _ => b.impSession P w I

end Silmaril.Wasm.Component.Reference

module

public import Silmaril.Wasm.Component.Reference.LinkedGDivIR.Defs

/-!
# The read-back of chatter for an abstract exporter, at deterministic profiles: definitions

**Scope.** The exporter interface `ExpSpec` of `LinkedG`, at a profile `P` (for the theorems, the
deterministic profiles `profile o`). `LinkedGDivIR` states the IR divergence law of
`LinkedG.toExp` conditionally on the read-back of chatter (`LinkedG.Task.ChatterReadBack`). That
read-back needs two more facts about the exporter, defined here.

## Determinism of an exporter

`ExpSpec.Det P e`: from a state, a call (a question at `sigU`) has at most one answer and at
most one next state. Then a session is determined by its questions (the `Linked2` facts
`expRunT_functional` and `round_det`, over the interface).

## Infinite plays are served along one run

`ExpSpec.AdeqIC P e` is the converse of `ExpSpec.AdeqI`: complete rounds of typed calls, a finite
list `L₀` and then chunks `T 0, T 1, …`, all of whose finite prefixes are plays of the IR
`e.comp.denU (impSem P)`, are served along **one** run of the exporter's steps from its initial
state: `L₀` up to `S 0`, then each chunk `T k` from `S k` to `S (k + 1)`. The chunks may be
empty, so the rounds may be finitely many. Without determinism every finite prefix is served
along *some* run (`ExpSpec.Adeq.bwd`), but the runs need not extend one another.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Games Silmaril.Wasm.Component
open Silmaril.Games.Abstract (streamTake)
open Silmaril.Wasm.Numerics (Profile)

/-- **A deterministic exporter** at `P`: from a state, a call has at most one answer and at
most one next state. -/
def ExpSpec.Det (P : Profile) (e : ExpSpec) : Prop :=
  ∀ ⦃s s₁ s₂ : e.St⦄ ⦃q : sigU.Op⦄ ⦃a₁ a₂ : Option Payload⦄,
    e.Step P s ⟨q, a₁⟩ s₁ → e.Step P s ⟨q, a₂⟩ s₂ → a₁ = a₂ ∧ s₁ = s₂

/-- **Infinite plays are served along one run** (the converse of `ExpSpec.AdeqI`): typed complete
rounds `L₀`, then the chunks `T 0, T 1, …`, all of whose finite prefixes are plays of the IR,
are served along one run of the exporter's steps from its initial state. -/
def ExpSpec.AdeqIC (P : Profile) (e : ExpSpec) : Prop :=
  ∀ (L₀ : List URound) (T : ℕ → List URound), (∀ r ∈ L₀, e.Typed r) →
    (∀ k, ∀ r ∈ T k, e.Typed r) →
    (∀ n, uMoves (L₀ ++ (streamTake T n).flatten) ∈ e.comp.denU (impSem P)) →
    ∃ S : ℕ → e.St, e.Run P e.init L₀ (S 0) ∧ ∀ k, e.Run P (S k) (T k) (S (k + 1))

end Silmaril.Wasm.Component.Reference

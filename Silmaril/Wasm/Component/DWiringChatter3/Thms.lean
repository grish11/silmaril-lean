module

public import Silmaril.Wasm.Component.DWiringChatter3.Defs
public import Silmaril.Wasm.Component.DWiringChatter2.Thms
import Silmaril.Proofs.Wasm.Component.DWiringChatter3.Cases

/-!
# Infinite plays of `ext`, routed

`Silmaril.Wasm.Component.DWiringLaws.Thms` gives the infinite plays of
`ext e D N = D.comp (extTop e N)` as visible limits of infinite interactions
(`inf_ext`), and those of `extTop e N` as infinite plays of copycat beside `N`
seen through `splitH e` (`inf_extTop`, with `ThroughAbove`). This module states
them without chains and without `ThroughAbove`, in terms of `D`'s runs and of
plays of `N` interleaved by `splitRoute e`.

* **A composite without chains** (`inf_comp_eq`): an infinite play of
  `σ.comp τ` is an infinite trace `J` with runs `I` of `σ` and `K` of `τ`
  (`IsRun`: an infinite play, or the prefixes of a finite play when the
  component stops) that are `Interleaved` with visible trace `J`.
* **The node above, routed** (`mem_extTop_iff`, `inf_extTop_iff`,
  `isRun_extTop_iff`): a play of `extTop e N` is a legal play whose routing
  `c.map (splitRoute e)` is a play of copycat beside `N`; an infinite play is an
  infinite trace of such plays whose routed trace, on `N`'s half, is an
  infinite play of `N` whenever it is infinite. `splitH e` forwards every outer
  question at once, so the routed trace *is* the pairing's infinite play.
* Hence **`inf_ext_routed`**.

**The cases.** In `inf_ext_routed`, `I` is infinite or `D` stops, and `C` is
infinite or the node above stops; with `C` infinite, its routed trace has an
infinite copycat half, an infinite `N` half, or both
(`Split.isInfPlay_infL_or_infR`).

* `D` and the node above do not both stop (`not_both_stop`).
* The node above stops: `D` moves forever at its lower interface
  (`inf_of_top_stop`).
* Copycat's half is infinite: `D` moves forever (`inf_of_copycat_inf`); `D`'s
  imports are passed outward forever.
* `N`'s half is infinite: it is an infinite play of `N` (part of the statement).
* Both are infinite: both of the above.
* `D` stops while the outer interface moves forever
  (`copycat_bounded_of_stop`): this is possible only through `N`. Copycat's half
  is bounded, since copycat passes each outer move on to `D`, and `N`'s half is
  infinite: `N` answers the outer questions routed to it without calling `D`.

Proofs are in `Silmaril.Proofs.Wasm.Component.DWiringChatter3`.
-/

public section

namespace Silmaril.Wasm.Component

open Silmaril.Games

universe u v w

/-- **Infinite plays of a composite, without chains**: an infinite trace,
interleaving a run of each component. -/
theorem inf_comp_eq {E F G : Sig.{u}} (σ : DStrategy E F) (τ : DStrategy F G) :
    (σ.comp τ).inf = {J | IsInfPlay J ∧ ∃ I K, IsRun σ I ∧ IsRun τ K ∧ Interleaved I K J} :=
  Silmaril.Proofs.Wasm.Component.DWiringChatter3.inf_comp_eq σ τ

/-- **Not both sides stop**: two traces that stop do not interleave to an
infinite one. -/
theorem not_both_stop {α : Type u} {β : Type v} {γ : Type w} {I : Set (List (α ⊕ β))}
    {K : Set (List (β ⊕ γ))} {J : Set (List (α ⊕ γ))} (hJ : IsInfPlay J)
    (h : Interleaved I K J) (s₀ : List (α ⊕ β)) (c₀ : List (β ⊕ γ)) :
    ¬ (I = prefixes s₀ ∧ K = prefixes c₀) :=
  Silmaril.Proofs.Wasm.Component.DWiringChatter3.not_both_stop hJ h s₀ c₀

namespace DStrategy

variable {X : Sig.{0}} {e : Nat} {N : DStrategy sigU sigU}

/-- **Plays of `extTop e N`, routed**: legal plays whose routing is a play of
copycat beside `N`. -/
theorem mem_extTop_iff {c : List (Move sigU sigU)} :
    c ∈ (extTop e N).toStrategy ↔
      Legal c ∧ c.map (splitRoute e) ∈ (Strategy.id sigU).pair N.toStrategy :=
  Silmaril.Proofs.Wasm.Component.DWiringChatter3.mem_extTop_iff

/-- **Infinite plays of `extTop e N`, routed.** -/
theorem inf_extTop_iff {C : Set (List (Move sigU sigU))} :
    C ∈ (extTop e N).inf ↔ IsInfPlay C ∧
      (∀ c ∈ C, Legal c ∧ c.map (splitRoute e) ∈ (Strategy.id sigU).pair N.toStrategy) ∧
      (IsInfPlay (Split.infR (List.map (splitRoute e) '' C)) →
        Split.infR (List.map (splitRoute e) '' C) ∈ N.inf) :=
  Silmaril.Proofs.Wasm.Component.DWiringChatter3.inf_extTop_iff

/-- **Runs of `extTop e N`, routed.** -/
theorem isRun_extTop_iff {C : Set (List (Move sigU sigU))} :
    IsRun (extTop e N) C ↔ (IsInfPlay C ∨ ∃ c₀, C = prefixes c₀) ∧
      (∀ c ∈ C, Legal c ∧ c.map (splitRoute e) ∈ (Strategy.id sigU).pair N.toStrategy) ∧
      (IsInfPlay (Split.infR (List.map (splitRoute e) '' C)) →
        Split.infR (List.map (splitRoute e) '' C) ∈ N.inf) :=
  Silmaril.Proofs.Wasm.Component.DWiringChatter3.isRun_extTop_iff

/-- **Infinite plays of `ext`, routed.** An infinite trace `J` interleaving a
run `I` of `D` (an infinite play, or a finite play where `D` stops) with a
trace `C` above `D` (infinite, or stopping) of legal plays whose routing
through `splitH e` is a play of copycat beside `N`; `N`'s half of the routed
trace, when infinite, is an infinite play of `N`. No `ThroughAbove`. -/
theorem inf_ext_routed (e : Nat) (D : DStrategy X sigU) (N : DStrategy sigU sigU) :
    (ext e D N).inf = {J | IsInfPlay J ∧ ∃ I C,
      (I ∈ D.inf ∨ ∃ s₀ ∈ D.toStrategy, I = prefixes s₀) ∧
      (IsInfPlay C ∨ ∃ c₀, C = prefixes c₀) ∧
      (∀ c ∈ C, Legal c ∧ c.map (splitRoute e) ∈ (Strategy.id sigU).pair N.toStrategy) ∧
      (IsInfPlay (Split.infR (List.map (splitRoute e) '' C)) →
        Split.infR (List.map (splitRoute e) '' C) ∈ N.inf) ∧
      Interleaved I C J} :=
  Silmaril.Proofs.Wasm.Component.DWiringChatter3.inf_ext_routed e D N

/-! ## The cases -/

/-- **If `D` stops, the outer moves go to `N`**: the trace above is infinite,
copycat's half of its routing is bounded and `N`'s half is infinite. -/
theorem copycat_bounded_of_stop {s₀ : List (Move X sigU)}
    {C : Set (List (Move sigU sigU))} {J : Set (List (Move X sigU))}
    (hC : IsInfPlay C ∨ ∃ c₀, C = prefixes c₀)
    (hmem : ∀ c ∈ C, Legal c ∧ c.map (splitRoute e) ∈ (Strategy.id sigU).pair N.toStrategy)
    (hJ : IsInfPlay J) (h : Interleaved (prefixes s₀) C J) :
    IsInfPlay C ∧ ¬ IsInfPlay (Split.infL (List.map (splitRoute e) '' C)) ∧
      IsInfPlay (Split.infR (List.map (splitRoute e) '' C)) :=
  Silmaril.Proofs.Wasm.Component.DWiringChatter3.copycat_bounded_of_stop hC hmem hJ h

/-- **If copycat's half is infinite, `D` moves forever.** -/
theorem inf_of_copycat_inf {D : DStrategy X sigU} {I : Set (List (Move X sigU))}
    {C : Set (List (Move sigU sigU))} {J : Set (List (Move X sigU))}
    (hI : I ∈ D.inf ∨ ∃ s₀ ∈ D.toStrategy, I = prefixes s₀)
    (hC : IsInfPlay C ∨ ∃ c₀, C = prefixes c₀)
    (hmem : ∀ c ∈ C, Legal c ∧ c.map (splitRoute e) ∈ (Strategy.id sigU).pair N.toStrategy)
    (hJ : IsInfPlay J) (h : Interleaved I C J)
    (hL : IsInfPlay (Split.infL (List.map (splitRoute e) '' C))) : I ∈ D.inf :=
  Silmaril.Proofs.Wasm.Component.DWiringChatter3.inf_of_copycat_inf hI hC hmem hJ h hL

/-- **If the node above stops, `D` moves forever.** -/
theorem inf_of_top_stop {D : DStrategy X sigU} {I : Set (List (Move X sigU))}
    {c₀ : List (Move sigU sigU)} {J : Set (List (Move X sigU))}
    (hI : I ∈ D.inf ∨ ∃ s₀ ∈ D.toStrategy, I = prefixes s₀) (hJ : IsInfPlay J)
    (h : Interleaved I (prefixes c₀) J) : I ∈ D.inf :=
  Silmaril.Proofs.Wasm.Component.DWiringChatter3.inf_of_top_stop hI hJ h

end DStrategy

end Silmaril.Wasm.Component

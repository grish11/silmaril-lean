module

public import Silmaril.Games.Abstract.SessionHostCex.Defs
public import Silmaril.Games.Abstract.SessionHost.Thms
import Silmaril.Proofs.Games.Abstract.SessionHostCex.Bound

/-!
# Sessions with host imports: a counterexample

The hypothesis of `SessionHost.pair_comp_threadS`,

  `((hostDOn F R).pair (DStrategy.id F)).comp (threadS t s₀) = threadS (hostLinkS R t) s₀`
  for `StoreDet (hostLinkS R t)`,

is needed, and `StoreDet t` cannot replace it.

**The bound is a hidden host answer** (`threadS_inf_not_subset_pair_comp`): the component's first
round asks the host for a bound `n` on its later rounds. The component is deterministic given
answers (`det_boundHostComp`), hence store-deterministic (`storeDet_boundHostComp`), but the
linked triple is not (`not_storeDet_hostLinkS`): the host call is hidden. The linked session
plays `unitRounds`, infinitely many rounds (`unitRounds_mem_hostLinkS`); no interaction of the
host beside copycat with the session of the component does (`unitRounds_not_mem_comp`):
`threadS_inf_subset_pair_comp` fails without its hypothesis, and the composite is not the linked
session (`pair_comp_ne_threadS`).

**`StoreDet t` is not enough** (`not_pair_comp_threadS_of_storeDet`): the equality fails for some
store-deterministic component. The host gives any answer, so the hypothesis of
`storeDet_hostLinkS` and `pair_comp_threadS_of_det` that it has at most one answer per call is
also needed (`not_functional_pickHost`).

Proofs are in `Silmaril.Proofs.Games.Abstract.SessionHostCex`.
-/

public section

namespace Silmaril.Games.Abstract.SessionHostCex

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
  Silmaril.Games.Abstract.StratThread Silmaril.Games.Abstract.StratSession
  Silmaril.Games.Abstract.SessionHost

variable {F : Sig.{0}}

/-- The bounding component is deterministic given answers. -/
theorem det_boundHostComp : AFun.Det (boundHostComp (F := F)).1 :=
  Silmaril.Proofs.Games.Abstract.SessionHostCex.det_boundHostComp

/-- The bounding component is store-deterministic: its host call shows the bound. -/
theorem storeDet_boundHostComp : StoreDet (boundHostComp (F := F)) :=
  storeDet_of_det det_boundHostComp

/-- The host has more than one answer per call. -/
theorem not_functional_pickHost :
    ¬ ∀ m n n', pickHost m (.answer n) → pickHost m (.answer n') → n = n' :=
  fun h => Nat.zero_ne_one (h () (0 : ℕ) (1 : ℕ) ⟨(0 : ℕ), rfl⟩ ⟨(1 : ℕ), rfl⟩)

/-- The linked triple is not store-deterministic: the bound is a hidden host answer. -/
theorem not_storeDet_hostLinkS : ¬ StoreDet (hostLinkS pickHost (boundHostComp (F := F))) :=
  Silmaril.Proofs.Games.Abstract.SessionHostCex.not_storeDet_hostLinkS

/-- The linked session plays infinitely many rounds. -/
theorem unitRounds_mem_hostLinkS :
    unitRounds ∈ (threadS (hostLinkS pickHost (boundHostComp (F := F))) none).inf :=
  Silmaril.Proofs.Games.Abstract.SessionHostCex.unitRounds_mem_hostLinkS

/-- No interaction of the host beside copycat with the session of the bounding component plays
infinitely many rounds. -/
theorem unitRounds_not_mem_comp :
    unitRounds ∉ (((hostDOn F pickHost).pair (DStrategy.id F)).comp
      (threadS (boundHostComp (F := F)) none)).inf :=
  Silmaril.Proofs.Games.Abstract.SessionHostCex.unitRounds_not_mem_comp

/-- **`StoreDet (hostLinkS R t)` is needed**: the linked infinite plays are not infinite plays of
the composite. -/
theorem threadS_inf_not_subset_pair_comp :
    ¬ (threadS (hostLinkS pickHost (boundHostComp (F := F))) none).inf ⊆
      (((hostDOn F pickHost).pair (DStrategy.id F)).comp
        (threadS (boundHostComp (F := F)) none)).inf :=
  fun h => unitRounds_not_mem_comp (h unitRounds_mem_hostLinkS)

/-- The composite is not the linked session. -/
theorem pair_comp_ne_threadS :
    ((hostDOn F pickHost).pair (DStrategy.id F)).comp (threadS (boundHostComp (F := F)) none) ≠
      threadS (hostLinkS pickHost (boundHostComp (F := F))) none :=
  fun h => unitRounds_not_mem_comp (h ▸ unitRounds_mem_hostLinkS)

/-- **`StoreDet t` cannot replace `StoreDet (hostLinkS R t)`**: linking host imports of a
store-deterministic component need not be composition with hiding. -/
theorem not_pair_comp_threadS_of_storeDet :
    ¬ ∀ t : ObsTriple (pickSig ⊕ₛ F) (Option ℕ) Unit (Unit ⊕ Unit), StoreDet t → ∀ s₀,
      ((hostDOn F pickHost).pair (DStrategy.id F)).comp (threadS t s₀) =
        threadS (hostLinkS pickHost t) s₀ :=
  fun h => pair_comp_ne_threadS (h _ storeDet_boundHostComp none)

end Silmaril.Games.Abstract.SessionHostCex

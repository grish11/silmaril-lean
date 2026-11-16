module

public import Silmaril.Games.Abstract.SessionLinkDead.Defs
public import Silmaril.Games.Abstract.SessionLink.Thms
import Silmaril.Proofs.Games.Abstract.SessionLinkDead.Thread
import Silmaril.Proofs.Games.Abstract.SessionLinkDead.Some

/-!
# Linking servers with plain traps: theorems

**The dead server has the server's session** (`threadS_deadS`): for every store-retaining triple
`t`, `threadS (deadS t) (some s₀) = threadS t s₀`. A plain trap of `t` ends the session of `t`:
the next question is accepted and never answered, with no divergence and no infinite play. In
`deadS t` it is a continuing trap to the dead server `none`, which accepts the next question and
never answers. `deadS t` has no plain trap (`noPlainTrap_deadS`), and keeps store determinism
(`storeDet_deadS`) and determinism given answers (`det_deadS`).

**Linking is composition with hiding, plain server traps included** (`comp_threadSD`): for a
store-deterministic server and a store-deterministic `linkSD t u`, with no hypothesis on plain
traps,

  `(threadS t s₀).comp (threadS u s₀') = threadS (linkSD t u) (some s₀, s₀')`.

This is `SessionLink.comp_threadS` for `deadS t`, transported along `threadS_deadS`; so are its
parts: the finite plays agree with no hypothesis at all (`comp_threadSD_toStrategy`), and for
components deterministic given answers the equality holds outright (`comp_threadSD_of_det`).

**Without plain traps** `linkSD t u` is `linkS t u` along `(s, s') ↦ (some s, s')`
(`linkSD_some`), and their sessions agree (`threadS_linkSD_of_noPlainTrap`).

Proofs are in `Silmaril.Proofs.Games.Abstract.SessionLinkDead`.
-/

public section

namespace Silmaril.Games.Abstract.SessionLinkDead

open Silmaril.Games Silmaril.Games.Abstract.StratObs Silmaril.Games.Abstract.StratThread
  Silmaril.Games.Abstract.StratSession Silmaril.Games.Abstract.SessionLink

universe u

variable {E : Sig.{u}} {S S' A B A' B' : Type u} {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})}
  {u : ObsTriple (sig1 A B) S' A' (B' ⊕ PUnit.{u + 1})}

/-! ## The dead server -/

/-- **The dead server has the server's session.** -/
theorem threadS_deadS (s₀ : S) : threadS (deadS t) (some s₀) = threadS t s₀ :=
  Silmaril.Proofs.Games.Abstract.SessionLinkDead.threadS_deadS s₀

/-- The dead server has no plain trap. -/
theorem noPlainTrap_deadS : NoPlainTrap (deadS t) :=
  Silmaril.Proofs.Games.Abstract.SessionLinkDead.noPlainTrap_deadS

/-- A store-deterministic server gives a store-deterministic dead server. -/
theorem storeDet_deadS (ht : StoreDet t) : StoreDet (deadS t) :=
  Silmaril.Proofs.Games.Abstract.SessionLinkDead.storeDet_deadS ht

/-- A server deterministic given answers gives a dead server deterministic given answers. -/
theorem det_deadS (ht : AFun.Det t.1) : AFun.Det (deadS t).1 :=
  Silmaril.Proofs.Games.Abstract.SessionLinkDead.det_deadS ht

/-! ## Linking with a server that may die -/

/-- **The finite plays of linked sessions, plain server traps included**: no hypothesis. -/
theorem comp_threadSD_toStrategy (s₀ : S) (s₀' : S') :
    ((threadS t s₀).comp (threadS u s₀')).toStrategy =
      (threadS (linkSD t u) (some s₀, s₀')).toStrategy := by
  rw [← threadS_deadS (t := t) s₀]; exact comp_threadS_toStrategy noPlainTrap_deadS _ _

/-- **Linked divergences are divergences of the composite.** -/
theorem div_linkSD_subset (s₀ : S) (s₀' : S') :
    (threadS (linkSD t u) (some s₀, s₀')).div ⊆ ((threadS t s₀).comp (threadS u s₀')).div := by
  rw [← threadS_deadS (t := t) s₀]; exact div_linkS_subset _ _

/-- **Linked infinite plays are infinite plays of the composite**, for a store-deterministic
linked triple. -/
theorem inf_linkSD_subset (hL : StoreDet (linkSD t u)) (s₀ : S) (s₀' : S') :
    (threadS (linkSD t u) (some s₀, s₀')).inf ⊆ ((threadS t s₀).comp (threadS u s₀')).inf := by
  rw [← threadS_deadS (t := t) s₀]; exact inf_linkS_subset hL _ _

/-- **Divergences of the composite are linked divergences**, for a store-deterministic server. -/
theorem div_comp_subset_dead (htd : StoreDet t) (s₀ : S) (s₀' : S') :
    ((threadS t s₀).comp (threadS u s₀')).div ⊆ (threadS (linkSD t u) (some s₀, s₀')).div := by
  rw [← threadS_deadS (t := t) s₀]; exact div_comp_subset noPlainTrap_deadS (storeDet_deadS htd) _ _

/-- **Infinite plays of the composite are linked infinite plays**, for a store-deterministic
server. -/
theorem inf_comp_subset_dead (htd : StoreDet t) (s₀ : S) (s₀' : S') :
    ((threadS t s₀).comp (threadS u s₀')).inf ⊆ (threadS (linkSD t u) (some s₀, s₀')).inf := by
  rw [← threadS_deadS (t := t) s₀]; exact inf_comp_subset noPlainTrap_deadS (storeDet_deadS htd) _ _

/-- **Linking is composition with hiding, plain server traps included.** -/
theorem comp_threadSD (htd : StoreDet t) (hL : StoreDet (linkSD t u)) (s₀ : S) (s₀' : S') :
    (threadS t s₀).comp (threadS u s₀') = threadS (linkSD t u) (some s₀, s₀') := by
  rw [← threadS_deadS (t := t) s₀]; exact comp_threadS noPlainTrap_deadS (storeDet_deadS htd) hL _ _

/-- **Linking deterministic components is composition with hiding**, plain server traps
included. -/
theorem comp_threadSD_of_det (ht : AFun.Det t.1) (hu : AFun.Det u.1) (s₀ : S) (s₀' : S') :
    (threadS t s₀).comp (threadS u s₀') = threadS (linkSD t u) (some s₀, s₀') := by
  rw [← threadS_deadS (t := t) s₀]
  exact comp_threadS_of_det noPlainTrap_deadS (det_deadS ht) hu _ _

/-! ## Without plain traps -/

/-- **Without plain traps, `linkSD` is `linkS`** along the embedding `(s, s') ↦ (some s, s')`: the
same finished behaviours with the final stores embedded, the same pending calls and the same
productive streams. -/
theorem linkSD_some (hnt : NoPlainTrap t) (s : S) (s' : S') :
    (∀ a', (linkSD t u).1 (some s, s') a' =
      (fun x => (x.1, someEnd x.2)) '' (linkS t u).1 (s, s') a') ∧
    (linkSD t u).2.1 (some s, s') = (linkS t u).2.1 (s, s') ∧
    (linkSD t u).2.2 (some s, s') = (linkS t u).2.2 (s, s') :=
  ⟨Silmaril.Proofs.Games.Abstract.SessionLinkDead.linkSD_some_fst hnt s s',
    Silmaril.Proofs.Games.Abstract.SessionLinkDead.linkSD_some_pend hnt s s',
    Silmaril.Proofs.Games.Abstract.SessionLinkDead.linkSD_some_inf hnt s s'⟩

/-- **Without plain traps, the sessions of `linkSD` and `linkS` agree.** -/
theorem threadS_linkSD_of_noPlainTrap (hnt : NoPlainTrap t) (s₀ : S) (s₀' : S') :
    threadS (linkSD t u) (some s₀, s₀') = threadS (linkS t u) (s₀, s₀') :=
  Silmaril.Proofs.Games.Abstract.SessionLinkDead.threadS_linkSD hnt s₀ s₀'

end Silmaril.Games.Abstract.SessionLinkDead

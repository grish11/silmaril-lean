module

public import Silmaril.Games.Abstract.SessionLinkCex.Defs
public import Silmaril.Games.Abstract.StratSession.Defs

/-!
# Linking counterexamples: linking does not preserve `AFun.Det`

The client may return at once, or call the server, which diverges. Both components are
deterministic given answers; the linked triple returns, and diverges, with the empty log.
-/

public section

namespace Silmaril.Proofs.Games.Abstract.SessionLinkCex

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
open Silmaril.Games.Abstract.StratThread Silmaril.Games.Abstract.StratSession
open Silmaril.Games.Abstract.SessionLink Silmaril.Games.Abstract.SessionLinkCex

variable {E : Sig.{0}}

theorem det_divServer : AFun.Det (divServer (E := E)).1 := by
  rintro _ _ x y hx hy
  simp only [divServer, Set.mem_singleton_iff] at hx hy
  subst hx hy
  rfl

theorem det_mayClient : AFun.Det mayClient.1 := by
  rintro _ _ x y hx hy
  simp only [mayClient, Set.mem_singleton_iff] at hx hy
  subst hx hy
  rfl

theorem noPlainTrap_divServer : NoPlainTrap (divServer (E := E)) := by
  intro _ _ _ h
  simp [divServer] at h

theorem noPlainTrap_mayClient : NoPlainTrap mayClient := by
  intro _ _ _ h
  simp [mayClient] at h

theorem ret_mem_linkS_may :
    (([] : List (Call E)), End.ret (Sum.inl ()) ((), ())) ∈
      (linkS (divServer (E := E)) mayClient).1 ((), ()) () :=
  .inl ⟨[], (), _, .nil _, rfl, rfl⟩

theorem div_mem_linkS_may :
    (([] : List (Call E)), (End.div : End (Unit × Unit) (Unit ⊕ Unit))) ∈
      (linkS (divServer (E := E)) mayClient).1 ((), ()) () :=
  .inr (.inl ⟨[], (), (), [], .nil _, .inl rfl, rfl, rfl⟩)

theorem not_det_linkS_may : ¬ AFun.Det (linkS (divServer (E := E)) mayClient).1 := by
  intro h
  have := h _ _ _ _ ret_mem_linkS_may div_mem_linkS_may
  simp [AFun.Agree] at this

end Silmaril.Proofs.Games.Abstract.SessionLinkCex

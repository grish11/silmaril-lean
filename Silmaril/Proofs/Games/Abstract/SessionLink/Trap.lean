module

public import Silmaril.Games.Abstract.SessionLink.Defs

/-!
# Linking sessions: plain traps

The plain traps of the linked triple are plain traps of the client: a server divergence and
hidden chatter end in `div`, and a client end is kept by `linkEnd` (`noPlainTrap_linkS`).
-/

public section

namespace Silmaril.Proofs.Games.Abstract.SessionLink

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.SessionLink
open Silmaril.Games.Abstract.StratSession

universe u

variable {E : Sig.{u}} {S S' A B A' B' : Type u}

theorem noPlainTrap_linkS {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})}
    {u : ObsTriple (sig1 A B) S' A' (B' ⊕ PUnit.{u + 1})} (hu : NoPlainTrap u) :
    NoPlainTrap (linkS t u) := by
  rintro σ a' c (⟨rs, s₁, e, -, he, hx⟩ | ⟨_, _, _, _, _, _, _, hx⟩ | ⟨_, _, _, _, _, _, _, hx⟩)
  · cases e with
    | trap => exact hu _ _ _ he
    | ret => simp [linkEnd] at hx
    | div => simp [linkEnd] at hx
  · simp at hx
  · simp at hx

end Silmaril.Proofs.Games.Abstract.SessionLink

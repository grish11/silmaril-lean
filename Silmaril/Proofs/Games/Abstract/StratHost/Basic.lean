module

public import Silmaril.Games.Abstract.StratHost.Defs

/-!
# Restricting an open play object by a relational host (proofs)
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.StratHost

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratLegal
  Silmaril.Games.Abstract.StratHost

universe u

variable {E : Sig.{u}} {S A B : Type u}

theorem consistent_lift (R : HostRel E) (c : List (Call (legalSig E R.legal))) :
    R.Consistent (c.map liftCall) := by
  intro x hx
  obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
  exact y.2.2

theorem consistent_iff (R : HostRel E) (cs : List (Call E)) :
    R.Consistent cs ↔ ∃ c : List (Call (legalSig E R.legal)), c.map liftCall = cs := by
  refine ⟨fun h => ?_, fun ⟨c, hc⟩ => hc ▸ consistent_lift R c⟩
  induction cs with
  | nil => exact ⟨[], rfl⟩
  | cons x cs ih =>
    obtain ⟨c, hc⟩ := ih fun y hy => h y (.tail _ hy)
    exact ⟨⟨x.1, x.2, h x (.head _)⟩ :: c, by simp [liftCall, hc]⟩

theorem restrict_hostRestrict (R : HostRel E) (t : ObsTriple E S A B) :
    restrict R.legal (hostRestrict R t) =
      ((restrict R.legal t).1, fun s a => {x | x ∈ (restrict R.legal t).2.1 s a ∧ R.Stalls x.2},
        (restrict R.legal t).2.2) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> funext s a <;> ext x
  · exact ⟨fun h => h.1, fun h => ⟨h, consistent_lift R x.1⟩⟩
  · exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, consistent_lift R x.1, h.2⟩⟩
  · exact ⟨fun h => h.1, fun h => ⟨h, fun n => (x n).2.2⟩⟩

end Silmaril.Proofs.Games.Abstract.StratHost

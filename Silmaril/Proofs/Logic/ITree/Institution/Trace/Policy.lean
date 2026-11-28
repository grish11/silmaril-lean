module

public import Silmaril.Logic.ITree.Institution.Trace.Policy.Defs

@[expose] public section

namespace Silmaril.Proofs.Logic.ITree.TraceInstitution

open Silmaril.Elgot.ITree

universe u v w
variable {E : Type u → Type u} {X : Type w} {A : Type v}

theorem replay_mono {p q : Handler X E} (admits : p ≤ q) (trace : Trace E A) (x : X) :
    Replay p x trace → Replay q x trace := by
  induction trace generalizing x with
  | exchange event reply tail ih =>
    rintro ⟨y, step, replay⟩
    exact ⟨y, admits ⟨_, event⟩ x reply y step, ih y replay⟩
  | «prefix» | request | result => exact id

end Silmaril.Proofs.Logic.ITree.TraceInstitution

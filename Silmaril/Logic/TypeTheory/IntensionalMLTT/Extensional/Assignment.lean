module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.Extensional.Assignment.Defs
import Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.ExtensionalAssignment

public section

namespace Silmaril.Logic.TypeTheory.IntensionalMLTT.Extensional

open Silmaril.Logic.TypeTheory.ExtensionalMLTT

/-- Extend an actual typed assignment by a fresh name at an actually formed type. -/
theorem assignment_cons {n i : ℕ} {Γ : Context n} {Δ : ECtx} {σ : Fin n → ETm 0}
    {A : Term n} {x : String} (e : TypedAssignment Γ Δ σ)
    (hΔ : ECtx.JEqH ∅ Δ .unit .star .star) (hx : x ∉ Δ.dv)
    (hA : ECtx.JEqH ∅ Δ (.univ i) (term σ A) (term σ A)) :
    TypedAssignment (Γ.snoc A) (Δ.cons x (term σ A)) (Fin.cons (.fv x) σ) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.ExtensionalAssignment.assignment_cons e hΔ hx hA

/-- Every declared target name comes from the given source-telescope naming. -/
theorem context_names {n : ℕ} (Γ : Context n) (ι : Fin n → String) (x : String)
    (hx : x ∈ (context Γ ι).dv) : ∃ i, ι i = x :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.ExtensionalAssignment.context_names Γ ι x hx


end Silmaril.Logic.TypeTheory.IntensionalMLTT.Extensional

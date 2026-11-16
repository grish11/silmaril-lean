module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.Extensional.Assignment.Defs
public import Silmaril.Logic.TypeTheory.IntensionalMLTT.Extensional.Syntax.Thms
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.NamedSubstitution.Thms

public section

namespace Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.ExtensionalAssignment

open Silmaril.Logic.TypeTheory.IntensionalMLTT
open Silmaril.Logic.TypeTheory.IntensionalMLTT.Extensional
open Silmaril.Logic.TypeTheory.ExtensionalMLTT

theorem assignment_cons {n i : ℕ} {Γ : Context n} {Δ : ECtx} {σ : Fin n → ETm 0}
    {A : Term n} {x : String} (e : TypedAssignment Γ Δ σ)
    (hΔ : ECtx.JEqH ∅ Δ .unit .star .star) (hx : x ∉ Δ.dv)
    (hA : ECtx.JEqH ∅ Δ (.univ i) (term σ A) (term σ A)) :
    TypedAssignment (Γ.snoc A) (Δ.cons x (term σ A)) (Fin.cons (.fv x) σ) := by
  have hctx : ECtx.JEqH ∅ (Δ.cons x (term σ A)) .unit .star .star := .cons_ok hΔ hx hA
  intro y B hy
  cases hy with
  | here =>
    simpa only [Term.weaken, term_rename, Function.comp_def, Fin.cons_succ, Fin.cons_zero] using
      ECtx.JEqH.var hctx (ECtx.Lookup.here _ _ _)
  | there hy =>
    simpa only [Term.weaken, term_rename, Function.comp_def, Fin.cons_succ] using
      (e hy).weaken hctx (ECtx.Embeds.fresh hx (term σ A))

theorem context_names {n : ℕ} (Γ : Context n) : ∀ (ι : Fin n → String) (x : String),
    x ∈ (context Γ ι).dv → ∃ i, ι i = x := by
  induction Γ with
  | nil => intro ι x hx; simp only [context, ECtx.dv, Finset.notMem_empty] at hx
  | snoc Γ A ih =>
    intro ι x hx
    have hs : x = ι 0 ∨ x ∈ (context Γ (fun i => ι i.succ)).dv := by
      simpa only [context, ECtx.dv, Finset.mem_insert] using hx
    rcases hs with hs | hs
    · exact ⟨0, hs.symm⟩
    · obtain ⟨i, hi⟩ := ih (fun i => ι i.succ) x hs
      exact ⟨i.succ, hi⟩

end Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.ExtensionalAssignment

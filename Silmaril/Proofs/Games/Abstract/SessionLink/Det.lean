module

public import Silmaril.Proofs.Games.Abstract.SessionLink.Plays
import Mathlib.Data.List.Basic

/-!
# Linking sessions: determinism (proofs)

`storeDet_linkS`: if the server and the client are deterministic given answers
(`AFun.Det` of their finished behaviours), the linked triple is store-deterministic. Two linked
returns with the same log and the same result are served by the same rounds: the client's calls
agree as long as their answers agree (`AFun.Det u.1`), and each served call is answered by the
same server round, since two server rounds whose logs are prefixes of the same log agree
(`AFun.Det t.1`, `agree_of_append`).
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.SessionLink

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
  Silmaril.Games.Abstract.StratThread Silmaril.Games.Abstract.StratSession
  Silmaril.Games.Abstract.SessionLink

universe u

variable {E : Sig.{u}} {S S' A B A' B' : Type u}

/-- Two agreeing behaviours whose logs extend to the same list have the same log and end. -/
theorem agree_of_append {S₁ B₁ : Type u} {c c' L L' : List (Call E)} {e e' : End S₁ B₁}
    (h : AFun.Agree c e c' e') (hL : c ++ L = c' ++ L') : c = c' ∧ e = e' := by
  induction c generalizing c' with
  | nil =>
    cases c' with
    | nil => exact ⟨rfl, h⟩
    | cons x c' => obtain ⟨m, n⟩ := x; exact h.elim
  | cons x c ih =>
    cases c' with
    | nil => obtain ⟨m, n⟩ := x; exact h.elim
    | cons x' c' =>
      simp only [List.cons_append, List.cons.injEq] at hL
      obtain ⟨rfl, hL⟩ := hL
      obtain ⟨m, n⟩ := x
      obtain ⟨hc, he⟩ := ih (h.2 HEq.rfl) hL
      exact ⟨by rw [hc], he⟩

variable {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})}
  {u : ObsTriple (sig1 A B) S' A' (B' ⊕ PUnit.{u + 1})}

/-- Served rounds with the same log, serving agreeing client behaviours, are equal. -/
theorem served_eq (ht : AFun.Det t.1) {s s₁ s₁' : S}
    {rs rs' : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))}
    (h : Rounds t s rs s₁) (h' : Rounds t s rs' s₁') (hlog : servedLog rs = servedLog rs')
    {e e' : End S' (B' ⊕ PUnit.{u + 1})} (hu : AFun.Agree (served rs) e (served rs') e') :
    rs = rs' ∧ s₁ = s₁' ∧ e = e' := by
  induction h generalizing rs' with
  | nil =>
    cases h' with
    | nil => exact ⟨rfl, rfl, hu⟩
    | cons => exact hu.elim
  | @cons s s₂ _ a c x rs hr _ ih =>
    cases h' with
    | nil => exact hu.elim
    | @cons _ s₂' _ a' c' x' rs' hr' h' =>
      obtain ⟨rfl, hu⟩ := hu
      simp only [servedLog_cons] at hlog
      obtain ⟨rfl, he⟩ := agree_of_append (ht _ _ _ _ hr hr') hlog
      simp only [End.ret.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      obtain ⟨rfl, rfl, rfl⟩ := ih h' (List.append_cancel_left hlog) (hu HEq.rfl)
      exact ⟨rfl, rfl, rfl⟩

/-- **Deterministic components give a store-deterministic linked triple.** -/
theorem storeDet_linkS (ht : AFun.Det t.1) (hu : AFun.Det u.1) : StoreDet (linkS t u) := by
  intro σ a' c y σ₁ σ₂ h₁ h₂
  rcases h₁ with ⟨rs, s₁, e, hR, hb, he⟩ | ⟨_, _, _, _, _, _, _, he⟩ | ⟨_, _, _, _, _, _, _, he⟩
  · rcases h₂ with ⟨rs', s₁', e', hR', hb', he'⟩ | ⟨_, _, _, _, _, _, _, he'⟩ |
        ⟨_, _, _, _, _, _, _, he'⟩
    · obtain ⟨rfl, he⟩ := Prod.ext_iff.1 he
      obtain ⟨hc, he'⟩ := Prod.ext_iff.1 he'
      obtain ⟨rfl, rfl⟩ := linkEnd_eq_ret he.symm
      obtain ⟨rfl, rfl⟩ := linkEnd_eq_ret he'.symm
      obtain ⟨-, h, he⟩ := served_eq ht hR hR' hc (hu _ _ _ _ hb hb')
      simp only [End.ret.injEq] at he
      exact Prod.ext h he.2
    · cases (Prod.ext_iff.1 he').2
    · cases (Prod.ext_iff.1 he').2
  · cases (Prod.ext_iff.1 he).2
  · cases (Prod.ext_iff.1 he).2

end Silmaril.Proofs.Games.Abstract.SessionLink

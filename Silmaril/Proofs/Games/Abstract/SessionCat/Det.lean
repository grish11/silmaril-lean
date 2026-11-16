module

public import Silmaril.Games.Abstract.SessionCat.Defs
public import Silmaril.Games.Abstract.SessionLink.Thms

/-!
# Session-level category laws: determinism of returns (proofs)

`retDet_linkS`: linking preserves `RetDet`. Two linked returns are served by server rounds whose
logs agree as long as the answers on `E` agree (`RetDet t`); when a served round agrees in full,
it gives the client the same answer and the same server store, so the client continues alike
(`RetDet u`). `agree_append` glues the agreement of one round to that of the rest.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.SessionCat

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
  Silmaril.Games.Abstract.StratThread Silmaril.Games.Abstract.StratSession
  Silmaril.Games.Abstract.SessionLink Silmaril.Games.Abstract.SessionCat

universe u

variable {E : Sig.{u}}

/-- Agreement of the first parts, and of the rest when the first parts end alike, give agreement
of the concatenations. -/
theorem agree_append {S₀ B₀ S₁ B₁ : Type u} {c c' L L' : List (Call E)} {e₀ e₀' : End S₀ B₀}
    {e e' : End S₁ B₁} (h : AFun.Agree c e₀ c' e₀') (hk : e₀ = e₀' → AFun.Agree L e L' e') :
    AFun.Agree (c ++ L) e (c' ++ L') e' := by
  induction c generalizing c' with
  | nil =>
    cases c' with
    | nil => exact hk h
    | cons x c' => obtain ⟨m, n⟩ := x; exact h.elim
  | cons x c ih =>
    cases c' with
    | nil => obtain ⟨m, n⟩ := x; exact h.elim
    | cons x' c' =>
      obtain ⟨m, n⟩ := x
      obtain ⟨m', n'⟩ := x'
      exact ⟨h.1, fun hn => ih (h.2 hn)⟩

/-- Agreement with the same log is equality of the ends. -/
theorem eq_of_agree {S₀ B₀ : Type u} {c : List (Call E)} {e e' : End S₀ B₀}
    (h : AFun.Agree c e c e') : e = e' := by
  induction c with
  | nil => exact h
  | cons x c ih => obtain ⟨m, n⟩ := x; exact ih (h.2 HEq.rfl)

/-- `RetDet` gives store determinism. -/
theorem storeDet_of_retDet {S A B : Type u} {t : ObsTriple E S A B} (ht : RetDet t) :
    StoreDet t := fun _ _ _ _ _ _ h₁ h₂ => by
  have := eq_of_agree (ht _ _ _ _ _ _ _ _ h₁ h₂)
  simp only [End.ret.injEq] at this
  exact this.2

variable {S S' A B A' B' : Type u} {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})}
  {u : ObsTriple (sig1 A B) S' A' (B' ⊕ PUnit.{u + 1})}

/-- Served rounds from the same store, serving agreeing client behaviours, have agreeing logs and
linked ends. -/
theorem agree_served (ht : RetDet t) {s s₁ s₁' : S}
    {rs rs' : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))}
    (h : Rounds t s rs s₁) (h' : Rounds t s rs' s₁') {e e' : End S' (B' ⊕ PUnit.{u + 1})}
    (hu : AFun.Agree (served rs) e (served rs') e') :
    AFun.Agree (servedLog rs) (linkEnd s₁ e) (servedLog rs') (linkEnd s₁' e') := by
  induction h generalizing rs' with
  | nil =>
    cases h' with
    | nil => cases hu; simp only [servedLog, List.flatMap_nil, AFun.Agree]
    | cons => exact hu.elim
  | @cons s s₂ _ a c x rs hr _ ih =>
    cases h' with
    | nil => exact hu.elim
    | @cons _ s₂' _ a' c' x' rs' hr' h' =>
      obtain ⟨rfl, hu⟩ := hu
      simp only [servedLog, List.flatMap_cons]
      refine agree_append (ht _ _ _ _ _ _ _ _ hr hr') fun he => ?_
      simp only [End.ret.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ih h' (hu HEq.rfl)

theorem linkEnd_eq_ret {s : S} {e : End S' (B' ⊕ PUnit.{u + 1})} {y : B' ⊕ PUnit.{u + 1}}
    {σ : S × S'} (h : linkEnd s e = End.ret y σ) : e = End.ret y σ.2 ∧ σ.1 = s := by
  cases e with
  | ret y' s' => simp only [linkEnd, End.ret.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
  | trap => cases h
  | div => cases h

/-- **Linking preserves `RetDet`.** -/
theorem retDet_linkS (ht : RetDet t) (hu : RetDet u) : RetDet (linkS t u) := by
  intro σ a' c c' y y' σ₁ σ₁' h₁ h₂
  rcases h₁ with ⟨rs, s₁, e, hR, hb, he⟩ | ⟨_, _, _, _, _, _, _, he⟩ | ⟨_, _, _, _, _, _, _, he⟩
  · rcases h₂ with ⟨rs', s₁', e', hR', hb', he'⟩ | ⟨_, _, _, _, _, _, _, he'⟩ |
        ⟨_, _, _, _, _, _, _, he'⟩
    · obtain ⟨rfl, he⟩ := Prod.ext_iff.1 he
      obtain ⟨rfl, he'⟩ := Prod.ext_iff.1 he'
      obtain ⟨rfl, h1⟩ := linkEnd_eq_ret he.symm
      obtain ⟨rfl, h1'⟩ := linkEnd_eq_ret he'.symm
      have := agree_served ht hR hR' (hu _ _ _ _ _ _ _ _ hb hb')
      simpa [linkEnd, ← h1, ← h1'] using this
    · cases (Prod.ext_iff.1 he').2
    · cases (Prod.ext_iff.1 he').2
  · cases (Prod.ext_iff.1 he).2
  · cases (Prod.ext_iff.1 he).2

end Silmaril.Proofs.Games.Abstract.SessionCat

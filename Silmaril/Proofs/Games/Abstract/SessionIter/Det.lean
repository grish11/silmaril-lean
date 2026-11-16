module

public import Silmaril.Games.Abstract.SessionIter.Defs
public import Silmaril.Games.Abstract.SessionCat.Thms
public import Silmaril.Games.Abstract.FunctionIter.Defs

/-!
# Session iteration: returns, plain traps and determinism (proofs)

The finished behaviours of `iterS t` are `AFun.iter` of the body with its ends reassociated.
Its returns are exactly the `IterRet` chains (`mem_iterS_ret`). Plain traps and returns are
tracked by induction on `AFun.IterBeh`. Determinism given answers is preserved by `AFun.iter`
(`det_iter`): an infinite silent chain (`spin`) of a deterministic body leaves no other
behaviour (`eq_div_of_spin`).
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.SessionIter

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
  Silmaril.Games.Abstract.StratOps Silmaril.Games.Abstract.StratSession
  Silmaril.Games.Abstract.SessionCat Silmaril.Games.Abstract.SessionIter

universe u

variable {E : Sig.{u}}

/-! ## Agreement -/

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

/-- Agreement transported along ends that are equal when the original ends are. -/
theorem agree_of_agree {S₀ B₀ S₁ B₁ : Type u} {c c' : List (Call E)} {e₀ e₀' : End S₀ B₀}
    {e e' : End S₁ B₁} (h : AFun.Agree c e₀ c' e₀') (hk : e₀ = e₀' → e = e') :
    AFun.Agree c e c' e' := by
  simpa using agree_append (L := []) (L' := []) h hk

/-! ## Behaviours of a reassociated body -/

variable {S A B C : Type u}

theorem mem_mapT_fst {t : ObsTriple E S A B} {h : B → C} {s : S} {a : A} {x : CallBeh E S C} :
    x ∈ (mapT t h).1 s a ↔ ∃ e, (x.1, e) ∈ t.1 s a ∧ x.2 = FullFun.endMap h e := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy, rfl⟩
  · rintro ⟨e, he, hx⟩
    exact ⟨_, he, Prod.ext rfl hx.symm⟩

theorem iterS_fst (t : ObsTriple E S A ((B ⊕ A) ⊕ PUnit.{u + 1})) :
    (iterS t).1 = AFun.iter (mapT t iterAssoc).1 := rfl

theorem endMap_eq_ret {h : B → C} {e : End S B} {y : C} {s : S}
    (he : FullFun.endMap h e = End.ret y s) : ∃ b, e = End.ret b s ∧ h b = y := by
  cases e with
  | ret b s' =>
    simp only [FullFun.endMap, End.ret.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨b, rfl, rfl⟩
  | trap => cases he
  | div => cases he

theorem endMap_eq_trap {h : B → C} {e : End S B} (he : FullFun.endMap h e = End.trap) :
    e = End.trap := by
  cases e <;> first | rfl | cases he

/-- **Returns of a session iteration** are `IterRet` chains. -/
theorem mem_iterS_ret {t : ObsTriple E S A ((B ⊕ A) ⊕ PUnit.{u + 1})} {s s' : S} {a : A}
    {c : List (Call E)} {x : B ⊕ PUnit.{u + 1}} :
    (c, End.ret x s') ∈ (iterS t).1 s a ↔ IterRet t s a c x s' := by
  constructor
  · intro h
    rw [iterS_fst] at h
    suffices ∀ s a y, AFun.IterBeh (mapT t iterAssoc).1 s a y →
        ∀ c x s', y = (c, End.ret x s') → IterRet t s a c x s' from this _ _ _ h _ _ _ rfl
    intro s a y hy
    induction hy with
    | exit hb =>
      rintro c x s' hy
      simp only [Prod.mk.injEq, End.ret.injEq] at hy
      obtain ⟨rfl, rfl, rfl⟩ := hy
      obtain ⟨e, he, hx⟩ := mem_mapT_fst.1 hb
      obtain ⟨y, rfl, hy⟩ := endMap_eq_ret hx.symm
      rcases y with (b | a') | ⟨⟩
      · cases hy; exact .exit he
      · cases hy
      · cases hy; exact .trap he
    | trap => rintro c x s' hy; cases hy
    | div => rintro c x s' hy; cases hy
    | step hb _ ih =>
      rintro c x s' hy
      simp only [Prod.mk.injEq] at hy
      obtain ⟨rfl, rfl⟩ := hy
      obtain ⟨e, he, hx⟩ := mem_mapT_fst.1 hb
      obtain ⟨y, rfl, hy⟩ := endMap_eq_ret hx.symm
      rcases y with (b | a') | ⟨⟩
      · cases hy
      · cases hy; exact .step he (ih _ _ _ rfl)
      · cases hy
    | spin => rintro c x s' hy; cases hy
  · intro h
    rw [iterS_fst]
    induction h with
    | exit he => exact .exit (mem_mapT_fst.2 ⟨_, he, rfl⟩)
    | trap he => exact .exit (mem_mapT_fst.2 ⟨_, he, rfl⟩)
    | step he _ ih => exact AFun.IterBeh.step (mem_mapT_fst.2 ⟨_, he, rfl⟩) ih

/-! ## Plain traps -/

theorem noPlainTrap_iterS {t : ObsTriple E S A ((B ⊕ A) ⊕ PUnit.{u + 1})} (ht : NoPlainTrap t) :
    NoPlainTrap (iterS t) := by
  intro s a c h
  rw [iterS_fst] at h
  suffices ∀ s a y, AFun.IterBeh (mapT t iterAssoc).1 s a y → y.2 ≠ End.trap from this _ _ _ h rfl
  intro s a y hy
  induction hy with
  | exit => exact fun h => by cases h
  | trap hb =>
    intro _
    obtain ⟨e, he, hx⟩ := mem_mapT_fst.1 hb
    exact ht _ _ _ (endMap_eq_trap hx.symm ▸ he)
  | div => exact fun h => by cases h
  | step _ _ ih => exact ih
  | spin => exact fun h => by cases h

theorem noPlainTrap_seqS {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})}
    {u : ObsTriple E S B (C ⊕ PUnit.{u + 1})} (ht : NoPlainTrap t) (hu : NoPlainTrap u) :
    NoPlainTrap (seqS t u) := by
  intro s a c h
  rcases SessionCat.mem_seqS.1 h with ⟨c', h', hx⟩ | ⟨c', _, hx⟩ | ⟨c', s₁, _, hx⟩ |
    ⟨c₁, b, s₁, c₂, e, _, he, hx⟩
  · cases hx; exact ht _ _ _ h'
  · cases hx
  · cases hx
  · simp only [Prod.mk.injEq] at hx
    obtain ⟨-, rfl⟩ := hx
    exact hu _ _ _ he

/-! ## Deterministic returns -/

theorem retDet_iterS {t : ObsTriple E S A ((B ⊕ A) ⊕ PUnit.{u + 1})} (ht : RetDet t) :
    RetDet (iterS t) := by
  intro s a c c' x x' s₁ s₁' h h'
  rw [mem_iterS_ret] at h h'
  induction h generalizing c' x' s₁' with
  | exit he =>
    cases h' with
    | exit he' => exact agree_of_agree (ht _ _ _ _ _ _ _ _ he he') fun h => by cases h; rfl
    | trap he' => exact agree_of_agree (ht _ _ _ _ _ _ _ _ he he') fun h => by cases h
    | step he' _ =>
      simpa using agree_append (L := []) (ht _ _ _ _ _ _ _ _ he he') fun h => by cases h
  | trap he =>
    cases h' with
    | exit he' => exact agree_of_agree (ht _ _ _ _ _ _ _ _ he he') fun h => by cases h
    | trap he' => exact agree_of_agree (ht _ _ _ _ _ _ _ _ he he') fun h => by cases h; rfl
    | step he' _ =>
      simpa using agree_append (L := []) (ht _ _ _ _ _ _ _ _ he he') fun h => by cases h
  | step he _ ih =>
    cases h' with
    | exit he' =>
      simpa using agree_append (L' := []) (ht _ _ _ _ _ _ _ _ he he') fun h => by cases h
    | trap he' =>
      simpa using agree_append (L' := []) (ht _ _ _ _ _ _ _ _ he he') fun h => by cases h
    | step he' h₂' =>
      exact agree_append (ht _ _ _ _ _ _ _ _ he he') fun h => by
        simp only [End.ret.injEq, Sum.inl.injEq, Sum.inr.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ih _ _ _ h₂'

/-- **Returns of a session sequence** are `SeqRet` rounds. -/
theorem mem_seqS_ret {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})}
    {u : ObsTriple E S B (C ⊕ PUnit.{u + 1})} {s s' : S} {a : A} {c : List (Call E)}
    {x : C ⊕ PUnit.{u + 1}} :
    (c, End.ret x s') ∈ (seqS t u).1 s a ↔ SeqRet t u s a c x s' := by
  rw [SessionCat.mem_seqS]
  constructor
  · rintro (⟨_, _, hx⟩ | ⟨_, _, hx⟩ | ⟨c₀, s₀, h₀, hx⟩ | ⟨c₁, b, s₁, c₂, e, h₁, he, hx⟩)
    · cases hx
    · cases hx
    · cases hx; exact .inl ⟨rfl, h₀⟩
    · simp only [Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact .inr ⟨c₁, b, s₁, c₂, h₁, he, rfl⟩
  · rintro (⟨rfl, h₀⟩ | ⟨c₁, b, s₁, c₂, h₁, he, rfl⟩)
    · exact .inr (.inr (.inl ⟨c, s', h₀, rfl⟩))
    · exact .inr (.inr (.inr ⟨c₁, b, s₁, c₂, _, h₁, he, rfl⟩))

theorem retDet_seqS {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})}
    {u : ObsTriple E S B (C ⊕ PUnit.{u + 1})} (ht : RetDet t) (hu : RetDet u) :
    RetDet (seqS t u) := by
  intro s a c c' x x' s₁ s₁' h h'
  rw [mem_seqS_ret] at h h'
  rcases h with ⟨rfl, h₀⟩ | ⟨c₁, b, s₂, c₂, h₁, he, rfl⟩ <;>
  rcases h' with ⟨rfl, h₀'⟩ | ⟨c₁', b', s₂', c₂', h₁', he', rfl⟩
  · exact agree_of_agree (ht _ _ _ _ _ _ _ _ h₀ h₀') fun h => by cases h; rfl
  · simpa using agree_append (L := []) (ht _ _ _ _ _ _ _ _ h₀ h₁') fun h => by cases h
  · simpa using agree_append (L' := []) (ht _ _ _ _ _ _ _ _ h₁ h₀') fun h => by cases h
  · exact agree_append (ht _ _ _ _ _ _ _ _ h₁ h₁') fun h => by
      simp only [End.ret.injEq, Sum.inl.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hu _ _ _ _ _ _ _ _ he he'

/-! ## Determinism given answers -/

theorem agree_nil_right {S₀ B₀ : Type u} {c : List (Call E)} {e e' : End S₀ B₀}
    (h : AFun.Agree c e [] e') : c = [] ∧ e = e' := by
  cases c with
  | nil => exact ⟨rfl, h⟩
  | cons x c => obtain ⟨m, n⟩ := x; exact h.elim

theorem det_mapT {t : ObsTriple E S A B} (ht : AFun.Det t.1) (h : B → C) :
    AFun.Det (mapT t h).1 := by
  intro s a x y hx hy
  obtain ⟨x₀, hx₀, rfl⟩ := hx
  obtain ⟨y₀, hy₀, rfl⟩ := hy
  exact agree_of_agree (ht _ _ _ _ hx₀ hy₀) fun h => by dsimp only; rw [h]

section Iter

variable {f : AFun E S A (B ⊕ A)}

/-- **A silent infinite chain of a deterministic body is its only behaviour.** -/
theorem eq_div_of_spin (hf : AFun.Det f) (σ : Nat → S × A)
    (hσ : ∀ n, ([], .ret (.inr (σ (n + 1)).2) (σ (n + 1)).1) ∈ f (σ n).1 (σ n).2) :
    ∀ s a y, AFun.IterBeh f s a y → ∀ n, (s, a) = σ n → y = ([], .div) := by
  intro s a y hy
  induction hy with
  | exit hb =>
    intro n hn
    have hσn := hσ n
    rw [← hn] at hσn
    obtain ⟨-, h⟩ := agree_nil_right (hf _ _ _ _ hb hσn)
    cases h
  | trap hb =>
    intro n hn
    have hσn := hσ n
    rw [← hn] at hσn
    obtain ⟨-, h⟩ := agree_nil_right (hf _ _ _ _ hb hσn)
    cases h
  | div hb =>
    intro n hn
    have hσn := hσ n
    rw [← hn] at hσn
    obtain ⟨-, h⟩ := agree_nil_right (hf _ _ _ _ hb hσn)
    cases h
  | step hb _ ih =>
    intro n hn
    have hσn := hσ n
    rw [← hn] at hσn
    obtain ⟨rfl, h⟩ := agree_nil_right (hf _ _ _ _ hb hσn)
    simp only [End.ret.injEq, Sum.inr.injEq] at h
    obtain ⟨h₁, h₂⟩ := h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (ih (n + 1) (Prod.ext h₂ h₁))
    rfl
  | spin => intros; rfl

/-- **Iteration preserves determinism given answers.** -/
theorem det_iter (hf : AFun.Det f) : AFun.Det (AFun.iter f) := by
  intro s a x y hx hy
  induction hx generalizing y with
  | exit hb =>
    cases hy with
    | exit hb' => exact agree_of_agree (hf _ _ _ _ hb hb') fun h => by cases h; rfl
    | trap hb' => exact agree_of_agree (hf _ _ _ _ hb hb') fun h => by cases h
    | div hb' => exact agree_of_agree (hf _ _ _ _ hb hb') fun h => by cases h
    | step hb' _ =>
      simpa using agree_append (L := []) (hf _ _ _ _ hb hb') fun h => by cases h
    | spin σ h0 hσ =>
      have hσ0 := hσ 0
      rw [h0] at hσ0
      obtain ⟨-, h⟩ := agree_nil_right (hf _ _ _ _ hb hσ0)
      cases h
  | trap hb =>
    cases hy with
    | exit hb' => exact agree_of_agree (hf _ _ _ _ hb hb') fun h => by cases h
    | trap hb' => exact agree_of_agree (hf _ _ _ _ hb hb') fun _ => rfl
    | div hb' => exact agree_of_agree (hf _ _ _ _ hb hb') fun h => by cases h
    | step hb' _ =>
      simpa using agree_append (L := []) (hf _ _ _ _ hb hb') fun h => by cases h
    | spin σ h0 hσ =>
      have hσ0 := hσ 0
      rw [h0] at hσ0
      obtain ⟨-, h⟩ := agree_nil_right (hf _ _ _ _ hb hσ0)
      cases h
  | div hb =>
    cases hy with
    | exit hb' => exact agree_of_agree (hf _ _ _ _ hb hb') fun h => by cases h
    | trap hb' => exact agree_of_agree (hf _ _ _ _ hb hb') fun h => by cases h
    | div hb' => exact agree_of_agree (hf _ _ _ _ hb hb') fun _ => rfl
    | step hb' _ =>
      simpa using agree_append (L := []) (hf _ _ _ _ hb hb') fun h => by cases h
    | spin σ h0 hσ =>
      have hσ0 := hσ 0
      rw [h0] at hσ0
      obtain ⟨-, h⟩ := agree_nil_right (hf _ _ _ _ hb hσ0)
      cases h
  | step hb hrest ih =>
    cases hy with
    | exit hb' =>
      simpa using agree_append (L' := []) (hf _ _ _ _ hb hb') fun h => by cases h
    | trap hb' =>
      simpa using agree_append (L' := []) (hf _ _ _ _ hb hb') fun h => by cases h
    | div hb' =>
      simpa using agree_append (L' := []) (hf _ _ _ _ hb hb') fun h => by cases h
    | step hb' hrest' =>
      exact agree_append (hf _ _ _ _ hb hb') fun h => by
        simp only [End.ret.injEq, Sum.inr.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ih _ hrest'
    | spin σ h0 hσ =>
      have hσ0 := hσ 0
      rw [h0] at hσ0
      obtain ⟨rfl, h⟩ := agree_nil_right (hf _ _ _ _ hb hσ0)
      simp only [End.ret.injEq, Sum.inr.injEq] at h
      obtain ⟨h₁, h₂⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (eq_div_of_spin hf σ hσ _ _ _ hrest 1 (Prod.ext h₂ h₁))
      rfl
  | spin σ h0 hσ =>
    rw [eq_div_of_spin hf σ hσ _ _ _ hy 0 h0.symm]
    rfl

end Iter

theorem det_iterS {t : ObsTriple E S A ((B ⊕ A) ⊕ PUnit.{u + 1})} (ht : AFun.Det t.1) :
    AFun.Det (iterS t).1 :=
  det_iter (det_mapT ht _)

end Silmaril.Proofs.Games.Abstract.SessionIter

module

public import Silmaril.Games.Abstract.SessionIter2.Defs
public import Silmaril.Games.Abstract.SessionCat.Thms
public import Silmaril.Games.Abstract.FunctionIter.Defs

/-!
# Store strength commutes with iteration (proofs)

A framed body leaves the second store component untouched, so its iteration does too: the
finished behaviours (`AFun.IterBeh`), continuing chains (`FullFun.ContChain`) and infinite
continuing chains of `frameS S' t` from `(s, s')` are those of `t` from `s` with `s'` attached.
In the converse direction a framed chain is projected on its first store component.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.SessionIter2

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
  Silmaril.Games.Abstract.StratOps Silmaril.Games.Abstract.SessionCat

universe u

variable {E : Sig.{u}} {S S' A B : Type u}

theorem frameEnd_eq_ret {s' : S'} {e : End S B} {b : B} {σ : S × S'}
    (h : frameEnd s' e = End.ret b σ) : e = End.ret b σ.1 ∧ σ.2 = s' := by
  cases e with
  | ret b₀ s₀ =>
    simp only [frameEnd, End.ret.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | trap => cases h
  | div => cases h

theorem frameEnd_eq_trap {s' : S'} {e : End S B} (h : frameEnd s' e = End.trap) : e = End.trap := by
  cases e <;> first | rfl | cases h

theorem frameEnd_eq_div {s' : S'} {e : End S B} (h : frameEnd s' e = End.div) : e = End.div := by
  cases e <;> first | rfl | cases h

variable {t : ObsTriple E S A B}

/-- A return of a framed triple is a return of the triple, the second store component kept. -/
theorem mem_frameS_ret {σ σ' : S × S'} {a : A} {c : List (Call E)} {b : B} :
    (c, End.ret b σ') ∈ (frameS S' t).1 σ a ↔ (c, End.ret b σ'.1) ∈ t.1 σ.1 a ∧ σ'.2 = σ.2 := by
  constructor
  · rintro ⟨y, hy, hx⟩
    obtain ⟨rfl, hx⟩ := Prod.ext_iff.1 hx
    obtain ⟨he, h2⟩ := frameEnd_eq_ret hx
    exact ⟨he ▸ hy, h2⟩
  · rintro ⟨h, h2⟩
    refine ⟨_, h, ?_⟩
    obtain ⟨σ₁, σ₂⟩ := σ'
    simp only at h2
    simp [frameEnd, h2]

theorem mem_frameS_trap {σ : S × S'} {a : A} {c : List (Call E)} :
    (c, End.trap) ∈ (frameS S' t).1 σ a ↔ (c, End.trap) ∈ t.1 σ.1 a := by
  constructor
  · rintro ⟨y, hy, hx⟩
    obtain ⟨rfl, hx⟩ := Prod.ext_iff.1 hx
    exact frameEnd_eq_trap hx ▸ hy
  · exact fun h => ⟨_, h, rfl⟩

theorem mem_frameS_div {σ : S × S'} {a : A} {c : List (Call E)} :
    (c, End.div) ∈ (frameS S' t).1 σ a ↔ (c, End.div) ∈ t.1 σ.1 a := by
  constructor
  · rintro ⟨y, hy, hx⟩
    obtain ⟨rfl, hx⟩ := Prod.ext_iff.1 hx
    exact frameEnd_eq_div hx ▸ hy
  · exact fun h => ⟨_, h, rfl⟩

variable {t : ObsTriple E S A (B ⊕ A)}

theorem contChain_frameS {σ σ' : S × S'} {a a' : A} {c : List (Call E)} :
    FullFun.ContChain (frameS S' t).1 σ a c σ' a' ↔
      FullFun.ContChain t.1 σ.1 a c σ'.1 a' ∧ σ'.2 = σ.2 := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨.refl, rfl⟩
    | step h₁ _ ih =>
      obtain ⟨h₁, e₁⟩ := mem_frameS_ret.1 h₁
      exact ⟨.step h₁ ih.1, ih.2.trans e₁⟩
  · rintro ⟨h, h2⟩
    obtain ⟨σ₁, σ₂⟩ := σ
    obtain ⟨σ₁', σ₂'⟩ := σ'
    simp only at h h2
    subst h2
    induction h with
    | refl => exact .refl
    | step h₁ _ ih => exact .step (mem_frameS_ret (σ' := (_, _)).2 ⟨h₁, rfl⟩) ih

theorem iterBeh_frameS {s : S} {s' : S'} {a : A} {x : CallBeh E S B} (h : AFun.IterBeh t.1 s a x) :
    AFun.IterBeh (frameS S' t).1 (s, s') a (x.1, frameEnd s' x.2) := by
  induction h with
  | exit h => exact .exit (mem_frameS_ret.2 ⟨h, rfl⟩)
  | trap h => exact .trap (mem_frameS_trap.2 h)
  | div h => exact .div (mem_frameS_div.2 h)
  | step h₁ _ ih =>
    dsimp only at ih ⊢
    exact .step (mem_frameS_ret (σ' := (_, s')).2 ⟨h₁, rfl⟩) ih
  | spin σ h0 hσ =>
    refine .spin (fun n => (((σ n).1, s'), (σ n).2)) (by simp [h0]) fun n => ?_
    exact mem_frameS_ret.2 ⟨hσ n, rfl⟩

theorem iterBeh_of_frameS {σ : S × S'} {a : A} {x : CallBeh E (S × S') B}
    (h : AFun.IterBeh (frameS S' t).1 σ a x) :
    ∃ y, AFun.IterBeh t.1 σ.1 a y ∧ (y.1, frameEnd σ.2 y.2) = x := by
  induction h with
  | @exit σ a c b σ' h =>
    obtain ⟨h, h2⟩ := mem_frameS_ret.1 h
    refine ⟨_, .exit h, ?_⟩
    obtain ⟨σ₁, σ₂⟩ := σ'
    simp only at h2
    simp [frameEnd, h2]
  | trap h => exact ⟨_, .trap (mem_frameS_trap.1 h), rfl⟩
  | div h => exact ⟨_, .div (mem_frameS_div.1 h), rfl⟩
  | step h₁ _ ih =>
    obtain ⟨h₁, h2⟩ := mem_frameS_ret.1 h₁
    obtain ⟨y, hy, hyx⟩ := ih
    obtain ⟨h₃, h₄⟩ := Prod.ext_iff.1 hyx
    rw [h2] at h₄
    exact ⟨(_ ++ y.1, y.2), .step h₁ hy, Prod.ext (by simpa using h₃) h₄⟩
  | spin ρ h0 hρ =>
    refine ⟨_, .spin (fun n => ((ρ n).1.1, (ρ n).2)) (by simp [h0]) fun n =>
      (mem_frameS_ret.1 (hρ n)).1, rfl⟩

theorem frameS_iterT (t : ObsTriple E S A (B ⊕ A)) :
    frameS S' (iterT t) = iterT (frameS S' t) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> funext σ a <;> ext x
  · constructor
    · rintro ⟨y, hy, rfl⟩
      exact iterBeh_frameS (s := σ.1) (s' := σ.2) hy
    · intro hx
      obtain ⟨y, hy, rfl⟩ := iterBeh_of_frameS hx
      exact ⟨y, hy, rfl⟩
  · constructor
    · rintro ⟨c, s₁, a₁, c', m, hc, hm, rfl⟩
      exact ⟨c, (s₁, σ.2), a₁, c', m, contChain_frameS.2 ⟨hc, rfl⟩, hm, rfl⟩
    · rintro ⟨c, σ₁, a₁, c', m, hc, hm, rfl⟩
      exact ⟨c, σ₁.1, a₁, c', m, (contChain_frameS.1 hc).1, hm, rfl⟩
  · constructor
    · rintro (⟨c, s₁, a₁, ω', hc, hω, rfl⟩ | ⟨ρ, l, h0, hρ, hl⟩)
      · exact .inl ⟨c, (s₁, σ.2), a₁, ω', contChain_frameS.2 ⟨hc, rfl⟩, hω, rfl⟩
      · refine .inr ⟨fun n => (((ρ n).1, σ.2), (ρ n).2), l, by simp [h0], fun n => ?_, hl⟩
        exact mem_frameS_ret.2 ⟨hρ n, rfl⟩
    · rintro (⟨c, σ₁, a₁, ω', hc, hω, rfl⟩ | ⟨ρ, l, h0, hρ, hl⟩)
      · exact .inl ⟨c, σ₁.1, a₁, ω', (contChain_frameS.1 hc).1, hω, rfl⟩
      · refine .inr ⟨fun n => ((ρ n).1.1, (ρ n).2), l, by simp [h0], fun n => ?_, hl⟩
        exact (mem_frameS_ret.1 (hρ n)).1

theorem frameS_iterS (t : ObsTriple E S A ((B ⊕ A) ⊕ PUnit.{u + 1})) :
    frameS S' (SessionIter.iterS t) = SessionIter.iterS (frameS S' t) := by
  rw [SessionIter.iterS, SessionIter.iterS, frameS_iterT, frameS_mapT]

end Silmaril.Proofs.Games.Abstract.SessionIter2

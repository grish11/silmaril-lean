module

public import Silmaril.Games.Abstract.SessionIter2.Defs
public import Silmaril.Games.Abstract.SessionIter.Thms
public import Silmaril.Games.Abstract.FunctionIter.Defs
public import Silmaril.Proofs.Games.Abstract.SessionIter2.Det

/-!
# Pending, divergent and infinite plays of sequenced and iterated sessions (proofs)

The generic descriptions of session plays (`StratSession.mem_pending`, `mem_div_iff`,
`mem_inf_iff_of_det`) are in terms of the triple components (`satP`, divergent behaviours,
productive streams) and its completed rounds. Here these components are computed for `seqS t u`
and `iterS t` in terms of `t` and `u`:

* divergences and productive streams by unfolding `seqT`, `caseT` and `iterT`, a continuing trap
  continuing with `trapS`, which has no call, divergence or stream;
* call prefixes (`satP`) by `StratOps.sat_seqT` (a total second part) or `sat_seqT_of_adm` (an
  admissible first part), and by `admissible_iterT` for an admissible body, after which the
  pending component of the operation is already saturated.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.SessionIter2

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
  Silmaril.Games.Abstract.StratOps Silmaril.Games.Abstract.StratThread
  Silmaril.Games.Abstract.StratSession Silmaril.Games.Abstract.SessionCat
  Silmaril.Games.Abstract.SessionIter Silmaril.Games.Abstract.SessionIter2

universe u

variable {E : Sig.{u}} {S A B C : Type u}

theorem satP_eq_of_adm {X : ObsTriple E S A B} (h : Admissible X) : satP X = X.2.1 :=
  congrArg (fun y : ObsTriple E S A B => y.2.1) h

theorem infRounds_iff {X : ObsTriple E S A B} {s₀ : S} {a : ℕ → A} {r : ℕ → List (Call E) × B}
    {s : ℕ → S} :
    InfRounds X s₀ a r s ↔ s 0 = s₀ ∧ ∀ k, ((r k).1, End.ret (r k).2 (s (k + 1))) ∈ X.1 (s k) (a k) :=
  ⟨fun h => ⟨h.zero, h.step⟩, fun h => ⟨h.1, h.2⟩⟩

/-! ## Sequencing -/

section Seq

variable {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})} {u : ObsTriple E S B (C ⊕ PUnit.{u + 1})}

theorem mem_seqS_div {s : S} {a : A} {c : List (Call E)} :
    (c, End.div) ∈ (seqS t u).1 s a ↔ (c, End.div) ∈ t.1 s a ∨
      ∃ c₁ b s₁ c₂, (c₁, End.ret (.inl b) s₁) ∈ t.1 s a ∧ (c₂, End.div) ∈ u.1 s₁ b ∧
        c = c₁ ++ c₂ := by
  rw [SessionCat.mem_seqS]
  constructor
  · rintro (⟨_, _, hx⟩ | ⟨c', h, hx⟩ | ⟨_, _, _, hx⟩ | ⟨c₁, b, s₁, c₂, e, h₁, he, hx⟩)
    · cases hx
    · cases hx; exact .inl h
    · cases hx
    · simp only [Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact .inr ⟨c₁, b, s₁, c₂, h₁, he, rfl⟩
  · rintro (h | ⟨c₁, b, s₁, c₂, h₁, he, rfl⟩)
    · exact .inr (.inl ⟨c, h, rfl⟩)
    · exact .inr (.inr (.inr ⟨c₁, b, s₁, c₂, _, h₁, he, rfl⟩))

theorem mem_seqS_inf {s : S} {a : A} {ω : ℕ → Call E} :
    ω ∈ (seqS t u).2.2 s a ↔ ω ∈ t.2.2 s a ∨
      ∃ c b s₁ ω', (c, End.ret (.inl b) s₁) ∈ t.1 s a ∧ ω' ∈ u.2.2 s₁ b ∧ ω = c ++ₛ ω' := by
  constructor
  · rintro (h | ⟨c, x, s₁, ω', h₁, h₂, rfl⟩)
    · exact .inl h
    · rcases x with b | ⟨⟩
      · exact .inr ⟨c, b, s₁, ω', h₁, h₂, rfl⟩
      · exact (h₂ : False).elim
  · rintro (h | ⟨c, b, s₁, ω', h₁, h₂, rfl⟩)
    · exact .inl h
    · exact .inr ⟨c, .inl b, s₁, ω', h₁, h₂, rfl⟩

theorem not_mem_satP_trapS {s : S} {c : List (Call E)} {m : E.Op} :
    (c, m) ∉ satP (trapS : ObsTriple E S PUnit.{u + 1} (C ⊕ PUnit.{u + 1})) s PUnit.unit := by
  rintro (h | ⟨_, _, h, -⟩ | ⟨d, e, ⟨y, hy, hyd⟩, n, c', hd⟩ | ⟨_, h, -⟩)
  · exact h
  · exact h
  · have hy : y = ([], End.ret PUnit.unit s) := hy
    subst hy
    simp only [Prod.mk.injEq] at hyd
    obtain ⟨rfl, -⟩ := hyd
    simp at hd
  · exact h

theorem total_caseT_trapS (hu : Total u) : Total (caseT u (trapS (B := C))) := by
  intro s x
  rcases x with b | ⟨⟩
  · exact hu s b
  · exact .inl ⟨_, ([], End.ret PUnit.unit s), rfl, rfl⟩

/-- The call prefixes of a sequence, once its saturation is computed componentwise. -/
theorem mem_satP_seqS_of (h : sat (seqT (sat t) (sat (caseT u trapS))) = sat (seqS t u))
    {s : S} {a : A} {c : List (Call E)} {m : E.Op} :
    (c, m) ∈ satP (seqS t u) s a ↔ (c, m) ∈ satP t s a ∨
      ∃ c₁ b s₁ c₂, (c₁, End.ret (.inl b) s₁) ∈ t.1 s a ∧ (c₂, m) ∈ satP u s₁ b ∧
        c = c₁ ++ c₂ := by
  have hX : satP (seqS t u) = (seqT (sat t) (sat (caseT u trapS))).2.1 := by
    rw [← satP_eq_of_adm (admissible_seqT admissible_sat admissible_sat)]
    exact (congrArg (fun y : ObsTriple E S A (C ⊕ PUnit.{u + 1}) => y.2.1) h).symm
  rw [hX, sat_caseT]
  constructor
  · rintro (h₁ | ⟨c₁, x, s₁, c₂, m', h₁, h₂, he⟩)
    · exact .inl h₁
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      rcases x with b | ⟨⟩
      · exact .inr ⟨c₁, b, s₁, c₂, h₁, h₂, rfl⟩
      · exact (not_mem_satP_trapS h₂).elim
  · rintro (h₁ | ⟨c₁, b, s₁, c₂, h₁, h₂, rfl⟩)
    · exact .inl h₁
    · exact .inr ⟨c₁, .inl b, s₁, c₂, m, h₁, h₂, rfl⟩

theorem mem_satP_seqS (hu : Total u) {s : S} {a : A} {c : List (Call E)} {m : E.Op} :
    (c, m) ∈ satP (seqS t u) s a ↔ (c, m) ∈ satP t s a ∨
      ∃ c₁ b s₁ c₂, (c₁, End.ret (.inl b) s₁) ∈ t.1 s a ∧ (c₂, m) ∈ satP u s₁ b ∧
        c = c₁ ++ c₂ :=
  mem_satP_seqS_of (sat_seqT (total_caseT_trapS hu))

theorem mem_satP_seqS_of_adm (ht : Admissible t) {s : S} {a : A} {c : List (Call E)}
    {m : E.Op} :
    (c, m) ∈ satP (seqS t u) s a ↔ (c, m) ∈ satP t s a ∨
      ∃ c₁ b s₁ c₂, (c₁, End.ret (.inl b) s₁) ∈ t.1 s a ∧ (c₂, m) ∈ satP u s₁ b ∧
        c = c₁ ++ c₂ :=
  mem_satP_seqS_of (sat_seqT_of_adm ht)

end Seq

/-! ## Iteration -/

section Iter

variable {t : ObsTriple E S A ((B ⊕ A) ⊕ PUnit.{u + 1})}

theorem mem_mapT_iterAssoc_inr {s s' : S} {a a' : A} {c : List (Call E)} :
    (c, End.ret (.inr a') s') ∈ (mapT t iterAssoc).1 s a ↔
      (c, End.ret (.inl (.inr a')) s') ∈ t.1 s a := by
  constructor
  · rintro ⟨⟨c₀, e⟩, h, hx⟩
    simp only [Prod.mk.injEq] at hx
    obtain ⟨rfl, hx⟩ := hx
    rcases e with ⟨(b | a₀) | ⟨⟩, s₀⟩ | _ | _ <;> simp [FullFun.endMap, iterAssoc] at hx
    obtain ⟨rfl, rfl⟩ := hx
    exact h
  · intro h
    exact ⟨_, h, rfl⟩

theorem mem_mapT_div {s : S} {a : A} {c : List (Call E)} :
    (c, End.div) ∈ (mapT t iterAssoc).1 s a ↔ (c, End.div) ∈ t.1 s a := by
  constructor
  · rintro ⟨⟨c₀, e⟩, h, hx⟩
    simp only [Prod.mk.injEq] at hx
    obtain ⟨rfl, hx⟩ := hx
    rcases e with _ | _ | _ <;> simp [FullFun.endMap] at hx
    exact h
  · intro h
    exact ⟨_, h, rfl⟩

theorem contS_iff {s s' : S} {a a' : A} {c : List (Call E)} :
    FullFun.ContChain (mapT t iterAssoc).1 s a c s' a' ↔ ContS t s a c s' a' := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | step h₁ _ ih => exact .step (mem_mapT_iterAssoc_inr.1 h₁) ih
  · intro h
    induction h with
    | refl => exact .refl
    | step h₁ _ ih => exact .step (mem_mapT_iterAssoc_inr.2 h₁) ih

theorem iterBeh_of_contS {s s' : S} {a a' : A} {c₁ : List (Call E)} (h : ContS t s a c₁ s' a') :
    ∀ {c₂ : List (Call E)} {e : End S (B ⊕ PUnit.{u + 1})},
      AFun.IterBeh (mapT t iterAssoc).1 s' a' (c₂, e) →
        AFun.IterBeh (mapT t iterAssoc).1 s a (c₁ ++ c₂, e) := by
  induction h with
  | refl => intro c₂ e h₂; simpa using h₂
  | step h₁ _ ih =>
    intro c₂ e h₂
    rw [List.append_assoc]
    exact .step (mem_mapT_iterAssoc_inr.2 h₁) (ih h₂)

theorem div_of_iterBeh {s : S} {a : A} {y : CallBeh E S (B ⊕ PUnit.{u + 1})}
    (h : AFun.IterBeh (mapT t iterAssoc).1 s a y) (hy : y.2 = End.div) :
    ∃ c₁ s' a' c₂, ContS t s a c₁ s' a' ∧
      ((c₂, End.div) ∈ t.1 s' a' ∨ (c₂ = [] ∧ InfContS t s' a' fun _ => [])) ∧
        y.1 = c₁ ++ c₂ := by
  induction h with
  | exit _ => cases hy
  | trap _ => cases hy
  | div h => exact ⟨[], _, _, _, .refl, .inl (mem_mapT_div.1 h), rfl⟩
  | step h₁ _ ih =>
    obtain ⟨c₁, s', a', c₂, hc, hd, he⟩ := ih hy
    refine ⟨_, s', a', c₂, .step (mem_mapT_iterAssoc_inr.1 h₁) hc, hd, ?_⟩
    simp only at he ⊢
    rw [he, List.append_assoc]
  | spin σ h0 hσ =>
    exact ⟨[], _, _, [], .refl, .inr ⟨rfl, σ, h0, fun n => mem_mapT_iterAssoc_inr.1 (hσ n)⟩, rfl⟩

theorem mem_iterS_div {s : S} {a : A} {c : List (Call E)} :
    (c, End.div) ∈ (iterS t).1 s a ↔ ∃ c₁ s' a' c₂, ContS t s a c₁ s' a' ∧
      ((c₂, End.div) ∈ t.1 s' a' ∨ (c₂ = [] ∧ InfContS t s' a' fun _ => [])) ∧
        c = c₁ ++ c₂ := by
  constructor
  · intro h
    exact div_of_iterBeh h rfl
  · rintro ⟨c₁, s', a', c₂, hc, hd | ⟨rfl, σ, h0, hσ⟩, rfl⟩
    · exact iterBeh_of_contS hc (.div (mem_mapT_div.2 hd))
    · exact iterBeh_of_contS hc (.spin σ h0 fun n => mem_mapT_iterAssoc_inr.2 (hσ n))

theorem mem_iterS_inf {s : S} {a : A} {ω : ℕ → Call E} :
    ω ∈ (iterS t).2.2 s a ↔
      (∃ c s' a' ω', ContS t s a c s' a' ∧ ω' ∈ t.2.2 s' a' ∧ ω = c ++ₛ ω') ∨
        ∃ l, InfContS t s a l ∧ Shape.StreamConcat l ω := by
  constructor
  · rintro (⟨c, s', a', ω', hc, hω, rfl⟩ | ⟨σ, l, h0, hσ, hl⟩)
    · exact .inl ⟨c, s', a', ω', contS_iff.1 hc, hω, rfl⟩
    · exact .inr ⟨l, ⟨σ, h0, fun n => mem_mapT_iterAssoc_inr.1 (hσ n)⟩, hl⟩
  · rintro (⟨c, s', a', ω', hc, hω, rfl⟩ | ⟨l, ⟨σ, h0, hσ⟩, hl⟩)
    · exact .inl ⟨c, s', a', ω', contS_iff.2 hc, hω, rfl⟩
    · exact .inr ⟨σ, l, h0, fun n => mem_mapT_iterAssoc_inr.2 (hσ n), hl⟩

theorem mem_satP_iterS (ht : Admissible t) {s : S} {a : A} {c : List (Call E)} {m : E.Op} :
    (c, m) ∈ satP (iterS t) s a ↔
      ∃ c₁ s' a' c₂, ContS t s a c₁ s' a' ∧ (c₂, m) ∈ satP t s' a' ∧ c = c₁ ++ c₂ := by
  have h₁ : satP (iterS t) = (iterS t).2.1 :=
    satP_eq_of_adm (admissible_iterT (admissible_mapT ht iterAssoc))
  rw [h₁, satP_eq_of_adm ht]
  constructor
  · rintro ⟨c₁, s', a', c₂, m', hc, hm, he⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨c₁, s', a', c₂, contS_iff.1 hc, hm, rfl⟩
  · rintro ⟨c₁, s', a', c₂, hc, hm, rfl⟩
    exact ⟨c₁, s', a', c₂, m, contS_iff.2 hc, hm, rfl⟩

end Iter

end Silmaril.Proofs.Games.Abstract.SessionIter2

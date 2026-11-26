module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Thms

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category

open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay

universe w x

variable {n m l : Nat} {α : Type w} {σ : Type x}

theorem bind_top_iff {p : Behaviour n α σ} {k : Fin n → Value α → σ → Behaviour m α σ} :
    p.bind k = ⊤ ↔ p = ⊤ ∨ ∃ i a s, p.Ordinary (.ret i a s) ∧ k i a s = ⊤ := by
  classical
  by_cases hp : p = ⊤
  · simp [hp]
  · simp [Behaviour.bind, Behaviour.Ordinary, hp]

/-- The two ways to obtain an ordinary observation from sequencing. -/
abbrev terminal (p : Behaviour n α σ) : Outcome m α σ → Prop
  | .ret _ _ _ => False
  | .fault s => p.Ordinary (.fault s)
  | .diverge => p.Ordinary .diverge

theorem ordinary_bind {p : Behaviour n α σ} {k : Fin n → Value α → σ → Behaviour m α σ}
    (ordinary : p.bind k ≠ ⊤) (o : Outcome m α σ) :
    (p.bind k).Ordinary o ↔ terminal p o ∨
      ∃ i a s, p.Ordinary (.ret i a s) ∧ (k i a s).Ordinary o := by
  classical
  have hp : p ≠ ⊤ := fun h => ordinary (bind_top_iff.mpr (.inl h))
  have hk {i a s} (h : .ret i a s ∈ p.possible) : k i a s ≠ ⊤ :=
    fun top => ordinary (bind_top_iff.mpr (.inr ⟨i, a, s, ⟨hp, h⟩, top⟩))
  have hn : ¬(p = ⊤ ∨ ∃ i a s, .ret i a s ∈ p.possible ∧ k i a s = ⊤) := by
    rintro (h | ⟨i, a, s, h, top⟩)
    · exact hp h
    · exact hk h top
  change ((p.bind k ≠ ⊤) ∧ _) ↔ _
  rw [and_iff_right ordinary]
  rw [Behaviour.bind, ite_eq_right hn]
  change o ∈ Outcome.bind p.possible (fun i a s => (k i a s).possible) ↔ _
  refine or_congr ?_ ?_
  · cases o <;> simp [terminal, Behaviour.Ordinary, hp]
  · exact ⟨fun ⟨i, a, s, ret, body⟩ => ⟨i, a, s, ⟨hp, ret⟩, ⟨hk ret, body⟩⟩,
      fun ⟨i, a, s, ret, body⟩ => ⟨i, a, s, ret.2, body.2⟩⟩

theorem behaviour_ext {p q : Behaviour n α σ} (top : p = ⊤ ↔ q = ⊤)
    (ordinary : ∀ o, p.Ordinary o ↔ q.Ordinary o) : p = q := by
  by_cases hp : p = ⊤
  · exact hp.trans (top.mp hp).symm
  have hq : q ≠ ⊤ := fun h => hp (top.mpr h)
  obtain ⟨P, rfl⟩ := WithTop.ne_top_iff_exists.mp hp
  obtain ⟨Q, rfl⟩ := WithTop.ne_top_iff_exists.mp hq
  apply WithTop.coe_inj.mpr
  exact Set.ext fun o => by
    simpa [Behaviour.Ordinary, Behaviour.possible, WithTop.coe_ne_top] using ordinary o

theorem bind_congr {p : Behaviour n α σ} {k h : Fin n → Value α → σ → Behaviour m α σ}
    (same : ∀ i a s, p.Ordinary (.ret i a s) → k i a s = h i a s) : p.bind k = p.bind h := by
  have top : p.bind k = ⊤ ↔ p.bind h = ⊤ := by
    simp only [bind_top_iff]
    refine or_congr_right ⟨fun ⟨i, a, s, h, top⟩ => ⟨i, a, s, h, same i a s h ▸ top⟩,
      fun ⟨i, a, s, h, top⟩ => ⟨i, a, s, h, (same i a s h).symm ▸ top⟩⟩
  refine behaviour_ext top ?_
  intro o
  by_cases hp : p.bind k = ⊤
  · simp [hp, top.mp hp, Behaviour.Ordinary]
  have hq : p.bind h ≠ ⊤ := fun h => hp (top.mpr h)
  rw [ordinary_bind hp, ordinary_bind hq]
  refine or_congr_right ⟨fun ⟨i, a, s, h, out⟩ => ⟨i, a, s, h, same i a s h ▸ out⟩,
    fun ⟨i, a, s, h, out⟩ => ⟨i, a, s, h, (same i a s h).symm ▸ out⟩⟩

theorem bind_assoc (p : Behaviour n α σ) (k : Fin n → Value α → σ → Behaviour m α σ)
    (h : Fin m → Value α → σ → Behaviour l α σ) :
    (p.bind k).bind h = p.bind (fun i a s => (k i a s).bind h) := by
  let left := (p.bind k).bind h
  let right := p.bind (fun i a s => (k i a s).bind h)
  have top : left = ⊤ ↔ right = ⊤ := by
    constructor
    · intro top
      rcases bind_top_iff.mp top with hk | ⟨j, b, t, out, ht⟩
      · rcases bind_top_iff.mp hk with hp | ⟨i, a, s, v, fail⟩
        · exact bind_top_iff.mpr (.inl hp)
        · exact bind_top_iff.mpr (.inr ⟨i, a, s, v, bind_top_iff.mpr (.inl fail)⟩)
      · obtain ⟨i, a, s, v, ret⟩ := ((ordinary_bind out.1 _).mp out).resolve_left id
        exact bind_top_iff.mpr (.inr ⟨i, a, s, v, bind_top_iff.mpr (.inr ⟨j, b, t, ret, ht⟩)⟩)
    · intro top
      rcases bind_top_iff.mp top with hp | ⟨i, a, s, v, fail⟩
      · exact bind_top_iff.mpr (.inl (bind_top_iff.mpr (.inl hp)))
      · rcases bind_top_iff.mp fail with hk | ⟨j, b, t, ret, ht⟩
        · exact bind_top_iff.mpr (.inl (bind_top_iff.mpr (.inr ⟨i, a, s, v, hk⟩)))
        · by_cases pm : p.bind k = ⊤
          · exact bind_top_iff.mpr (.inl pm)
          · have out := (ordinary_bind pm (.ret j b t)).mpr (.inr ⟨i, a, s, v, ret⟩)
            exact bind_top_iff.mpr (.inr ⟨j, b, t, out, ht⟩)
  refine behaviour_ext top ?_
  intro o
  change left.Ordinary o ↔ right.Ordinary o
  by_cases hl : left = ⊤
  · simp [hl, top.mp hl, Behaviour.Ordinary]
  have hr : right ≠ ⊤ := fun e => hl (top.mpr e)
  have pm : p.bind k ≠ ⊤ := fun e => hl (bind_top_iff.mpr (.inl e))
  have keeps {i a s} (v : p.Ordinary (.ret i a s)) : (k i a s).bind h ≠ ⊤ :=
    fun e => hr (bind_top_iff.mpr (.inr ⟨i, a, s, v, e⟩))
  rw [ordinary_bind hl, ordinary_bind hr]
  have early : terminal (p.bind k) o ↔ terminal p o ∨
      ∃ i a s, p.Ordinary (.ret i a s) ∧ terminal (k i a s) o := by
    cases o with
    | ret => simp [terminal]
    | fault | diverge => exact ordinary_bind pm _
  rw [early]
  constructor
  · rintro ((out | ⟨i, a, s, ret, last⟩) | ⟨j, b, t, ret, out⟩)
    · exact .inl out
    · exact .inr ⟨i, a, s, ret, (ordinary_bind (keeps ret) o).mpr (.inl last)⟩
    · obtain ⟨i, a, s, first, middle⟩ := ((ordinary_bind pm _).mp ret).resolve_left id
      exact .inr ⟨i, a, s, first, (ordinary_bind (keeps first) o).mpr (.inr ⟨j, b, t, middle, out⟩)⟩
  · rintro (out | ⟨i, a, s, first, rest⟩)
    · exact .inl (.inl out)
    · rcases (ordinary_bind (keeps first) o).mp rest with last | ⟨j, b, t, middle, out⟩
      · exact .inl (.inr ⟨i, a, s, first, last⟩)
      · exact .inr ⟨j, b, t, (ordinary_bind pm _).mpr (.inr ⟨i, a, s, first, middle⟩), out⟩

abbrev pureReturn (i : Fin n) (a : Value α) (s : σ) : Behaviour n α σ :=
  ↑({.ret i a s} : Set (Outcome n α σ))

theorem ordinary_return_iff {i : Fin n} {a : Value α} {s : σ} {o : Outcome n α σ} :
    (pureReturn i a s).Ordinary o ↔ o = .ret i a s := by
  simp [pureReturn, Behaviour.Ordinary, Behaviour.possible]

theorem return_bind (i : Fin n) (a : Value α) (s : σ)
    (k : Fin n → Value α → σ → Behaviour m α σ) : (pureReturn i a s).bind k = k i a s := by
  have top : (pureReturn i a s).bind k = ⊤ ↔ k i a s = ⊤ := by
    simp [bind_top_iff, ordinary_return_iff, WithTop.coe_ne_top]
  refine behaviour_ext top ?_
  intro o
  by_cases h : k i a s = ⊤
  · simp [h, top.mpr h, Behaviour.Ordinary]
  rw [ordinary_bind (fun t => h (top.mp t))]
  cases o <;> simp [terminal, ordinary_return_iff]

theorem bind_return (p : Behaviour n α σ) : p.bind pureReturn = p := by
  have top : p.bind pureReturn = ⊤ ↔ p = ⊤ := by simp [bind_top_iff, WithTop.coe_ne_top]
  refine behaviour_ext top ?_
  intro o
  by_cases hp : p = ⊤
  · simp [hp, Behaviour.Ordinary]
  rw [ordinary_bind (fun t => hp (top.mp t))]
  cases o <;> simp [terminal, ordinary_return_iff]

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category

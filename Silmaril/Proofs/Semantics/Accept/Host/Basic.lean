module

public import Silmaril.Semantics.Accept.Host.Defs

/-! # Proofs: runs of host models, languages and simulations -/

@[expose] public section

namespace Silmaril.Proofs.Semantics.Accept.Host

open Silmaril.Accept Silmaril.Accept.Host

universe u v w w'

variable {E : Type u} {X : Type v} {S : Type w}

theorem run_append {h : Host E X S} {s s₁ s₂ : S} {t u : List E} {A B : Set X}
    (ht : h.Run s t s₁ A) (hu : h.Run s₁ u s₂ B) : h.Run s (t ++ u) s₂ (A ∪ B) := by
  induction ht with
  | nil => simpa using hu
  | cons hr _ ih =>
      rw [Set.union_assoc]
      exact .cons hr (ih hu)

theorem run_append_inv {h : Host E X S} {s s₂ : S} {t u : List E} {C : Set X}
    (hr : h.Run s (t ++ u) s₂ C) :
    ∃ s₁ A B, h.Run s t s₁ A ∧ h.Run s₁ u s₂ B ∧ C = A ∪ B := by
  induction t generalizing s C with
  | nil => exact ⟨s, ∅, C, .nil s, hr, by simp⟩
  | cons e t ih =>
      cases hr with
      | cons he hrest =>
          obtain ⟨s₁, A, B, h1, h2, rfl⟩ := ih hrest
          exact ⟨s₁, _ ∪ A, B, .cons he h1, h2, by rw [Set.union_assoc]⟩

theorem run_sim {E' : Type u} {S' : Type w'} {h₁ : Host E X S} {h₂ : Host E' X S'}
    {f : E → E'} {R : S → S' → Prop} (hs : Host.Sim h₁ h₂ f R) :
    ∀ {s₁ : S} {s₂ : S'} {s₁' : S} {t : List E} {A : Set X}, R s₁ s₂ → h₁.Run s₁ t s₁' A →
      ∃ s₂' B, h₂.Run s₂ (t.map f) s₂' B ∧ R s₁' s₂' ∧ A ⊆ B := by
  intro s₁ s₂ s₁' t A hR hr
  induction hr generalizing s₂ with
  | nil s => exact ⟨s₂, ∅, .nil s₂, hR, le_rfl⟩
  | cons he _ ih =>
      obtain ⟨m, B₁, hB₁, hRm, hAB₁⟩ := hs.step hR he
      obtain ⟨s₂', B₂, hB₂, hR', hAB₂⟩ := ih hRm
      exact ⟨s₂', B₁ ∪ B₂, .cons hB₁ hB₂, hR', Set.union_subset_union hAB₁ hAB₂⟩

theorem lang_subset_of_sim {E' : Type u} {S' : Type w'} {h₁ : Host E X S} {h₂ : Host E' X S'}
    {f : E → E'} {R : S → S' → Prop} (hs : Host.Sim h₁ h₂ f R) (T : Set (List E)) :
    h₁.lang T ⊆ h₂.lang (List.map f '' T) := by
  intro x hx
  simp only [Host.lang, Set.mem_iUnion] at hx ⊢
  obtain ⟨t, ht, s, A, hr, hxA⟩ := hx
  obtain ⟨s', B, hr', -, hAB⟩ := run_sim hs hs.init hr
  exact ⟨t.map f, ⟨t, ht, rfl⟩, s', B, hr', hAB hxA⟩

theorem allowed_subset_of_sim {E' : Type u} {S' : Type w'} {h₁ : Host E X S}
    {h₂ : Host E' X S'} {f : E → E'} {R : S → S' → Prop} (hs : Host.Sim h₁ h₂ f R) :
    List.map f '' h₁.allowed ⊆ h₂.allowed := by
  rintro _ ⟨t, ⟨s, A, hr⟩, rfl⟩
  obtain ⟨s', B, hr', -⟩ := run_sim hs hs.init hr
  exact ⟨s', B, hr'⟩

theorem run_congr {h₁ h₂ : Host E X S} (P : E → Prop)
    (hP : ∀ s e s' A, P e → (h₁.resp s e s' A ↔ h₂.resp s e s' A)) :
    ∀ {s s' : S} {t : List E} {A : Set X}, (∀ e ∈ t, P e) → (h₁.Run s t s' A ↔ h₂.Run s t s' A) := by
  intro s s' t A ht
  induction t generalizing s A with
  | nil => exact ⟨fun h => by cases h; exact .nil _, fun h => by cases h; exact .nil _⟩
  | cons e es ih =>
      have he := ht e List.mem_cons_self
      have hes : ∀ e ∈ es, P e := fun e h => ht e (List.mem_cons_of_mem _ h)
      constructor
      · intro h; cases h with
        | cons hr hrest => exact .cons ((hP _ _ _ _ he).1 hr) ((ih hes).1 hrest)
      · intro h; cases h with
        | cons hr hrest => exact .cons ((hP _ _ _ _ he).2 hr) ((ih hes).2 hrest)

theorem run_mem_split {h : Host E X S} {x : X} :
    ∀ {s s' : S} {t : List E} {A : Set X}, h.Run s t s' A → x ∈ A →
      ∃ u e v s₁ s₂ B C, t = u ++ e :: v ∧ h.Run s u s₁ B ∧ h.resp s₁ e s₂ C ∧ x ∈ C := by
  intro s s' t A hr hx
  induction hr with
  | nil => simp at hx
  | @cons s s₁ s₂ e es A B hr hrest ih =>
      rcases hx with hx | hx
      · exact ⟨[], e, es, s, s₁, ∅, A, rfl, .nil s, hr, hx⟩
      · obtain ⟨u, e', v, m₁, m₂, B', C, rfl, hu, he, hxC⟩ := ih hx
        exact ⟨e :: u, e', v, m₁, m₂, _, C, rfl, .cons hr hu, he, hxC⟩

end Silmaril.Proofs.Semantics.Accept.Host

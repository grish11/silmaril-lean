module

public import Silmaril.Semantics.Accept.Host.Defs
import Silmaril.Proofs.Semantics.Accept.Host.Basic

/-!
# Host models: laws

* runs: concatenation and splitting (`Run.append`, `Run.append_inv`), prefixes of allowed
  traces are allowed (`allowed_prefix`);
* languages are unions over traces: `mem_lang`, monotone in the trace set (`lang_mono`),
  preserving unions (`lang_union`, `lang_iUnion`, `lang_sUnion`) but only *including* the
  intersection (`lang_inter_subset`; a strict example is in
  `Silmaril.Semantics.Accept.Handle.Examples`);
* simulations: `Run.sim`, `lang_subset_of_sim`, the identity simulation (`Sim.refl`),
  composition (`Sim.trans`), and `langOver` monotonicity in the family (`langOver_mono`).
-/

@[expose] public section

namespace Silmaril.Accept

universe u v w w' w''

namespace Host

variable {E : Type u} {X : Type v} {S : Type w} {h : Host E X S}

theorem Run.append {s s₁ s₂ : S} {t u : List E} {A B : Set X} (ht : h.Run s t s₁ A)
    (hu : h.Run s₁ u s₂ B) : h.Run s (t ++ u) s₂ (A ∪ B) :=
  Silmaril.Proofs.Semantics.Accept.Host.run_append ht hu

theorem Run.append_inv {s s₂ : S} {t u : List E} {C : Set X} (hr : h.Run s (t ++ u) s₂ C) :
    ∃ s₁ A B, h.Run s t s₁ A ∧ h.Run s₁ u s₂ B ∧ C = A ∪ B :=
  Silmaril.Proofs.Semantics.Accept.Host.run_append_inv hr

theorem Run.single {s s' : S} {e : E} {A : Set X} (hr : h.resp s e s' A) :
    h.Run s [e] s' A := by
  simpa using Run.cons hr (Run.nil s')

theorem allowed_prefix {t u : List E} (ht : t ++ u ∈ h.allowed) : t ∈ h.allowed :=
  let ⟨_, _, hr⟩ := ht
  let ⟨s₁, A, _, h1, _⟩ := Run.append_inv hr
  ⟨s₁, A, h1⟩

@[simp] theorem mem_lang {T : Set (List E)} {x : X} :
    x ∈ h.lang T ↔ ∃ t ∈ T, ∃ s A, h.Run h.init t s A ∧ x ∈ A := by
  simp [lang, accepts]

theorem lang_mono {T T' : Set (List E)} (hT : T ⊆ T') : h.lang T ⊆ h.lang T' :=
  Set.biUnion_subset_biUnion_left hT

theorem lang_union (T T' : Set (List E)) : h.lang (T ∪ T') = h.lang T ∪ h.lang T' :=
  Set.biUnion_union T T' h.accepts

theorem lang_iUnion {ι : Sort*} (T : ι → Set (List E)) : h.lang (⋃ i, T i) = ⋃ i, h.lang (T i) :=
  Set.biUnion_iUnion T h.accepts

theorem lang_sUnion (Ts : Set (Set (List E))) : h.lang (⋃₀ Ts) = ⋃ T ∈ Ts, h.lang T := by
  ext x; simp only [mem_lang, Set.mem_sUnion, Set.mem_iUnion]; aesop

theorem lang_empty : h.lang ∅ = ∅ := by simp [lang]

theorem lang_inter_subset (T T' : Set (List E)) : h.lang (T ∩ T') ⊆ h.lang T ∩ h.lang T' :=
  Set.subset_inter (lang_mono Set.inter_subset_left) (lang_mono Set.inter_subset_right)

theorem Run.sim {E' : Type u} {S' : Type w'} {h₂ : Host E' X S'} {f : E → E'}
    {R : S → S' → Prop} (hs : Sim h h₂ f R) {s₁ s₁' : S} {s₂ : S'} {t : List E} {A : Set X}
    (hR : R s₁ s₂) (hr : h.Run s₁ t s₁' A) :
    ∃ s₂' B, h₂.Run s₂ (t.map f) s₂' B ∧ R s₁' s₂' ∧ A ⊆ B :=
  Silmaril.Proofs.Semantics.Accept.Host.run_sim hs hR hr

/-- **Simulation transfers acceptance** along the event map. -/
theorem lang_subset_of_sim {E' : Type u} {S' : Type w'} {h₂ : Host E' X S'} {f : E → E'}
    {R : S → S' → Prop} (hs : Sim h h₂ f R) (T : Set (List E)) :
    h.lang T ⊆ h₂.lang (List.map f '' T) :=
  Silmaril.Proofs.Semantics.Accept.Host.lang_subset_of_sim hs T

/-- The same-event form: a simulation by `h₂` makes `h₂` accept at least as much. -/
theorem lang_subset_of_sim_id {S' : Type w'} {h₂ : Host E X S'} {R : S → S' → Prop}
    (hs : Sim h h₂ id R) (T : Set (List E)) : h.lang T ⊆ h₂.lang T := by
  simpa using lang_subset_of_sim hs T

theorem allowed_subset_of_sim {E' : Type u} {S' : Type w'} {h₂ : Host E' X S'} {f : E → E'}
    {R : S → S' → Prop} (hs : Sim h h₂ f R) : List.map f '' h.allowed ⊆ h₂.allowed :=
  Silmaril.Proofs.Semantics.Accept.Host.allowed_subset_of_sim hs

/-- Hosts with the same responses to the events of a trace class have the same runs on it. -/
theorem Run.congr {h₂ : Host E X S} (P : E → Prop)
    (hP : ∀ s e s' A, P e → (h.resp s e s' A ↔ h₂.resp s e s' A)) {s s' : S} {t : List E}
    {A : Set X} (ht : ∀ e ∈ t, P e) : h.Run s t s' A ↔ h₂.Run s t s' A :=
  Silmaril.Proofs.Semantics.Accept.Host.run_congr P hP ht

theorem lang_congr {h₂ : Host E X S} (P : E → Prop)
    (hP : ∀ s e s' A, P e → (h.resp s e s' A ↔ h₂.resp s e s' A)) (hi : h.init = h₂.init)
    {T : Set (List E)} (hT : ∀ t ∈ T, ∀ e ∈ t, P e) : h.lang T = h₂.lang T := by
  ext x
  simp only [mem_lang]
  constructor
  · rintro ⟨t, ht, s, A, hr, hx⟩
    exact ⟨t, ht, s, A, hi ▸ (Run.congr P hP (hT t ht)).1 hr, hx⟩
  · rintro ⟨t, ht, s, A, hr, hx⟩
    exact ⟨t, ht, s, A, (Run.congr P hP (hT t ht)).2 (hi ▸ hr), hx⟩

/-- An accepted value is accepted by one event of the run, after a run of the prefix. -/
theorem Run.mem_split {s s' : S} {t : List E} {A : Set X} {x : X} (hr : h.Run s t s' A)
    (hx : x ∈ A) :
    ∃ u e v s₁ s₂ B C, t = u ++ e :: v ∧ h.Run s u s₁ B ∧ h.resp s₁ e s₂ C ∧ x ∈ C :=
  Silmaril.Proofs.Semantics.Accept.Host.run_mem_split hr hx

theorem Sim.refl (h : Host E X S) : Sim h h id Eq :=
  ⟨rfl, fun {_ _ _ _ A} hR he => ⟨_, A, hR ▸ he, rfl, le_rfl⟩⟩

theorem Sim.trans {E' E'' : Type u} {S' : Type w'} {S'' : Type w''} {h₂ : Host E' X S'}
    {h₃ : Host E'' X S''} {f : E → E'} {g : E' → E''} {R : S → S' → Prop}
    {R' : S' → S'' → Prop} (h₁₂ : Sim h h₂ f R) (h₂₃ : Sim h₂ h₃ g R') :
    Sim h h₃ (g ∘ f) (fun a c => ∃ b, R a b ∧ R' b c) where
  init := ⟨_, h₁₂.init, h₂₃.init⟩
  step := by
    rintro _ _ _ _ _ ⟨b, hab, hbc⟩ he
    obtain ⟨b', B, hb, hR, hAB⟩ := h₁₂.step hab he
    obtain ⟨c', C, hc, hR', hBC⟩ := h₂₃.step hbc hb
    exact ⟨c', C, hc, ⟨b', hR, hR'⟩, hAB.trans hBC⟩

end Host

theorem langOver_mono {ι κ : Sort*} {E : Type u} {X : Type v} {S : Type w}
    {Hs : ι → Host E X S} {Ks : κ → Host E X S} (hHK : ∀ i, ∃ k, Hs i = Ks k)
    (T : Set (List E)) : langOver Hs T ⊆ langOver Ks T := by
  intro x hx
  simp only [langOver, Set.mem_iUnion] at hx ⊢
  obtain ⟨i, hi⟩ := hx
  obtain ⟨k, hk⟩ := hHK i
  exact ⟨k, hk ▸ hi⟩

theorem mem_langOver {ι : Sort*} {E : Type u} {X : Type v} {S : Type w} {Hs : ι → Host E X S}
    {T : Set (List E)} {x : X} : x ∈ langOver Hs T ↔ ∃ i, x ∈ (Hs i).lang T := by
  simp [langOver]

end Silmaril.Accept

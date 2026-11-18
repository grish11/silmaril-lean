module

public import Silmaril.Games.Abstract.StratThread.Thms

/-!
# Bisimilarity of store-deterministic triples from their round observations

For store-deterministic triples without plain traps, the initial stores are bisimilar
(`StratThread.ObsEq`) iff the two triples have the same completed rounds, and after each the same
divergences, call prefixes and productive streams (`obsEq_iff_rounds`). The relation is "reached
by the same rounds". Also: a coherent infinite sequence of rounds transfers along a bisimulation
(`InfRounds.transfer`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
open Silmaril.Games.Abstract.StratThread

variable {E : Sig.{0}} {S S' A B : Type} {t : ObsTriple E S A B} {t' : ObsTriple E S' A B}

theorem rounds_det (ht : StoreDet t) {s s₁ s₂ : S} {rs : List (A × List (Call E) × B)}
    (h₁ : Rounds t s rs s₁) (h₂ : Rounds t s rs s₂) : s₁ = s₂ := by
  induction h₁ generalizing s₂ with
  | nil => cases h₂; rfl
  | cons h _ ih =>
    cases h₂ with
    | cons h' hr' =>
      obtain rfl := ht _ _ _ _ _ _ h h'
      exact ih hr'

theorem rounds_snoc {s s₂ : S} :
    ∀ {rs : List (A × List (Call E) × B)} {a : A} {c : List (Call E)} {b : B},
      Rounds t s (rs ++ [(a, c, b)]) s₂ ↔ ∃ s₁, Rounds t s rs s₁ ∧ (c, End.ret b s₂) ∈ t.1 s₁ a
  | [], a, c, b => by
    constructor
    · intro h
      cases h with
      | cons h hr => cases hr; exact ⟨s, .nil s, h⟩
    · rintro ⟨s₁, h₁, h⟩
      cases h₁
      exact .cons h (.nil _)
  | (a₀, c₀, b₀) :: rs, a, c, b => by
    constructor
    · intro h
      cases h with
      | cons h hr =>
        obtain ⟨s₁, h₁, h₂⟩ := (rounds_snoc (s := _) (rs := rs)).1 hr
        exact ⟨s₁, .cons h h₁, h₂⟩
    · rintro ⟨s₁, h₁, h⟩
      cases h₁ with
      | cons h₀ hr => exact .cons h₀ ((rounds_snoc (rs := rs)).2 ⟨s₁, hr, h⟩)

/-- **Bisimilarity from round observations.** -/
theorem obsEq_of_rounds (ht : StoreDet t) (ht' : StoreDet t')
    (hn : ∀ s a c, (c, End.trap) ∉ t.1 s a) (hn' : ∀ s a c, (c, End.trap) ∉ t'.1 s a)
    {s₀ : S} {s₀' : S'}
    (hF : ∀ rs, (∃ s, Rounds t s₀ rs s) ↔ ∃ s', Rounds t' s₀' rs s')
    (hD : ∀ rs a c, (∃ s, Rounds t s₀ rs s ∧ (c, End.div) ∈ t.1 s a) ↔
      ∃ s', Rounds t' s₀' rs s' ∧ (c, End.div) ∈ t'.1 s' a)
    (hP : ∀ rs a x, (∃ s, Rounds t s₀ rs s ∧ x ∈ satP t s a) ↔
      ∃ s', Rounds t' s₀' rs s' ∧ x ∈ satP t' s' a)
    (hI : ∀ rs a ω, (∃ s, Rounds t s₀ rs s ∧ ω ∈ t.2.2 s a) ↔
      ∃ s', Rounds t' s₀' rs s' ∧ ω ∈ t'.2.2 s' a) :
    ObsEq t t' s₀ s₀' := by
  refine ⟨fun s s' => ∃ rs, Rounds t s₀ rs s ∧ Rounds t' s₀' rs s', ?_, [], .nil _, .nil _⟩
  rintro s s' ⟨rs, h, h'⟩
  refine ⟨fun a c => ⟨fun hc => (hn _ _ _ hc).elim, fun hc => (hn' _ _ _ hc).elim⟩,
    fun a c => ⟨fun hc => ?_, fun hc => ?_⟩, ?_, ?_, ?_, ?_⟩
  · obtain ⟨s'', h'', hd⟩ := (hD rs a c).1 ⟨s, h, hc⟩
    rwa [rounds_det ht' h' h'']
  · obtain ⟨s'', h'', hd⟩ := (hD rs a c).2 ⟨s', h', hc⟩
    rwa [rounds_det ht h h'']
  · funext a
    ext x
    constructor
    · intro hx
      obtain ⟨s'', h'', hd⟩ := (hP rs a x).1 ⟨s, h, hx⟩
      rwa [rounds_det ht' h' h'']
    · intro hx
      obtain ⟨s'', h'', hd⟩ := (hP rs a x).2 ⟨s', h', hx⟩
      rwa [rounds_det ht h h'']
  · funext a
    ext ω
    constructor
    · intro hx
      obtain ⟨s'', h'', hd⟩ := (hI rs a ω).1 ⟨s, h, hx⟩
      rwa [rounds_det ht' h' h'']
    · intro hx
      obtain ⟨s'', h'', hd⟩ := (hI rs a ω).2 ⟨s', h', hx⟩
      rwa [rounds_det ht h h'']
  · intro a c b s₁ hc
    obtain ⟨s₁', hr'⟩ := (hF (rs ++ [(a, c, b)])).1 ⟨s₁, rounds_snoc.2 ⟨s, h, hc⟩⟩
    obtain ⟨s'', h'', hc'⟩ := rounds_snoc.1 hr'
    rw [rounds_det ht' h' h'']
    exact ⟨s₁', hc', rs ++ [(a, c, b)], rounds_snoc.2 ⟨s, h, hc⟩, hr'⟩
  · intro a c b s₁' hc
    obtain ⟨s₁, hr⟩ := (hF (rs ++ [(a, c, b)])).2 ⟨s₁', rounds_snoc.2 ⟨s', h', hc⟩⟩
    obtain ⟨s'', h'', hc'⟩ := rounds_snoc.1 hr
    rw [rounds_det ht h h'']
    exact ⟨s₁, hc', rs ++ [(a, c, b)], hr, rounds_snoc.2 ⟨s', h', hc⟩⟩

/-- Along a bisimulation, the completed rounds transfer, with related final stores. -/
theorem rounds_transfer {R : S → S' → Prop} (hR : IsBisim t t' R) :
    ∀ {s : S} {s' : S'} {rs : List (A × List (Call E) × B)} {s₁ : S},
      R s s' → Rounds t s rs s₁ → ∃ s₁', Rounds t' s' rs s₁' ∧ R s₁ s₁'
  | _, s', _, _, hs, .nil _ => ⟨s', .nil _, hs⟩
  | _, _, _, _, hs, .cons h hr => by
    obtain ⟨s₂', h', hs₂⟩ := (hR _ _ hs).ret _ _ _ _ h
    obtain ⟨s₁', hr', hs₁⟩ := rounds_transfer hR hs₂ hr
    exact ⟨s₁', .cons h' hr', hs₁⟩

/-- **Round observations from bisimilarity.** -/
theorem rounds_of_obsEq {s₀ : S} {s₀' : S'} (h : ObsEq t t' s₀ s₀') :
    (∀ rs, (∃ s, Rounds t s₀ rs s) → ∃ s', Rounds t' s₀' rs s') ∧
    (∀ rs a c, (∃ s, Rounds t s₀ rs s ∧ (c, End.div) ∈ t.1 s a) →
      ∃ s', Rounds t' s₀' rs s' ∧ (c, End.div) ∈ t'.1 s' a) ∧
    (∀ rs a ω, (∃ s, Rounds t s₀ rs s ∧ ω ∈ t.2.2 s a) →
      ∃ s', Rounds t' s₀' rs s' ∧ ω ∈ t'.2.2 s' a) := by
  obtain ⟨R, hR, h₀⟩ := h
  refine ⟨fun rs ⟨s, hs⟩ => ?_, fun rs a c ⟨s, hs, hd⟩ => ?_, fun rs a ω ⟨s, hs, hi⟩ => ?_⟩
  · obtain ⟨s', h', -⟩ := rounds_transfer hR h₀ hs
    exact ⟨s', h'⟩
  · obtain ⟨s', h', hss⟩ := rounds_transfer hR h₀ hs
    exact ⟨s', h', ((hR _ _ hss).div a c).1 hd⟩
  · obtain ⟨s', h', hss⟩ := rounds_transfer hR h₀ hs
    exact ⟨s', h', (hR _ _ hss).inf ▸ hi⟩

/-- **A coherent infinite sequence of rounds transfers along a bisimulation.** -/
theorem InfRounds.transfer {R : S → S' → Prop} (hR : IsBisim t t' R) {s₀ : S} {s₀' : S'}
    (h₀ : R s₀ s₀') {a : ℕ → A} {r : ℕ → List (Call E) × B} {s : ℕ → S}
    (h : InfRounds t s₀ a r s) : ∃ s' : ℕ → S', InfRounds t' s₀' a r s' := by
  have step : ∀ k (x : {y : S' // R (s k) y}), ∃ y : {y : S' // R (s (k + 1)) y},
      ((r k).1, End.ret (r k).2 y.1) ∈ t'.1 x.1 (a k) := by
    intro k x
    obtain ⟨y, hy, hR'⟩ := (hR _ _ x.2).ret _ _ _ _ (h.step k)
    exact ⟨⟨y, hR'⟩, hy⟩
  choose F hF using step
  let seq : (k : ℕ) → {y : S' // R (s k) y} := fun k =>
    Nat.rec ⟨s₀', h.zero ▸ h₀⟩ (fun k x => F k x) k
  exact ⟨fun k => (seq k).1, ⟨rfl, fun k => hF k (seq k)⟩⟩

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj

module

public import Silmaril.Proofs.Wasm.Component.DWiringChatter3.Ext

/-!
# Infinite plays of `ext`, case by case

In the routed form of an infinite play `J` of `ext e D N` (`inf_ext_routed`),
`D` plays a run `I` and the node above plays a routed run `C`.

* **Not both stop** (`not_both_stop`): the visible play of an interaction is
  at most as long as its two sides, so if `D` and `extTop e N` both stop, `J`
  is bounded. If the node above stops, `D` moves forever at its lower
  interface; if `D` stops, `C` is infinite.
* **If `D` stops, copycat is bounded and `N` moves forever**
  (`copycat_bounded_of_stop`): every move at `D`'s interface in `C` is a move
  of `D`, so `C` has boundedly many of them. Copycat forwards every outer
  move to `D`, so its half of the routed play has at most twice as many moves
  as it has at `D`'s interface, plus one. Hence copycat's half is bounded, and
  `N`'s half is infinite: the outer moves are answered by `N` itself, never
  through copycat.
* So **if copycat's half is infinite, `D` moves forever**
  (`inf_of_copycat_inf`): `D`'s imports are passed outward forever.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.DWiringChatter3

open Silmaril.Games Silmaril.Wasm.Component

universe u v w

/-! ## Counting moves at the lower interface -/

section Count

variable {α : Type u} {β : Type v} {γ : Type w}

theorem zip_countP {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {p : List (α ⊕ γ)} (h : Zip s t p) :
    s.countP Sum.isRight = t.countP Sum.isLeft := by
  induction h with
  | nil => rfl
  | left _ _ ih => simpa [List.countP_cons] using ih
  | right _ _ ih => simpa [List.countP_cons] using ih
  | sync _ _ ih => simpa [List.countP_cons] using ih

end Count

theorem countP_halves {E F₁ F₂ : Sig.{u}} (b : Bool) (p : List (Move E (F₁ ⊕ₛ F₂))) :
    (Split.halves b p).1.countP Sum.isLeft + (Split.halves b p).2.countP Sum.isLeft =
      p.countP Sum.isLeft := by
  induction p generalizing b with
  | nil => cases b <;> rfl
  | cons o p ih =>
    rcases o with l | (q | ⟨q, r⟩)
    · have h₀ := ih false
      have h₁ := ih true
      cases b <;> simp [Split.halves, List.countP_cons] <;> omega
    · rcases q with q | q <;> simp [Split.halves, ih]
    · rcases q with q | q <;> simp [Split.halves, ih]

theorem countP_route (e : Nat) (c : List (Move sigU sigU)) :
    (c.map (splitRoute e)).countP Sum.isLeft = c.countP Sum.isLeft := by
  induction c with
  | nil => rfl
  | cons o c ih =>
    rcases o with l | (q | ⟨q, r⟩)
    · simp [splitRoute, List.countP_cons, ih]
    · simp [splitRoute, ih]
    · by_cases hq : q.1 < e <;> simp [splitRoute, hq, ih]

theorem length_le_of_prefix_double {E : Sig.{u}} :
    ∀ {w : List (Ev E)} {x : List (Move E E)}, x <+: Ev.double w →
      x.length ≤ 2 * x.countP Sum.isLeft + 1
  | [], x, h => by rw [List.prefix_nil.1 h]; simp
  | y :: w, x, h => by
    rw [Ev.double_cons] at h
    obtain ⟨t, ht⟩ := h
    have hy : (Ev.copy y).length = 2 ∧ (Ev.copy y).countP Sum.isLeft = 1 := by
      cases y <;> simp [List.countP_cons]
    rcases List.append_eq_append_iff.1 ht with ⟨a', hca, -⟩ | ⟨b', rfl, hb⟩
    · by_cases hl : x.length = 2
      · have hxy : x = Ev.copy y :=
          (List.IsPrefix.eq_of_length ⟨a', hca.symm⟩ (by omega))
        subst hxy
        omega
      · have : x.length ≤ (Ev.copy y).length := by rw [hca]; simp
        omega
    · have := length_le_of_prefix_double (w := w) (x := b') ⟨t, hb.symm⟩
      simp only [List.length_append, List.countP_append]
      omega

/-- A copycat play has at most twice as many moves as lower moves, plus one. -/
theorem length_le_of_mem_id {E : Sig.{u}} {x : List (Move E E)} (h : x ∈ Strategy.id E) :
    x.length ≤ 2 * x.countP Sum.isLeft + 1 := by
  obtain ⟨w, -, hw⟩ := Strategy.mem_id.1 h
  exact length_le_of_prefix_double hw

/-! ## The cases -/

/-- **Not both sides stop.** -/
theorem not_both_stop {α : Type u} {β : Type v} {γ : Type w} {I : Set (List (α ⊕ β))}
    {K : Set (List (β ⊕ γ))} {J : Set (List (α ⊕ γ))} (hJ : IsInfPlay J)
    (h : Interleaved I K J) (s₀ : List (α ⊕ β)) (c₀ : List (β ⊕ γ)) :
    ¬ (I = prefixes s₀ ∧ K = prefixes c₀) := by
  rintro ⟨rfl, rfl⟩
  obtain ⟨p, hp, hl⟩ := hJ.unbounded (s₀.length + c₀.length + 1)
  obtain ⟨s, hs, c, hc, p', -, -, -, hpp, hz⟩ :=
    h [] List.nil_prefix [] List.nil_prefix p hp
  have h₁ := zip_length hz
  have h₂ := List.IsPrefix.length_le hs
  have h₃ := List.IsPrefix.length_le hc
  have h₄ := hpp.length_le
  omega

variable {e : Nat} {N : DStrategy sigU sigU}

/-- **If `D` stops, copycat's half is bounded and `N`'s is infinite.** -/
theorem copycat_bounded_of_stop {X : Sig.{0}} {s₀ : List (Move X sigU)}
    {C : Set (List (Move sigU sigU))} {J : Set (List (Move X sigU))}
    (hC : IsInfPlay C ∨ ∃ c₀, C = prefixes c₀)
    (hmem : ∀ c ∈ C, Legal c ∧ c.map (splitRoute e) ∈ (Strategy.id sigU).pair N.toStrategy)
    (hJ : IsInfPlay J) (h : Interleaved (prefixes s₀) C J) :
    IsInfPlay C ∧ ¬ IsInfPlay (Split.infL (List.map (splitRoute e) '' C)) ∧
      IsInfPlay (Split.infR (List.map (splitRoute e) '' C)) := by
  have hCi : IsInfPlay C := by
    rcases hC with hC | ⟨c₀, rfl⟩
    · exact hC
    · exact absurd ⟨rfl, rfl⟩ (not_both_stop hJ h s₀ c₀)
  have hJt := isTrace_of_isInfPlay hJ
  -- every member of `C` has at most `s₀.length` moves at `D`'s interface
  have hcnt : ∀ c ∈ C, c.countP Sum.isLeft ≤ s₀.length := by
    intro c hc
    obtain ⟨s, hs, c', -, _, -, -, hcc, -, hz⟩ := h [] List.nil_prefix c hc [] hJt.nil_mem
    have h₁ := zip_countP hz
    have h₂ : s.countP Sum.isRight ≤ s.length := List.countP_le_length
    have h₃ := List.IsPrefix.length_le hs
    have h₄ : c.countP Sum.isLeft ≤ c'.countP Sum.isLeft := hcc.sublist.countP_le
    omega
  have hR := isInfPlay_image hCi (splitRoute e)
  have hL : ¬ IsInfPlay (Split.infL (List.map (splitRoute e) '' C)) := by
    intro hL
    obtain ⟨u, ⟨_, ⟨c, hc, rfl⟩, hu⟩, hl⟩ := hL.unbounded (2 * s₀.length + 2)
    have h₁ := length_le_of_mem_id (Strategy.mem_pair.1 (hmem c hc).2).2.1
    have h₂ := countP_halves false (c.map (splitRoute e))
    rw [countP_route] at h₂
    have h₃ := hcnt c hc
    have h₄ := hu.length_le
    omega
  exact ⟨hCi, hL, (Split.isInfPlay_infL_or_infR hR).resolve_left hL⟩

/-- **If copycat's half is infinite, `D` moves forever.** -/
theorem inf_of_copycat_inf {X : Sig.{0}} {D : DStrategy X sigU} {I : Set (List (Move X sigU))}
    {C : Set (List (Move sigU sigU))} {J : Set (List (Move X sigU))}
    (hI : I ∈ D.inf ∨ ∃ s₀ ∈ D.toStrategy, I = prefixes s₀)
    (hC : IsInfPlay C ∨ ∃ c₀, C = prefixes c₀)
    (hmem : ∀ c ∈ C, Legal c ∧ c.map (splitRoute e) ∈ (Strategy.id sigU).pair N.toStrategy)
    (hJ : IsInfPlay J) (h : Interleaved I C J)
    (hL : IsInfPlay (Split.infL (List.map (splitRoute e) '' C))) : I ∈ D.inf := by
  rcases hI with hI | ⟨s₀, -, rfl⟩
  · exact hI
  · exact absurd hL (copycat_bounded_of_stop hC hmem hJ h).2.1

/-- **If the node above stops, `D` moves forever.** -/
theorem inf_of_top_stop {X : Sig.{0}} {D : DStrategy X sigU} {I : Set (List (Move X sigU))}
    {c₀ : List (Move sigU sigU)} {J : Set (List (Move X sigU))}
    (hI : I ∈ D.inf ∨ ∃ s₀ ∈ D.toStrategy, I = prefixes s₀) (hJ : IsInfPlay J)
    (h : Interleaved I (prefixes c₀) J) : I ∈ D.inf := by
  rcases hI with hI | ⟨s₀, -, rfl⟩
  · exact hI
  · exact absurd ⟨rfl, rfl⟩ (not_both_stop hJ h s₀ c₀)

end Silmaril.Proofs.Wasm.Component.DWiringChatter3

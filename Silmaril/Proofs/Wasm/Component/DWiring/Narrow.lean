module

public import Silmaril.Proofs.Wasm.Component.DWiring.Chatter

/-!
# Handlers that always call: infinite plays of `atSizes`

`narrowH k` answers every question by exactly one call, so it makes at least
one move below per move above, up to one (`count_allCall`). Hence in an
infinite interaction with `narrowH k` on top, the strategy below moves forever
(`unbounded_s`); with `unbounded_t` (`widenH n` below), every infinite play of
`atSizes n k σ` comes from an infinite play of `σ` (`inf_atSizes_sub`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.DWiring

open Silmaril.Games Silmaril.Wasm.Component

universe u

variable {E F : Sig.{u}}

/-- A handler answering every question by exactly one call. -/
def AllCall (h : Handler E F) : Prop :=
  ∀ q, ∃ m k, h q = .call m k ∧ ∀ n, ∃ r, k n = .pure r

/-- The counting invariant of a handler that always calls. -/
def Inv₂ (h : Handler E F) : h.toReduction.State → ℕ → ℕ → Prop
  | .idle, a, b => b ≤ a
  | .run _ c, a, b => (b ≤ a + 1 ∧ ∃ m k, c = .call m k ∧ ∀ n, ∃ r, k n = .pure r) ∨
      (b + 1 ≤ a ∧ ∃ r, c = .pure r)
  | .wait _ _ k, a, b => b ≤ a ∧ ∀ n, ∃ r, k n = .pure r

theorem inv₂_le {h : Handler E F} {x : h.toReduction.State} {a b : ℕ} (hx : Inv₂ h x a b) :
    b ≤ a + 1 := by
  cases x with
  | idle => exact Nat.le_succ_of_le hx
  | run q c => rcases hx with ⟨hx, -⟩ | ⟨hx, -⟩ <;> omega
  | wait q m k => exact Nat.le_succ_of_le hx.1

theorem inv₂_step {h : Handler E F} (hh : AllCall h) {x y : h.toReduction.State}
    {o : Option (Move E F)} (hs : h.toReduction.toLTS.step x o y) {a b : ℕ}
    (hx : Inv₂ h x a b) : Inv₂ h y (a + nL o.toList) (b + nR o.toList) := by
  cases hs with
  | ask q =>
    simp only [Option.toList_some, nL_inr, nL_nil, nR_inr, nR_nil, Inv₂]
    exact .inl ⟨by simp only [Inv₂] at hx; omega, hh q⟩
  | tau hc => exact hc.elim
  | call hc =>
    simp only [Option.toList_some, nL_inl, nL_nil, nR_inl, nR_nil, Inv₂]
    change _ = Prog.call _ _ at hc
    subst hc
    rcases hx with ⟨hab, m', k', hc, hk⟩ | ⟨-, r, hr⟩
    · cases hc
      exact ⟨by omega, hk⟩
    · cases hr
  | resume q m k n =>
    simp only [Option.toList_some, nL_inl, nL_nil, nR_inl, nR_nil, Inv₂]
    exact .inr ⟨by simp only [Inv₂] at hx; omega, hx.2 n⟩
  | ret hc =>
    simp only [Option.toList_some, nL_inr, nL_nil, nR_inr, nR_nil, Inv₂]
    change _ = Prog.pure _ at hc
    subst hc
    rcases hx with ⟨-, m, k, hc, -⟩ | ⟨hab, -⟩
    · cases hc
    · omega

theorem inv₂_run {h : Handler E F} (hh : AllCall h) : ∀ {x y : h.toReduction.State}
    {s : List (Move E F)}, h.toReduction.toLTS.Run x s y →
    ∀ {a b : ℕ}, Inv₂ h x a b → Inv₂ h y (a + nL s) (b + nR s)
  | _, _, _, .nil _, _, _, hx => by simpa using hx
  | _, _, _, .tau hs hr, _, _, hx => by
    simpa using inv₂_run hh hr (by simpa using inv₂_step hh hs hx)
  | _, _, _, .vis (o := o) (s := s) hs hr, _, _, hx => by
    have := inv₂_run hh hr (inv₂_step hh hs hx)
    cases o <;> simp only [Option.toList_some, nL_inl, nL_inr, nR_inl, nR_inr, nL_nil,
      nR_nil] at this ⊢ <;> (convert this using 1; omega)

/-- **A handler that always calls makes at least one move below per move above**,
up to one. -/
theorem count_allCall {h : Handler E F} (hh : AllCall h) {t : List (Move E F)}
    (ht : t ∈ Strategy.ofHandler h) : nR t ≤ nL t + 1 := by
  obtain ⟨y, hr⟩ := Strategy.mem_ofHandler.1 ht
  have := inv₂_le (inv₂_run hh hr (a := 0) (b := 0) (show 0 ≤ 0 from le_rfl))
  simpa using this

theorem allCall_narrowH (k : Nat) : AllCall (narrowH k) :=
  fun _ => ⟨_, _, rfl, fun r => ⟨r, rfl⟩⟩

/-- With a handler that always calls on top, the strategy below moves forever
when the visible part does. -/
theorem unbounded_s {X : Sig.{u}} {h : Handler E F} (hh : AllCall h) {δ : DStrategy X E}
    (i : DStrategy.InfInteraction δ (DStrategy.ofHandler h)) (hp : i.p.Unbounded) :
    i.s.Unbounded := by
  intro k
  by_contra hk
  push Not at hk
  obtain ⟨n, hn⟩ := hp (2 * k + 2)
  have hz := zip_counts (i.zip n)
  have hc := count_allCall hh (i.mem_t n)
  have hp := length_eq (i.p n)
  have hs := length_eq (i.s n)
  have ht := length_eq (i.t n)
  have := hk n
  omega

/-- **Infinite plays of `atSizes` come from infinite plays of `σ`.** -/
theorem inf_atSizes_sub {n k : Nat} {σ : DStrategy sigU sigU}
    {I : Set (List (Move (sigN n) (sigN k)))}
    (hI : I ∈ (DStrategy.atSizes n k σ).inf) :
    ∃ i : DStrategy.InfInteraction ((DStrategy.ofHandler (widenH n)).comp σ)
        (DStrategy.ofHandler (narrowH k)),
      I = i.p.lim ∧ ∃ j : DStrategy.InfInteraction (DStrategy.ofHandler (widenH n)) σ,
        i.s.lim = j.p.lim ∧ j.t.Unbounded ∧ j.t.lim ∈ σ.inf := by
  obtain ⟨i, hu, rfl⟩ := hI
  obtain ⟨j, hju, hj⟩ := i.lim_s (unbounded_s (allCall_narrowH k) i hu)
  have ht := unbounded_t (oneCall_widenH n) j hju
  exact ⟨i, rfl, j, hj, ht, j.lim_t ht⟩

/-- Divergence of `atSizes`. -/
theorem div_atSizes {n k : Nat} {σ : DStrategy sigU sigU} :
    (DStrategy.atSizes n k σ).div =
      {p | ∃ s t, Zip s t p ∧ t ∈ Strategy.ofHandler (narrowH k) ∧
      ((∃ u v, Zip u v s ∧ u ∈ Strategy.ofHandler (widenH n) ∧ v ∈ σ.div) ∨
        ∃ i : DStrategy.InfInteraction (DStrategy.ofHandler (widenH n)) σ,
          ∀ m, i.p m = s)} := by
  rw [DStrategy.atSizes, comp_ofHandler_div (oneCall_narrowH k), ofHandler_comp_div]
  ext p
  exact ⟨fun ⟨s, t, hz, hs, ht⟩ => ⟨s, t, hz, ht, hs⟩,
    fun ⟨s, t, hz, ht, hs⟩ => ⟨s, t, hz, hs, ht⟩⟩

/-- Without trap chatter, `atSizes` diverges exactly where `σ` does. -/
theorem div_atSizes_of_noTrap {n k : Nat} {σ : DStrategy sigU sigU}
    (hσ : ∀ I ∈ σ.inf, ¬ EventuallyTrap n I) :
    (DStrategy.atSizes n k σ).div = {p | ∃ s t u v, Zip u v s ∧ Zip s t p ∧
      u ∈ Strategy.ofHandler (widenH n) ∧ t ∈ Strategy.ofHandler (narrowH k) ∧
        v ∈ σ.div} := by
  rw [div_atSizes]
  ext p
  constructor
  · rintro ⟨s, t, hz, ht, ⟨u, v, hz', hu, hv⟩ | ⟨i, hi⟩⟩
    · exact ⟨s, t, u, v, hz', hz, hu, ht, hv⟩
    · obtain ⟨h₁, h₂⟩ := chatter_widenH i hi
      exact (hσ _ h₁ h₂).elim
  · rintro ⟨s, t, u, v, hz', hz, hu, ht, hv⟩
    exact ⟨s, t, hz, ht, .inl ⟨u, v, hz', hu, hv⟩⟩

end Silmaril.Proofs.Wasm.Component.DWiring

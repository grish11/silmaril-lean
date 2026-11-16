module

public import Silmaril.Games.DivCompChatter.Defs
public import Silmaril.Games.DivComp.Thms

/-!
# Hidden chatter of a composite: proofs

Proofs for `Silmaril.Games.DivCompChatter.Thms`.

* With the visible part fixed, the two sides of an interaction differ in length
  by a fixed amount (`zip_length`), so when the total length grows, both sides
  grow (`lt_of_zip`).
* An unbounded chain inside an infinite play converges to it (`lim_eq_of_mem`).
* From `Chatter I J p`, choosing ever longer interacting pairs gives increasing
  chains inside `I` and `J` (`pairs`), hence an infinite interaction
  (`interaction`).
-/

public section

namespace Silmaril.Proofs.Games.DivCompChatter

open Silmaril.Games Silmaril.Games.DStrategy

universe u v w

section
variable {α : Type u} {β : Type v} {γ : Type w}

/-- With the visible part fixed, the two sides of an interaction differ in
length by a fixed amount. -/
theorem zip_length {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {p : List (α ⊕ γ)} (h : Zip s t p) :
    s.length + (p.filterMap Sum.getRight?).length =
      t.length + (p.filterMap Sum.getLeft?).length := by
  induction h with
  | nil => rfl
  | left a _ ih => simp only [List.length_cons, List.filterMap_cons, Sum.getLeft?_inl,
      Sum.getRight?_inl]; omega
  | right c _ ih => simp only [List.length_cons, List.filterMap_cons, Sum.getLeft?_inr,
      Sum.getRight?_inr]; omega
  | sync b _ ih => simp only [List.length_cons]; omega

/-- With the visible part fixed, a longer interaction is longer on both sides. -/
theorem lt_of_zip {s s' : List (α ⊕ β)} {t t' : List (β ⊕ γ)} {p : List (α ⊕ γ)}
    (h : Zip s t p) (h' : Zip s' t' p) (hl : s.length + t.length < s'.length + t'.length) :
    s.length < s'.length ∧ t.length < t'.length := by
  have := zip_length h
  have := zip_length h'
  omega

/-- An unbounded chain inside an infinite play converges to it. -/
theorem lim_eq_of_mem {I : Set (List α)} (hI : IsInfPlay I) {c : Chain α} (hc : ∀ n, c n ∈ I)
    (hu : c.Unbounded) : c.lim = I := by
  ext q
  refine ⟨fun ⟨n, hq⟩ => hI.of_prefix (hc n) hq, fun hq => ?_⟩
  obtain ⟨n, hn⟩ := hu q.length
  exact ⟨n, hI.prefix_of_length_le hq (hc n) hn⟩

/-- Chatter makes the right trace arbitrarily long. -/
theorem unbounded_right {I : Set (List (α ⊕ β))} {J : Set (List (β ⊕ γ))}
    {p : List (α ⊕ γ)} (h : Chatter I J p) : ∀ k, ∃ t ∈ J, k ≤ t.length := by
  intro k
  obtain ⟨s, -, t, ht, hk, hz⟩ :=
    h (2 * k + (p.filterMap Sum.getLeft?).length + (p.filterMap Sum.getRight?).length)
  have := zip_length hz
  exact ⟨t, ht, by omega⟩

/-- Chatter makes the left trace arbitrarily long. -/
theorem unbounded_left {I : Set (List (α ⊕ β))} {J : Set (List (β ⊕ γ))}
    {p : List (α ⊕ γ)} (h : Chatter I J p) : ∀ k, ∃ s ∈ I, k ≤ s.length := by
  intro k
  obtain ⟨s, hs, t, -, hk, hz⟩ :=
    h (2 * k + (p.filterMap Sum.getLeft?).length + (p.filterMap Sum.getRight?).length)
  have := zip_length hz
  exact ⟨s, hs, by omega⟩

/-- A chain whose limit has arbitrarily long members is unbounded. -/
theorem unbounded_of_lim {c : Chain α} (h : ∀ k, ∃ t ∈ c.lim, k ≤ t.length) : c.Unbounded := by
  intro k
  obtain ⟨t, ⟨n, hn⟩, hk⟩ := h k
  exact ⟨n, hk.trans hn.length_le⟩

/-- Chatter of two infinite plays: increasing chains of interacting pairs inside
them, whose total length grows by at least one at each step. -/
theorem pairs {I : Set (List (α ⊕ β))} {J : Set (List (β ⊕ γ))} {p : List (α ⊕ γ)}
    (hI : IsInfPlay I) (hJ : IsInfPlay J) (h : Chatter I J p) :
    ∃ (s : Chain (α ⊕ β)) (t : Chain (β ⊕ γ)), (∀ n, s n ∈ I) ∧ (∀ n, t n ∈ J) ∧
      (∀ n, Zip (s n) (t n) p) ∧ s.Mono ∧ t.Mono ∧
      (∀ n, n ≤ (s n).length + (t n).length) := by
  have h' : ∀ k, ∃ q : List (α ⊕ β) × List (β ⊕ γ),
      q.1 ∈ I ∧ q.2 ∈ J ∧ k ≤ q.1.length + q.2.length ∧ Zip q.1 q.2 p := fun k => by
    obtain ⟨s, hs, t, ht, hk, hz⟩ := h k
    exact ⟨(s, t), hs, ht, hk, hz⟩
  choose f hf using h'
  let c : ℕ → List (α ⊕ β) × List (β ⊕ γ) := fun n =>
    Nat.rec (f 0) (fun _ q => f (q.1.length + q.2.length + 1)) n
  have hc : ∀ n, (c n).1 ∈ I ∧ (c n).2 ∈ J ∧ Zip (c n).1 (c n).2 p := by
    intro n
    cases n with
    | zero => exact ⟨(hf 0).1, (hf 0).2.1, (hf 0).2.2.2⟩
    | succ n =>
      have := hf ((c n).1.length + (c n).2.length + 1)
      exact ⟨this.1, this.2.1, this.2.2.2⟩
  have hstep : ∀ n, (c n).1.length + (c n).2.length + 1 ≤
      (c (n + 1)).1.length + (c (n + 1)).2.length := fun n =>
    (hf ((c n).1.length + (c n).2.length + 1)).2.2.1
  have hlt : ∀ n, (c n).1.length < (c (n + 1)).1.length ∧
      (c n).2.length < (c (n + 1)).2.length := fun n =>
    lt_of_zip (hc n).2.2 (hc (n + 1)).2.2 (hstep n)
  have hlen : ∀ n, n ≤ (c n).1.length + (c n).2.length := by
    intro n
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih => have := hstep n; omega
  exact ⟨fun n => (c n).1, fun n => (c n).2, fun n => (hc n).1, fun n => (hc n).2.1,
    fun n => (hc n).2.2, fun n => hI.prefix_of_length_le (hc n).1 (hc (n + 1)).1 (hlt n).1.le,
    fun n => hJ.prefix_of_length_le (hc n).2.1 (hc (n + 1)).2.1 (hlt n).2.le, hlen⟩

end

variable {E F G H : Sig.{u}}

/-- **Chatter gives an infinite interaction.** -/
theorem interaction {σ : DStrategy E F} {τ : DStrategy F G} {p : List (Move E G)}
    {I : Set (List (Move E F))} (hI : I ∈ σ.inf) {J : Set (List (Move F G))} (hJ : J ∈ τ.inf)
    (h : Chatter I J p) : ∃ i : InfInteraction σ τ, ∀ m, i.p m = p := by
  obtain ⟨s, t, hs, ht, hz, ms, mt, hl⟩ := pairs (σ.inf_isInf hI) (τ.inf_isInf hJ) h
  have lens : ∀ n, (s n).length + (p.filterMap Sum.getRight?).length =
      (t n).length + (p.filterMap Sum.getLeft?).length := fun n => zip_length (hz n)
  have us : s.Unbounded := fun k => by
    let n := 2 * k + (p.filterMap Sum.getLeft?).length + (p.filterMap Sum.getRight?).length
    refine ⟨n, ?_⟩
    have := lens n
    have := hl n
    omega
  have ut : t.Unbounded := fun k => by
    let n := 2 * k + (p.filterMap Sum.getLeft?).length + (p.filterMap Sum.getRight?).length
    refine ⟨n, ?_⟩
    have := lens n
    have := hl n
    omega
  refine ⟨⟨s, t, fun _ => p, hz, fun n => σ.inf_sub hI (hs n), fun n => τ.inf_sub hJ (ht n),
    ms, mt, fun _ => List.prefix_refl _, fun k => ⟨k, hl k⟩, fun _ => ?_, fun _ => ?_⟩,
    fun _ => rfl⟩
  · rw [lim_eq_of_mem (σ.inf_isInf hI) hs us]; exact hI
  · rw [lim_eq_of_mem (τ.inf_isInf hJ) ht ut]; exact hJ

/-- **Hidden chatter, characterised by the components' infinite plays.** -/
theorem chatter_iff {σ : DStrategy E F} {τ : DStrategy F G} {p : List (Move E G)} :
    (∃ i : InfInteraction σ τ, ∀ m, i.p m = p) ↔ ∃ I ∈ σ.inf, ∃ J ∈ τ.inf, Chatter I J p := by
  refine ⟨fun ⟨i, hp⟩ => ?_, fun ⟨I, hI, J, hJ, h⟩ => interaction hI hJ h⟩
  obtain ⟨-, -, hsI, htJ⟩ := i.chatter_inf hp
  refine ⟨_, hsI, _, htJ, fun k => ?_⟩
  obtain ⟨n, hn⟩ := i.unbounded k
  exact ⟨_, Chain.mem_lim_self _ n, _, Chain.mem_lim_self _ n, hn, hp n ▸ i.zip n⟩

/-- Hidden chatter with a composite on the right. -/
theorem chatter_comp_right_iff {σ : DStrategy E F} {τ : DStrategy F G} {ρ : DStrategy G H}
    {p : List (Move E H)} :
    (∃ i : InfInteraction σ (τ.comp ρ), ∀ m, i.p m = p) ↔
      ∃ I ∈ σ.inf, ∃ j : InfInteraction τ ρ, Chatter I j.p.lim p := by
  rw [chatter_iff]
  constructor
  · rintro ⟨I, hI, J, hJ, h⟩
    obtain ⟨j, -, rfl⟩ := mem_inf_comp.1 hJ
    exact ⟨I, hI, j, h⟩
  · rintro ⟨I, hI, j, h⟩
    exact ⟨I, hI, _, mem_inf_comp.2 ⟨j, unbounded_of_lim (unbounded_right h), rfl⟩, h⟩

/-- Hidden chatter with a composite on the left. -/
theorem chatter_comp_left_iff {σ : DStrategy E F} {τ : DStrategy F G} {ρ : DStrategy G H}
    {p : List (Move E H)} :
    (∃ i : InfInteraction (σ.comp τ) ρ, ∀ m, i.p m = p) ↔
      ∃ j : InfInteraction σ τ, ∃ K ∈ ρ.inf, Chatter j.p.lim K p := by
  rw [chatter_iff]
  constructor
  · rintro ⟨I, hI, K, hK, h⟩
    obtain ⟨j, -, rfl⟩ := mem_inf_comp.1 hI
    exact ⟨j, K, hK, h⟩
  · rintro ⟨j, K, hK, h⟩
    exact ⟨_, mem_inf_comp.2 ⟨j, unbounded_of_lim (unbounded_left h), rfl⟩, K, hK, h⟩

/-- Hidden chatter with a composite on the right whose upper component makes
the lower one move whenever the visible play grows. -/
theorem chatter_comp_right_iff_of_moves {σ : DStrategy E F} {τ : DStrategy F G}
    {ρ : DStrategy G H} (hρ : ∀ j : InfInteraction τ ρ, j.p.Unbounded → j.s.Unbounded)
    {p : List (Move E H)} :
    (∃ i : InfInteraction σ (τ.comp ρ), ∀ m, i.p m = p) ↔
      ∃ I ∈ σ.inf, ∃ j : InfInteraction τ ρ, j.s.Unbounded ∧ j.s.lim ∈ τ.inf ∧
        Chatter I j.p.lim p := by
  rw [chatter_comp_right_iff]
  constructor
  · rintro ⟨I, hI, j, h⟩
    have hs := hρ j (unbounded_of_lim (unbounded_right h))
    exact ⟨I, hI, j, hs, j.lim_s hs, h⟩
  · rintro ⟨I, hI, j, -, -, h⟩
    exact ⟨I, hI, j, h⟩

end Silmaril.Proofs.Games.DivCompChatter

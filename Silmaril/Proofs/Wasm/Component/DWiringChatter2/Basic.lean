module

public import Silmaril.Games.DivCompChatter.Defs
public import Silmaril.Games.Div.Thms
public import Silmaril.Games.Zip.Thms

/-!
# Chatter is eventually pure synchronisation

Two infinite traces `I` and `J` that chatter after `p` (`Chatter I J p`) have
only finitely many outer events: every member of `I` interacting with a member
of `J` with visible part `p` has at most `p.length` of them, and members of an
infinite trace are prefixes of longer ones. So after some aligned pair
`s₀ ∈ I`, `c₀ ∈ J` interacting with visible part `p`, both traces consist of
the same shared events `w`, synchronised one by one (`chatter_tail_iff`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.DWiringChatter2

open Silmaril.Games

universe u v w

section Counts

variable {α : Type u} {β : Type v} {γ : Type w}

/-- The number of left events of a trace. -/
def cntL (s : List (α ⊕ β)) : ℕ := (s.filterMap Sum.getLeft?).length

/-- The number of right events of a trace. -/
def cntR (s : List (α ⊕ β)) : ℕ := (s.filterMap Sum.getRight?).length

@[simp] theorem cntL_nil : cntL ([] : List (α ⊕ β)) = 0 := rfl
@[simp] theorem cntR_nil : cntR ([] : List (α ⊕ β)) = 0 := rfl
@[simp] theorem cntL_cons_inl (a : α) (s : List (α ⊕ β)) : cntL (.inl a :: s) = cntL s + 1 :=
  rfl
@[simp] theorem cntL_cons_inr (b : β) (s : List (α ⊕ β)) : cntL (.inr b :: s) = cntL s :=
  rfl
@[simp] theorem cntR_cons_inl (a : α) (s : List (α ⊕ β)) : cntR (.inl a :: s) = cntR s :=
  rfl
@[simp] theorem cntR_cons_inr (b : β) (s : List (α ⊕ β)) : cntR (.inr b :: s) = cntR s + 1 :=
  rfl

@[simp] theorem cntL_append (s t : List (α ⊕ β)) : cntL (s ++ t) = cntL s + cntL t := by
  simp [cntL]
@[simp] theorem cntR_append (s t : List (α ⊕ β)) : cntR (s ++ t) = cntR s + cntR t := by
  simp [cntR]

@[simp] theorem cntL_map_inl (w : List α) : cntL (w.map (Sum.inl (β := β))) = w.length := by
  induction w <;> simp_all
@[simp] theorem cntR_map_inl (w : List α) : cntR (w.map (Sum.inl (β := β))) = 0 := by
  induction w <;> simp_all
@[simp] theorem cntL_map_inr (w : List β) : cntL (w.map (Sum.inr (α := α))) = 0 := by
  induction w <;> simp_all
@[simp] theorem cntR_map_inr (w : List β) : cntR (w.map (Sum.inr (α := α))) = w.length := by
  induction w <;> simp_all

theorem length_eq_cnt (s : List (α ⊕ β)) : s.length = cntL s + cntR s := by
  induction s with
  | nil => rfl
  | cons x s ih => rcases x with a | b <;> simp [ih] <;> omega

theorem cntL_mono {s t : List (α ⊕ β)} (h : s <+: t) : cntL s ≤ cntL t := by
  obtain ⟨u, rfl⟩ := h
  simp

theorem cntR_mono {s t : List (α ⊕ β)} (h : s <+: t) : cntR s ≤ cntR t := by
  obtain ⟨u, rfl⟩ := h
  simp

/-- A trace without left events is a list of right events. -/
theorem eq_map_inr_of_cntL {u : List (α ⊕ β)} (h : cntL u = 0) :
    u = (u.filterMap Sum.getRight?).map Sum.inr := by
  induction u with
  | nil => rfl
  | cons x u ih =>
    rcases x with a | b
    · simp at h
    · rw [cntL_cons_inr] at h
      exact congrArg (Sum.inr b :: ·) (ih h)

/-- A trace without right events is a list of left events. -/
theorem eq_map_inl_of_cntR {u : List (α ⊕ β)} (h : cntR u = 0) :
    u = (u.filterMap Sum.getLeft?).map Sum.inl := by
  induction u with
  | nil => rfl
  | cons x u ih =>
    rcases x with a | b
    · rw [cntR_cons_inl] at h
      exact congrArg (Sum.inl a :: ·) (ih h)
    · simp at h

/-- An extension adding no left event adds right events only. -/
theorem eq_append_inr {s t : List (α ⊕ β)} (h : s <+: t) (hc : cntL t ≤ cntL s) :
    ∃ w : List β, t = s ++ w.map Sum.inr := by
  obtain ⟨u, rfl⟩ := h
  simp only [cntL_append] at hc
  exact ⟨_, congrArg (s ++ ·) (eq_map_inr_of_cntL (by omega))⟩

/-- An extension adding no right event adds left events only. -/
theorem eq_append_inl {s t : List (α ⊕ β)} (h : s <+: t) (hc : cntR t ≤ cntR s) :
    ∃ w : List α, t = s ++ w.map Sum.inl := by
  obtain ⟨u, rfl⟩ := h
  simp only [cntR_append] at hc
  exact ⟨_, congrArg (s ++ ·) (eq_map_inl_of_cntR (by omega))⟩

/-- Shared events are synchronised one for one; outer events are visible. -/
theorem zip_counts {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {p : List (α ⊕ γ)} (h : Zip s t p) :
    cntR s = cntL t ∧ cntL s + cntR t = p.length := by
  induction h with
  | nil => exact ⟨rfl, rfl⟩
  | left a _ ih => simp only [cntL_cons_inl, cntR_cons_inl, List.length_cons]; omega
  | right c _ ih => simp only [cntL_cons_inr, cntR_cons_inr, List.length_cons]; omega
  | sync b _ ih => simp only [cntR_cons_inr, cntL_cons_inl, cntL_cons_inr, cntR_cons_inl]; omega

/-- The lengths of two interacting traces differ by at most the visible part. -/
theorem zip_length {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {p : List (α ⊕ γ)} (h : Zip s t p) :
    t.length ≤ s.length + p.length ∧ s.length ≤ t.length + p.length := by
  have := zip_counts h
  have := length_eq_cnt s
  have := length_eq_cnt t
  omega

end Counts

/-! ## Appending and removing synchronised events -/

section Zip

variable {α : Type u} {β : Type v} {γ : Type w}

/-- Append synchronised events. -/
theorem zip_append_sync {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {p : List (α ⊕ γ)}
    (h : Zip s t p) (w : List β) : Zip (s ++ w.map .inr) (t ++ w.map .inl) p := by
  induction h with
  | nil =>
    induction w with
    | nil => exact .nil
    | cons b w ih => exact .sync b ih
  | left a _ ih => exact .left a ih
  | right c _ ih => exact .right c ih
  | sync b _ ih => exact .sync b ih

/-- Append visible events of the left trace. -/
theorem zip_append_inl {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {p : List (α ⊕ γ)}
    (h : Zip s t p) (w : List α) : Zip (s ++ w.map .inl) t (p ++ w.map .inl) := by
  induction h with
  | nil =>
    induction w with
    | nil => exact .nil
    | cons a w ih => exact .left a ih
  | left a _ ih => exact .left a ih
  | right c _ ih => exact .right c ih
  | sync b _ ih => exact .sync b ih

theorem not_inl_mem_map_inr {a : α} {cs : List γ} : (.inl a : α ⊕ γ) ∉ cs.map .inr := by
  simp

theorem not_inr_mem_map_inl {c : γ} {as : List α} : (.inr c : α ⊕ γ) ∉ as.map .inl := by
  simp

/-- Remove a last synchronised event. -/
theorem zip_strip1 {b b' : β} : ∀ {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {p : List (α ⊕ γ)},
    Zip (s ++ [.inr b]) (t ++ [.inl b']) p → b = b' ∧ Zip s t p := by
  intro s t p h
  generalize hx : s ++ [.inr b] = x at h
  generalize hy : t ++ [.inl b'] = y at h
  induction h generalizing s t with
  | nil => simp at hx
  | left a _ ih =>
    cases s with
    | nil => simp at hx
    | cons x s =>
      simp only [List.cons_append, List.cons.injEq] at hx
      obtain ⟨rfl, hx⟩ := hx
      obtain ⟨hb, h⟩ := ih hx hy
      exact ⟨hb, .left a h⟩
  | right c _ ih =>
    cases t with
    | nil => simp at hy
    | cons x t =>
      simp only [List.cons_append, List.cons.injEq] at hy
      obtain ⟨rfl, hy⟩ := hy
      obtain ⟨hb, h⟩ := ih hx hy
      exact ⟨hb, .right c h⟩
  | @sync s' t' p' b₀ h ih =>
    cases s with
    | nil =>
      simp only [List.nil_append, List.cons.injEq, Sum.inr.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      cases t with
      | nil =>
        simp only [List.nil_append, List.cons.injEq, Sum.inl.injEq] at hy
        obtain ⟨rfl, rfl⟩ := hy
        exact ⟨rfl, h⟩
      | cons x t =>
        simp only [List.cons_append, List.cons.injEq] at hy
        obtain ⟨rfl, rfl⟩ := hy
        obtain ⟨cs, hcs, -⟩ := Zip.nil_left_iff.1 h
        exact absurd (hcs ▸ List.mem_append_right t (List.mem_singleton_self _))
          not_inl_mem_map_inr
    | cons x s =>
      simp only [List.cons_append, List.cons.injEq] at hx
      obtain ⟨rfl, hx⟩ := hx
      cases t with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at hy
        obtain ⟨-, rfl⟩ := hy
        obtain ⟨as, has, -⟩ := Zip.nil_right_iff.1 (hx ▸ h)
        exact absurd (has ▸ List.mem_append_right s (List.mem_singleton_self _))
          not_inr_mem_map_inl
      | cons y t =>
        simp only [List.cons_append, List.cons.injEq] at hy
        obtain ⟨rfl, hy⟩ := hy
        obtain ⟨hb, h⟩ := ih hx hy
        exact ⟨hb, .sync b₀ h⟩

/-- Remove last synchronised events, as many on both sides. -/
theorem zip_strip {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {p : List (α ⊕ γ)} (ws : List β) :
    ∀ {wt : List β}, ws.length = wt.length →
      Zip (s ++ ws.map .inr) (t ++ wt.map .inl) p → ws = wt ∧ Zip s t p := by
  generalize hn : ws.length = n
  induction n generalizing ws with
  | zero =>
    intro wt hl h
    rw [List.length_eq_zero_iff] at hn
    rw [eq_comm, List.length_eq_zero_iff] at hl
    subst hn hl
    simpa using h
  | succ n ih =>
    intro wt hl h
    rcases List.eq_nil_or_concat ws with rfl | ⟨ws, b, rfl⟩
    · simp at hn
    rcases List.eq_nil_or_concat wt with rfl | ⟨wt, b', rfl⟩
    · simp [← hn] at hl
    simp only [List.concat_eq_append] at hn hl h ⊢
    simp only [List.map_append, List.map_cons, List.map_nil, ← List.append_assoc] at h
    obtain ⟨hb, h₁⟩ := zip_strip1 h
    subst hb
    obtain ⟨hw, h₂⟩ := ih ws (by simpa using hn) (by simpa using hl) h₁
    exact ⟨hw ▸ rfl, h₂⟩

end Zip

/-! ## Infinite traces -/

section Inf

variable {α : Type u}

/-- An unbounded chain of members of an infinite trace converges to it. -/
theorem lim_eq_of_mem {I : Set (List α)} (hI : IsInfPlay I) {c : Chain α}
    (hc : ∀ m, c m ∈ I) (hu : c.Unbounded) : c.lim = I := by
  ext q
  constructor
  · rintro ⟨m, hq⟩
    exact hI.of_prefix (hc m) hq
  · intro hq
    obtain ⟨m, hm⟩ := hu q.length
    exact ⟨m, hI.prefix_of_length_le hq (hc m) hm⟩

theorem nil_mem {I : Set (List α)} (hI : IsInfPlay I) : [] ∈ I := by
  obtain ⟨s, hs, -⟩ := hI.unbounded 0
  exact hI.of_prefix hs List.nil_prefix

/-- A bounded measure attains its maximum on a nonempty set. -/
theorem exists_max {β : Type v} {S : Set β} {x₀ : β} (h₀ : x₀ ∈ S) (f : β → ℕ) (B : ℕ)
    (hB : ∀ x ∈ S, f x ≤ B) : ∃ x ∈ S, ∀ y ∈ S, f y ≤ f x := by
  by_contra hc
  simp only [not_exists, not_and, not_forall, not_le] at hc
  have : ∀ n, ∃ x ∈ S, n ≤ f x := by
    intro n
    induction n with
    | zero => exact ⟨x₀, h₀, Nat.zero_le _⟩
    | succ n ih =>
      obtain ⟨x, hx, hn⟩ := ih
      obtain ⟨y, hy, hxy⟩ := hc x hx
      exact ⟨y, hy, by omega⟩
  obtain ⟨x, hx, hn⟩ := this (B + 1)
  have := hB x hx
  omega

end Inf

/-! ## Chatter -/

section Chatter

variable {α : Type u} {β : Type v} {γ : Type w}

/-- **Chatter is eventually pure synchronisation.** Two infinite traces chatter
after `p` iff, after an aligned pair `s₀ ∈ I`, `c₀ ∈ J` interacting with
visible part `p`, both continue by the same arbitrarily long shared events. -/
theorem chatter_tail_iff {I : Set (List (α ⊕ β))} {J : Set (List (β ⊕ γ))}
    (hI : IsInfPlay I) (hJ : IsInfPlay J) {p : List (α ⊕ γ)} :
    Chatter I J p ↔ ∃ s₀ ∈ I, ∃ c₀ ∈ J, Zip s₀ c₀ p ∧
      ∀ k, ∃ w : List β, k ≤ w.length ∧ s₀ ++ w.map .inr ∈ I ∧ c₀ ++ w.map .inl ∈ J := by
  constructor
  · intro hC
    have hlong : ∀ n, ∃ s ∈ I, ∃ c ∈ J, n ≤ s.length ∧ n ≤ c.length ∧ Zip s c p := by
      intro n
      obtain ⟨s, hs, c, hc, hk, hz⟩ := hC (2 * n + p.length)
      have := zip_length hz
      exact ⟨s, hs, c, hc, by omega, by omega, hz⟩
    have hbI : ∀ s ∈ I, cntL s ≤ p.length := by
      intro s hs
      obtain ⟨s', hs', c', -, hl, -, hz⟩ := hlong s.length
      exact (cntL_mono (hI.prefix_of_length_le hs hs' hl)).trans
        (Nat.le.intro (zip_counts hz).2)
    have hbJ : ∀ c ∈ J, cntR c ≤ p.length := by
      intro c hc
      obtain ⟨s', -, c', hc', -, hl, hz⟩ := hlong c.length
      exact (cntR_mono (hJ.prefix_of_length_le hc hc' hl)).trans
        (by have := (zip_counts hz).2; omega)
    obtain ⟨sm, hsm, hmax_s⟩ := exists_max (nil_mem hI) cntL _ hbI
    obtain ⟨cm, hcm, hmax_c⟩ := exists_max (nil_mem hJ) cntR _ hbJ
    obtain ⟨s₁, hs₁, c₁, hc₁, h₁, h₂, hz₁⟩ := hlong (sm.length + cm.length)
    have hext_s : ∀ s ∈ I, s₁.length ≤ s.length → ∃ w : List β, s = s₁ ++ w.map .inr := by
      intro s hs hl
      refine eq_append_inr (hI.prefix_of_length_le hs₁ hs hl) ?_
      exact (hmax_s s hs).trans
        (cntL_mono (hI.prefix_of_length_le hsm hs₁ (by omega)))
    have hext_c : ∀ c ∈ J, c₁.length ≤ c.length → ∃ w : List β, c = c₁ ++ w.map .inl := by
      intro c hc hl
      refine eq_append_inl (hJ.prefix_of_length_le hc₁ hc hl) ?_
      exact (hmax_c c hc).trans
        (cntR_mono (hJ.prefix_of_length_le hcm hc₁ (by omega)))
    refine ⟨s₁, hs₁, c₁, hc₁, hz₁, fun k => ?_⟩
    obtain ⟨s, hs, c, hc, h₃, h₄, hz⟩ := hlong (s₁.length + c₁.length + k)
    obtain ⟨ws, rfl⟩ := hext_s s hs (by omega)
    obtain ⟨wc, rfl⟩ := hext_c c hc (by omega)
    have e₁ := (zip_counts hz).1
    have e₂ := (zip_counts hz₁).1
    simp only [cntR_append, cntR_map_inr, cntL_append, cntL_map_inl] at e₁
    obtain ⟨rfl, -⟩ := zip_strip ws (by omega) hz
    refine ⟨ws, ?_, hs, hc⟩
    simp only [List.length_append, List.length_map] at h₃
    omega
  · rintro ⟨s₀, -, c₀, -, hz, ht⟩ k
    obtain ⟨w, hk, hs, hc⟩ := ht k
    exact ⟨_, hs, _, hc, by simp only [List.length_append, List.length_map]; omega,
      zip_append_sync hz w⟩

end Chatter

end Silmaril.Proofs.Wasm.Component.DWiringChatter2

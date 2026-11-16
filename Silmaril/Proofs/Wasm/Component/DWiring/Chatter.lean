module

public import Silmaril.Proofs.Wasm.Component.DWiring.Trap

/-!
# Chatter below `widenH`: the infinite play

`chatter_widenH`: in an infinite interaction of `widenH n` with `σ` whose
visible part is constant, `σ` plays one of its infinite plays, and from some
point on every move of it is a trap event (`EventuallyTrap`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.DWiring

open Silmaril.Games Silmaril.Wasm.Component

universe u v w

/-- The hidden events of the two sides of an interaction agree. -/
theorem hidden_eq {α : Type u} {β : Type v} {γ : Type w} {s : List (α ⊕ β)}
    {t : List (β ⊕ γ)} {p : List (α ⊕ γ)} (h : Zip s t p) :
    s.filterMap Sum.getRight? = t.filterMap Sum.getLeft? := by
  induction h with
  | nil => rfl
  | left a _ ih => exact ih
  | right c _ ih => exact ih
  | sync b _ ih => simp [ih]

theorem filterMap_map_inr {α : Type u} {β : Type v} (l : List β) :
    (l.map (Sum.inr (α := α))).filterMap Sum.getRight? = l := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [ih]

theorem filterMap_map_inl {α : Type u} {β : Type v} (l : List α) :
    (l.map (Sum.inl (β := β))).filterMap Sum.getLeft? = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem eq_map_inr {α : Type u} {β : Type v} :
    ∀ {w : List (α ⊕ β)}, nL w = 0 → w = (w.filterMap Sum.getRight?).map Sum.inr
  | [], _ => rfl
  | .inl _ :: _, h => by simp at h
  | .inr b :: w, h => by simpa using eq_map_inr (w := w) (by simpa using h)

theorem eq_map_inl {α : Type u} {β : Type v} :
    ∀ {w : List (α ⊕ β)}, nR w = 0 → w = (w.filterMap Sum.getLeft?).map Sum.inl
  | [], _ => rfl
  | .inr _ :: _, h => by simp at h
  | .inl a :: w, h => by simpa using eq_map_inl (w := w) (by simpa using h)

theorem ext_inr {α : Type u} {β : Type v} {s s' : List (α ⊕ β)} (h : s <+: s')
    (hn : nL s' = nL s) : ∃ ws : List β, s' = s ++ ws.map Sum.inr := by
  obtain ⟨w, rfl⟩ := h
  refine ⟨_, congrArg (s ++ ·) (eq_map_inr ?_)⟩
  simp only [nL, List.filterMap_append, List.length_append] at hn
  simpa [nL] using hn

theorem ext_inl {α : Type u} {β : Type v} {s s' : List (α ⊕ β)} (h : s <+: s')
    (hn : nR s' = nR s) : ∃ vs : List α, s' = s ++ vs.map Sum.inl := by
  obtain ⟨w, rfl⟩ := h
  refine ⟨_, congrArg (s ++ ·) (eq_map_inl ?_)⟩
  simp only [nR, List.filterMap_append, List.length_append] at hn
  simpa [nR] using hn

variable {n : Nat} {G : Sig.{0}}

/-- Each stage of a chattering interaction: `σ` extends its first play by
hidden events only, and the handler runs these events from some state. -/
theorem stage {σ : DStrategy sigU G}
    (i : DStrategy.InfInteraction (DStrategy.ofHandler (widenH n)) σ) {p : List (Move (sigN n) G)}
    (hp : ∀ m, i.p m = p) (m : ℕ) :
    ∃ vs : List (Ev sigU), i.t m = i.t 0 ++ vs.map Sum.inl ∧ ∃ x y,
      (widenH n).toReduction.toLTS.Run x (vs.map Sum.inr) y := by
  have hz := zip_counts (i.zip m)
  have hz₀ := zip_counts (i.zip 0)
  rw [hp] at hz hz₀
  obtain ⟨ws, hws⟩ := ext_inr (i.mono_s.le (Nat.zero_le m)) (by omega)
  obtain ⟨vs, hvs⟩ := ext_inl (i.mono_t.le (Nat.zero_le m)) (by omega)
  refine ⟨vs, hvs, ?_⟩
  have he := hidden_eq (i.zip m)
  rw [hws, hvs, List.filterMap_append, List.filterMap_append, hidden_eq (i.zip 0)] at he
  rw [filterMap_map_inr, filterMap_map_inl] at he
  have hwv : ws = vs := List.append_cancel_left he
  subst hwv
  obtain ⟨y, hr⟩ := Strategy.mem_ofHandler.1 (i.mem_s m)
  rw [hws] at hr
  obtain ⟨x, -, hr⟩ := LTS.Run.of_append hr
  exact ⟨x, y, hr⟩

/-- **Chatter below `widenH`.** -/
theorem chatter_widenH {σ : DStrategy sigU G}
    (i : DStrategy.InfInteraction (DStrategy.ofHandler (widenH n)) σ) {p : List (Move (sigN n) G)}
    (hp : ∀ m, i.p m = p) : i.t.lim ∈ σ.inf ∧ EventuallyTrap n i.t.lim := by
  obtain ⟨-, ht, -, hlim⟩ := i.chatter_inf hp
  refine ⟨hlim, ?_⟩
  obtain ⟨N, -, hN⟩ := i.mono_t.unbounded_ge ht ((i.t 0).length + 1) 0
  obtain ⟨vN, hvN, -⟩ := stage i hp N
  refine ⟨i.t N, Chain.mem_lim_self _ N, fun u x hux => ?_⟩
  obtain ⟨M, hM⟩ := hux
  obtain ⟨M', hM', hlen⟩ := i.mono_t.unbounded_ge ht ((i.t N ++ u ++ [x]).length + 1) (M + N)
  have hpre : i.t N ++ u ++ [x] <+: i.t M' := hM.trans (i.mono_t.le (by omega))
  obtain ⟨r, hr⟩ := hpre
  obtain ⟨vs, hvs, x₀, y₀, hrun⟩ := stage i hp M'
  rw [← hr, hvN] at hvs
  simp only [List.append_assoc] at hvs
  have hvs' := List.append_cancel_left hvs
  -- `vs.map inl = vN.map inl ++ (u ++ [x] ++ r)`
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := List.map_eq_append_iff.1 hvs'.symm
  have ha₁ : a₁ = vN := List.map_injective_iff.2 Sum.inl_injective h₁
  subst ha₁
  obtain ⟨b₁, b₂, rfl, hu, h₃⟩ := List.map_eq_append_iff.1 h₂
  obtain ⟨c₁, c₂, rfl, hx, hr'⟩ := List.map_eq_append_iff.1 h₃
  obtain ⟨e, rfl⟩ : ∃ e, c₁ = [e] := by
    rcases c₁ with _ | ⟨e, _ | _⟩ <;> simp at hx
    exact ⟨e, rfl⟩
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hx
  refine ⟨e, hx.symm, ?_⟩
  have hlN : 0 < a₁.length := by
    have := congrArg List.length hvN
    simp only [List.length_append, List.length_map] at this
    omega
  have hlr : 0 < c₂.length := by
    have h₄ := congrArg List.length hr
    have h₅ := congrArg List.length hr'
    simp only [List.length_append, List.length_map] at h₄ h₅ hlen
    omega
  obtain ⟨a, as, rfl⟩ := List.exists_cons_of_length_pos hlN
  obtain ⟨b, bs, rfl⟩ := List.exists_cons_of_length_pos hlr
  have hsplit : (a :: as ++ (b₁ ++ ([e] ++ b :: bs))).map Sum.inr =
      (a :: ((as ++ b₁ ++ [e]) ++ [b])).map (Sum.inr (α := Ev (sigN n))) ++
        bs.map Sum.inr := by
    simp
  rw [hsplit] at hrun
  obtain ⟨z, hrun, -⟩ := LTS.Run.of_append hrun
  exact run_traps hrun e (by simp)

end Silmaril.Proofs.Wasm.Component.DWiring

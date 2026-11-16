module

public import Silmaril.Wasm.Component.DWiringLaws.Defs
public import Silmaril.Games.DivComp.Thms
public import Silmaril.Games.DivLTS.Thms
public import Silmaril.Games.Handler.Thms

/-!
# Interactions with handlers: basic facts

* Counting events: `nL`, `nR`, `zip_counts`; the hidden events of the two
  sides of an interaction agree (`hidden_eq`); `zip_append_sync`,
  `zip_length_le`.
* Handler runs: the positions they pass through (`spos`, `run_path`); they are
  deterministic (`run_det`); an increasing unbounded chain of handler plays
  converges to an infinite play of the handler (`lim_mem_inf_ofHandler`).
* An unbounded chain inside an infinite play converges to it (`lim_eq_of_mem`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.DWiringLaws

open Silmaril.Games Silmaril.Wasm.Component

universe u v w

/-! ## Counting events -/

/-- The number of left events. -/
def nL {α : Type u} {β : Type v} (s : List (α ⊕ β)) : ℕ := (s.filterMap Sum.getLeft?).length

/-- The number of right events. -/
def nR {α : Type u} {β : Type v} (s : List (α ⊕ β)) : ℕ :=
  (s.filterMap Sum.getRight?).length

section
variable {α : Type u} {β : Type v} {γ : Type w}

@[simp] theorem nL_nil : nL ([] : List (α ⊕ β)) = 0 := rfl
@[simp] theorem nR_nil : nR ([] : List (α ⊕ β)) = 0 := rfl
@[simp] theorem nL_inl (a : α) (s : List (α ⊕ β)) : nL (.inl a :: s) = nL s + 1 := rfl
@[simp] theorem nL_inr (b : β) (s : List (α ⊕ β)) : nL (.inr b :: s) = nL s := rfl
@[simp] theorem nR_inl (a : α) (s : List (α ⊕ β)) : nR (.inl a :: s) = nR s := rfl
@[simp] theorem nR_inr (b : β) (s : List (α ⊕ β)) : nR (.inr b :: s) = nR s + 1 := rfl

theorem length_eq (s : List (α ⊕ β)) : s.length = nL s + nR s := by
  induction s with
  | nil => rfl
  | cons x s ih => cases x <;> simp [ih] <;> omega

/-- How an interaction distributes events. -/
theorem zip_counts {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {p : List (α ⊕ γ)} (h : Zip s t p) :
    nL s = nL p ∧ nR t = nR p ∧ nR s = nL t := by
  induction h with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | left a _ ih => simp [ih.1, ih.2.1, ih.2.2]
  | right c _ ih => simp [ih.1, ih.2.1, ih.2.2]
  | sync b _ ih => simp [ih.1, ih.2.1, ih.2.2]

/-- The visible play is at most as long as the two sides together. -/
theorem zip_length_le {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {p : List (α ⊕ γ)}
    (h : Zip s t p) : p.length ≤ s.length + t.length := by
  have := zip_counts h
  rw [length_eq s, length_eq t, length_eq p]
  omega

/-- The hidden events of the two sides of an interaction agree. -/
theorem hidden_eq {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {p : List (α ⊕ γ)} (h : Zip s t p) :
    s.filterMap Sum.getRight? = t.filterMap Sum.getLeft? := by
  induction h with
  | nil => rfl
  | left a _ ih => exact ih
  | right c _ ih => exact ih
  | sync b _ ih => simp [ih]

theorem filterMap_map_inr (l : List β) :
    (l.map (Sum.inr (α := α))).filterMap Sum.getRight? = l := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [ih]

theorem filterMap_map_inl (l : List α) :
    (l.map (Sum.inl (β := β))).filterMap Sum.getLeft? = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem eq_map_inr : ∀ {w : List (α ⊕ β)}, nL w = 0 → w = (w.filterMap Sum.getRight?).map Sum.inr
  | [], _ => rfl
  | .inl _ :: _, h => by simp at h
  | .inr b :: w, h => by simpa using eq_map_inr (w := w) (by simpa using h)

theorem eq_map_inl : ∀ {w : List (α ⊕ β)}, nR w = 0 → w = (w.filterMap Sum.getLeft?).map Sum.inl
  | [], _ => rfl
  | .inr _ :: _, h => by simp at h
  | .inl a :: w, h => by simpa using eq_map_inl (w := w) (by simpa using h)

/-- Hidden events appended to both sides keep the visible play. -/
theorem zip_append_sync {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {p : List (α ⊕ γ)}
    (h : Zip s t p) : ∀ ws : List β, Zip (s ++ ws.map Sum.inr) (t ++ ws.map Sum.inl) p := by
  induction h with
  | nil =>
    intro ws
    induction ws with
    | nil => exact .nil
    | cons b ws ih => exact .sync b ih
  | left a _ ih => exact fun ws => .left a (ih ws)
  | right c _ ih => exact fun ws => .right c (ih ws)
  | sync b _ ih => exact fun ws => .sync b (ih ws)

/-- Extensions of both sides that keep the visible play are hidden events. -/
theorem ext_hidden {s s' : List (α ⊕ β)} {t t' : List (β ⊕ γ)} {p : List (α ⊕ γ)}
    (h : Zip s t p) (h' : Zip s' t' p) (hs : s <+: s') (ht : t <+: t') :
    ∃ ws : List β, s' = s ++ ws.map Sum.inr ∧ t' = t ++ ws.map Sum.inl := by
  obtain ⟨a, rfl⟩ := hs
  obtain ⟨b, rfl⟩ := ht
  have hc := zip_counts h
  have hc' := zip_counts h'
  have ha : nL a = 0 := by
    simp only [nL, List.filterMap_append, List.length_append] at hc hc' ⊢
    omega
  have hb : nR b = 0 := by
    simp only [nR, List.filterMap_append, List.length_append] at hc hc' ⊢
    omega
  have he := hidden_eq h'
  rw [List.filterMap_append, List.filterMap_append, hidden_eq h] at he
  have hab := List.append_cancel_left he
  refine ⟨a.filterMap Sum.getRight?, by rw [← eq_map_inr ha], ?_⟩
  rw [hab, ← eq_map_inl hb]
end

/-! ## Handler runs -/

section
variable {E F : Sig.{u}}

/-- The game position of a state of a reduction semantics. -/
def spos {R : Reduction E F} : R.State → Pos E F
  | .idle => .idle
  | .run q _ => .run q
  | .wait q m _ => .wait q m

theorem step_pos {R : Reduction E F} {x y : R.State} {o : Move E F}
    (h : R.toLTS.step x (some o) y) : Step (spos x) o (spos y) := by
  cases h with
  | ask q => exact .ask q
  | call _ => exact .call _ _
  | resume q m k n => exact .reply _ _ _
  | ret _ => exact .ret _ _

theorem step_pos_none {R : Reduction E F} {x y : R.State}
    (h : R.toLTS.step x none y) : spos x = spos y := by
  cases h with
  | tau _ => rfl

/-- A run passes through the positions of its states. -/
theorem run_path {R : Reduction E F} : ∀ {x y : R.State} {s : List (Move E F)},
    R.toLTS.Run x s y → Path (spos x) s (spos y)
  | _, _, _, .nil _ => .nil _
  | _, _, _, .tau hs hr => (step_pos_none hs) ▸ run_path hr
  | _, _, _, .vis hs hr => .cons (step_pos hs) (run_path hr)

theorem step_det {h : Handler E F} {x y y' : h.toReduction.State} {o : Option (Move E F)}
    (h₁ : h.toReduction.toLTS.step x o y) (h₂ : h.toReduction.toLTS.step x o y') : y = y' := by
  cases h₁ with
  | ask q => cases h₂; rfl
  | tau hc => exact hc.elim
  | call hc =>
    cases h₂ with
    | call hc' =>
      change _ = Prog.call _ _ at hc hc'
      rw [hc] at hc'
      cases hc'
      rfl
  | resume q m k n => cases h₂; rfl
  | ret hc => cases h₂; rfl

/-- Handler runs are deterministic. -/
theorem run_det {h : Handler E F} : ∀ {x y y' : h.toReduction.State} {s : List (Move E F)},
    h.toReduction.toLTS.Run x s y → h.toReduction.toLTS.Run x s y' → y = y'
  | _, _, _, _, .nil _, .nil _ => rfl
  | _, _, _, _, .tau hs _, _ => by cases hs with | tau hc => exact hc.elim
  | _, _, _, _, _, .tau hs _ => by cases hs with | tau hc => exact hc.elim
  | _, _, _, _, .vis hs hr, .vis hs' hr' => by
    rw [step_det hs hs'] at hr
    exact run_det hr hr'

/-- **An increasing unbounded chain of plays of a handler converges to one of
its infinite plays.** -/
theorem lim_mem_inf_ofHandler {h : Handler E F} {c : Chain (Move E F)} (hm : c.Mono)
    (hu : c.Unbounded) (hc : ∀ m, c m ∈ Strategy.ofHandler h) :
    c.lim ∈ (DStrategy.ofHandler h).inf := by
  have ex : ∀ m, ∃ y, h.toReduction.toLTS.Run .idle (c m) y :=
    fun m => Strategy.mem_ofHandler.1 (hc m)
  let r : h.toReduction.toLTS.InfRun :=
    { st := fun | 0 => .idle | m + 1 => (ex m).choose
      tr := fun | 0 => [] | m + 1 => c m
      st_zero := rfl
      tr_zero := rfl
      step := by
        intro m
        cases m with
        | zero => exact ⟨c 0, rfl, (ex 0).choose_spec⟩
        | succ m =>
          obtain ⟨w, hw⟩ := hm m
          refine ⟨w, hw.symm, ?_⟩
          have hr := (ex (m + 1)).choose_spec
          have hr₀ := (ex m).choose_spec
          change h.toReduction.toLTS.Run (ex m).choose w (ex (m + 1)).choose
          generalize (ex (m + 1)).choose = y at hr ⊢
          generalize (ex m).choose = y₀ at hr₀ ⊢
          rw [← hw] at hr
          obtain ⟨z, hz, hzw⟩ := LTS.Run.of_append hr
          rw [run_det hz hr₀] at hzw
          exact hzw }
  have hlim : r.tr.lim = c.lim := by
    ext q
    constructor
    · rintro ⟨m, hq⟩
      cases m with
      | zero => exact ⟨0, (List.prefix_nil.1 hq) ▸ List.nil_prefix⟩
      | succ m => exact ⟨m, hq⟩
    · rintro ⟨m, hq⟩
      exact ⟨m + 1, hq⟩
  have hu' : r.tr.Unbounded := fun k => by
    obtain ⟨m, hm⟩ := hu k
    exact ⟨m + 1, hm⟩
  have hl : ∀ m, Legal (r.tr m) := fun m => by
    cases m with
    | zero => exact Legal.nil
    | succ m => exact (Strategy.ofHandler h).legal (hc m)
  rw [← hlim]
  exact DStrategy.lim_mem_inf_ofLTS r hu' hl
end

/-! ## Chains in infinite plays -/

/-- An unbounded chain of members of an infinite play converges to it. -/
theorem lim_eq_of_mem {α : Type u} {I : Set (List α)} (hI : IsInfPlay I) {c : Chain α}
    (hc : ∀ m, c m ∈ I) (hu : c.Unbounded) : c.lim = I := by
  ext q
  constructor
  · rintro ⟨m, hq⟩
    exact hI.of_prefix (hc m) hq
  · intro hq
    obtain ⟨m, hm⟩ := hu q.length
    exact ⟨m, hI.prefix_of_length_le hq (hc m) hm⟩

end Silmaril.Proofs.Wasm.Component.DWiringLaws

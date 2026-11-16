module

public import Silmaril.Wasm.Cfg.Variant.Defs
public import Silmaril.Wasm.Cfg.BlockTree.Thms

@[expose] public section

/-!
# CFG variants: theorems relating TE and AE to the legacy graph

* `edge_iff_te`: a legacy edge is a TE edge, or the `trap` edge of a `mustTrap` block.
* `edge_iff_ae`: a legacy edge is an AE edge, the `trap` edge of a must-trap block, the `raise`
  edge of a must-raise block (`succOf_raise_iff`: only `throw`/`throw_ref` have one), or a
  `try_table`'s catch edge.
* `succTE_of_mustTrap`: a must-trap block has no TE successors (a terminal, abrupt block).
* `succOf_trap_iff`: only `unreachable` has a legacy edge to `trap` (labels, continuations and
  entries never resolve to `trap`).
-/

namespace Silmaril.Wasm.Cfg

theorem contRev_ne_trap (body : Expr) : ∀ rp, contRev body rp ≠ .trap
  | [] => by simp [contRev]
  | (m, _) :: rp => by
    unfold contRev
    split
    · simp
    · exact contRev_ne_trap body rp

theorem entry_ne_trap (body : Expr) (p : List SeqStep) (i : Nat) : entry body p i ≠ .trap := by
  unfold entry; split
  · simp
  · exact contRev_ne_trap body _

theorem labelsRev_ne_trap (body : Expr) : ∀ rp, ∀ t ∈ labelsRev body rp, t ≠ .trap
  | [] => by simp [labelsRev]
  | (m, a) :: rp => by
    intro t ht
    simp only [labelsRev, List.mem_cons] at ht
    rcases ht with rfl | ht
    · split
      · exact entry_ne_trap _ _ _
      · exact contRev_ne_trap _ _
    · exact labelsRev_ne_trap body rp t ht

theorem resolveT_ne_trap {ℓ : List Target} (h : ∀ t ∈ ℓ, t ≠ .trap) (l : LabelIdx) :
    resolveT ℓ l ≠ .trap := by
  unfold resolveT
  rw [List.getD_eq_getElem?_getD]
  cases hx : ℓ[l.value.val]? with
  | none => simp
  | some t => simpa using h t (List.mem_of_getElem? hx)

/-- **Only `unreachable` has a legacy edge to `trap`.** -/
theorem succOf_trap_iff (body : Expr) (b : BlockId) (s : Segment) :
    Target.trap ∈ succOf body b s ↔ s.term = some .unreachable := by
  have hr : ∀ l, Target.trap ≠ resolveT (labels body b.seq) l :=
    fun l => (resolveT_ne_trap (labelsRev_ne_trap body b.seq.reverse) l).symm
  have he : ∀ p i, Target.trap ≠ entry body p i := fun p i => (entry_ne_trap body p i).symm
  constructor
  · intro h
    unfold succOf at h
    split at h
    all_goals first
      | assumption
      | (simp [List.mem_map, he, hr] at h; done)
      | (simp [List.mem_map, he, hr] at h
         obtain ⟨a, -, ha⟩ := h
         exact absurd ha.symm (hr _))
  · intro h; simp [succOf, h]

/-- **The translation back**: a legacy edge is a TE edge or the `trap` edge of a must-trap
block. -/
theorem edge_iff_te (body : Expr) (b : BlockId) (t : Target) :
    Edge body b t ↔ EdgeTE body b t ∨ (t = .trap ∧ mustTrap body b) := by
  constructor
  · intro h
    by_cases ht : t = .trap
    · subst ht
      obtain ⟨s, hs, hm⟩ := h
      exact Or.inr ⟨rfl, s, hs, (succOf_trap_iff body b s).1 hm⟩
    · exact Or.inl ⟨h, ht⟩
  · rintro (⟨h, -⟩ | ⟨rfl, s, hs, hu⟩)
    · exact h
    · exact ⟨s, hs, (succOf_trap_iff body b s).2 hu⟩

/-- A must-trap block has exactly the legacy successor `trap`, hence none in TE. -/
theorem succTE_of_mustTrap (body : Expr) (b : BlockId) (s : Segment)
    (h : s.term = some .unreachable) : succTE body b s = [] := by
  simp [succTE, succOf, h]

/-! ## Variant AE -/

theorem contRev_ne_raise (body : Expr) : ∀ rp, contRev body rp ≠ .raise
  | [] => by simp [contRev]
  | (m, _) :: rp => by
    unfold contRev
    split
    · simp
    · exact contRev_ne_raise body rp

theorem entry_ne_raise (body : Expr) (p : List SeqStep) (i : Nat) : entry body p i ≠ .raise := by
  unfold entry; split
  · simp
  · exact contRev_ne_raise body _

theorem labelsRev_ne_raise (body : Expr) : ∀ rp, ∀ t ∈ labelsRev body rp, t ≠ .raise
  | [] => by simp [labelsRev]
  | (m, a) :: rp => by
    intro t ht
    simp only [labelsRev, List.mem_cons] at ht
    rcases ht with rfl | ht
    · split
      · exact entry_ne_raise _ _ _
      · exact contRev_ne_raise _ _
    · exact labelsRev_ne_raise body rp t ht

theorem resolveT_ne_raise {ℓ : List Target} (h : ∀ t ∈ ℓ, t ≠ .raise) (l : LabelIdx) :
    resolveT ℓ l ≠ .raise := by
  unfold resolveT
  rw [List.getD_eq_getElem?_getD]
  cases hx : ℓ[l.value.val]? with
  | none => simp
  | some t => simpa using h t (List.mem_of_getElem? hx)

/-- **Only `throw`/`throw_ref` have a legacy edge to `raise`.** -/
theorem succOf_raise_iff (body : Expr) (b : BlockId) (s : Segment) :
    Target.raise ∈ succOf body b s ↔ (∃ x, s.term = some (.throw x)) ∨ s.term = some .throwRef := by
  have hr : ∀ l, Target.raise ≠ resolveT (labels body b.seq) l :=
    fun l => (resolveT_ne_raise (labelsRev_ne_raise body b.seq.reverse) l).symm
  have he : ∀ p i, Target.raise ≠ entry body p i := fun p i => (entry_ne_raise body p i).symm
  constructor
  · intro h
    unfold succOf at h
    split at h
    all_goals first
      | exact Or.inl ⟨_, by assumption⟩
      | exact Or.inr (by assumption)
      | (simp [List.mem_map, he, hr] at h; done)
      | (simp [List.mem_map, he, hr] at h
         obtain ⟨a, -, ha⟩ := h
         exact absurd ha.symm (hr _))
  · rintro (⟨x, h⟩ | h) <;> simp [succOf, h]

/-- **The all-effects translation back**: a legacy edge is an AE edge, the `trap` edge of a
must-trap block, the `raise` edge of a must-raise block, or a `try_table`'s catch edge (whose
target AE reaches through the handler outcomes of raises). -/
theorem edge_iff_ae (body : Expr) (b : BlockId) (t : Target) :
    Edge body b t ↔ EdgeAE body b t ∨ (t = .trap ∧ mustTrap body b) ∨
      (t = .raise ∧ mustRaise body b) ∨ catchEdge body b t := by
  constructor
  · rintro ⟨s, hs, hm⟩
    by_cases ht : t = .trap
    · subst ht; exact Or.inr (Or.inl ⟨rfl, s, hs, (succOf_trap_iff body b s).1 hm⟩)
    by_cases hr : t = .raise
    · subst hr; exact Or.inr (Or.inr (Or.inl ⟨rfl, s, hs, (succOf_raise_iff body b s).1 hm⟩))
    cases hterm : s.term with
    | some i =>
      cases i
      case tryTable bt cs bd =>
        simp only [succOf, hterm, List.mem_cons] at hm
        rcases hm with rfl | hm
        · exact Or.inl ⟨s, hs, by simp [succAE, hterm]⟩
        · exact Or.inr (Or.inr (Or.inr ⟨s, bt, cs, bd, hs, hterm, hm⟩))
      all_goals
        exact Or.inl ⟨s, hs, by simp [succAE, hterm, ht, hr]; simpa [hterm] using hm⟩
    | none => exact Or.inl ⟨s, hs, by simp [succAE, hterm, ht, hr]; simpa [hterm] using hm⟩
  · rintro (⟨s, hs, hm⟩ | ⟨rfl, s, hs, hu⟩ | ⟨rfl, s, hs, hu⟩ | ⟨s, bt, cs, bd, hs, hterm, hm⟩)
    · refine ⟨s, hs, ?_⟩
      unfold succAE at hm
      split at hm
      · rename_i bt cs bd hterm; simp only [List.mem_singleton] at hm; subst hm; simp [succOf, hterm]
      · exact (List.mem_filter.1 hm).1
    · exact ⟨s, hs, (succOf_trap_iff body b s).2 hu⟩
    · exact ⟨s, hs, (succOf_raise_iff body b s).2 hu⟩
    · exact ⟨s, hs, by simp [succOf, hterm]; exact Or.inr (by simpa using hm)⟩

/-! ## Maximal blocks -/

/-- If `c` merges into `b`, then `b`'s only AE edge goes to `c`. -/
theorem canMerge_succ {body : Expr} {b c : BlockId} (h : canMerge body b c = true) (t : Target) :
    EdgeAE body b t ↔ t = .block c := by
  unfold canMerge at h
  split at h
  · rename_i s hs
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    constructor
    · rintro ⟨s', hs', ht⟩
      rw [hs] at hs'; cases hs'
      rw [h.1.1] at ht; simpa using ht
    · rintro rfl; exact ⟨s, hs, by rw [h.1.1]; simp⟩
  · cases h

/-- If `c` merges into `b`, then no other block has an AE or handler edge into `c`. -/
theorem canMerge_pred {body : Expr} {b c : BlockId} (h : canMerge body b c = true)
    {b' : BlockId} {s' : Segment} (hs' : lookup body b' = some s')
    (hin : .block c ∈ succAE body b' s' ∨ .block c ∈ handlerSucc body b' s') : b' = b := by
  unfold canMerge at h
  split at h
  · simp only [Bool.and_eq_true] at h
    have hall := h.2
    unfold onlyPred at hall
    rw [List.all_eq_true] at hall
    have := hall (b', s') ((mem_blocks body b' s').2 hs')
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at this
    rcases this with h1 | h1
    · exact h1
    · exfalso
      have : (succAE body b' s' ++ handlerSucc body b' s').contains (Target.block c) = true := by
        simpa [List.contains_iff_mem] using hin
      rw [this] at h1; cases h1
  · cases h

/-- If `c` merges into `b`, then `c` is not the entry. -/
theorem canMerge_not_entry {body : Expr} {b c : BlockId} (h : canMerge body b c = true) :
    cfgEntry body ≠ .block c := by
  unfold canMerge at h
  split at h
  · simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h; exact h.1.2
  · cases h

end Silmaril.Wasm.Cfg

module

public import Silmaril.Wasm.Cfg.Variant.Defs

@[expose] public section

/-!
# CFG variants: theorems relating TE to the legacy graph

* `edge_iff_te`: a legacy edge is a TE edge, or the `trap` edge of a `mustTrap` block.
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

end Silmaril.Wasm.Cfg

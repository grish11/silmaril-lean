module

public import Silmaril.Semantics.Region.Tree.CFG.Defs
public import Silmaril.Semantics.Region.Tree.Thms

@[expose] public section
namespace Silmaril.Semantics.Region.Tree.Proofs

theorem flatten_lift {V Seg Lab} (r : TreeRow V Seg Lab) (g : FlatCFG Lab) (h : LabelCover r g) :
    (SegCFG.lift r g).flatten = g := by
  have succ : (SegCFG.lift r g).flatten.successors = g.successors := by
    funext a
    apply Set.ext
    intro b
    constructor
    · rintro ⟨v, hv, c, hc, hb⟩
      have : c = a := Option.some.inj (hc.symm.trans hv)
      exact this ▸ hb
    · intro hb
      have inside := h.source_closed a b hb
      rw [← h.labels_eq] at inside
      obtain ⟨v, hv⟩ := inside
      exact ⟨v, hv, a, hv, hb⟩
  cases g
  change FlatCFG.mk _ _ _ _ = FlatCFG.mk _ _ _ _
  congr 1
  · exact h.entry_eq
  · exact h.labels_eq
  · exact h.exits_eq

theorem lift_exists_iff {V Seg Lab} (r : TreeRow V Seg Lab) (g : FlatCFG Lab) :
    (∃ tree : SegCFG V Seg Lab, tree.region = r ∧ tree.flatten = g) ↔ LabelCover r g := by
  constructor
  · rintro ⟨tree, rfl, rfl⟩
    exact ⟨rfl, rfl, rfl, fun _ _ ⟨v, hv, _⟩ => ⟨v, hv⟩⟩
  · intro h
    exact ⟨SegCFG.lift r g, rfl, flatten_lift r g h⟩

theorem flatten_successors_unique {V Seg Lab} (g : SegCFG V Seg Lab) (unique : UniqueLabels g.region.body)
    (v : V) (a : Lab) (hv : g.region.body.labelAt v = some a) : g.flatten.successors a = g.successors v := by
  apply Set.ext
  intro b
  constructor
  · rintro ⟨w, hw, hb⟩
    exact unique w v a hw hv ▸ hb
  · intro hb
    exact ⟨v, hv, hb⟩

theorem covers_trans {Lab} {a b c : FlatCFG Lab} (ab : Covers a b) (bc : Covers b c) : Covers a c := by
  refine ⟨ab.entry_eq.trans bc.entry_eq, bc.internal.trans ab.internal, bc.exits.trans ab.exits, ?_⟩
  intro v hv
  exact (bc.successors v hv).trans (ab.successors v (bc.internal hv))

end Silmaril.Semantics.Region.Tree.Proofs

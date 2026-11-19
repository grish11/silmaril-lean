module

public import Silmaril.Automata.Graph.RegionTree.Defs
public import Silmaril.Automata.Graph.Thms
public import Silmaril.Semantics.Region.Tree.CFG.Thms

@[expose] public section
namespace Silmaril.Automata.Graph.RegionTree.Proofs
open Silmaril.Machine.Graph
open Silmaril.Semantics.Region.Tree

theorem witness_cover {Seg} {g : Digraph} {policy : ExitPolicy g} {r : TreeRow Nat Seg Nat}
    (h : Witness g policy r) : LabelCover r (flat g policy) := by
  refine ⟨h.entry_eq, h.exits_eq, ?_, fun _ _ hb => hb.1⟩
  ext l
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨live, rfl⟩ := (h.labels v l).mp hv
    exact live
  · intro live
    exact ⟨l, (h.labels l l).mpr ⟨live, rfl⟩⟩

theorem ancestor_descendant (s : Shape Nat) {a b : Nat} (h : Ancestor s.parent a b) : s.Descendant a b := by
  induction h with
  | parent hp => exact Relation.ReflTransGen.single hp
  | up hp _ ih => exact ih.tail hp

theorem descendant_iff_ancestor (s : Shape Nat) {a b : Nat} :
    s.Descendant a b ↔ a = b ∨ Ancestor s.parent a b := by
  constructor
  · intro h
    induction h with
    | refl => exact Or.inl rfl
    | tail _ edge ih =>
      rcases ih with eq | ancestor
      · exact Or.inr (eq.symm ▸ Ancestor.parent edge)
      · exact Or.inr (Ancestor.up edge ancestor)
  · rintro (rfl | h)
    · exact .refl
    · exact ancestor_descendant s h

theorem witness_rooted {Seg} {g : Digraph} {policy : ExitPolicy g} {r : TreeRow Nat Seg Nat}
    (h : Witness g policy r) {v : Nat} (live : g.Reachable v) : r.body.shape.Descendant r.body.shape.root v := by
  rw [h.root_eq]
  by_cases eq : v = g.entry
  · exact eq ▸ Relation.ReflTransGen.refl
  · apply ancestor_descendant
    exact (h.exact g.entry v live).mpr ⟨Digraph.Dominates.entry g v, fun e => eq e.symm⟩

theorem proposal_witness {Seg} (g : Digraph) (policy : ExitPolicy g) (payload : Nat → Seg) :
    Witness g policy (proposal g policy payload) := by
  classical
  refine ⟨rfl, rfl, rfl, ?_, idom_exact g, ?_⟩
  · intro v l
    simp only [proposal, SegTree.labelAt]
    split_ifs with h
    · simp [h, eq_comm]
    · simp [h]
  · intro v l eq
    simp [proposal] at eq

end Silmaril.Automata.Graph.RegionTree.Proofs

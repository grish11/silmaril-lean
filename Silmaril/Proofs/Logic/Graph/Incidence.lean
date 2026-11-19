module

public import Silmaril.Logic.Graph.Incidence.Defs

@[expose] public section
namespace Silmaril.Logic.Graph.Incidence.Proofs
open CategoryTheory Silmaril.Logic.Institution

theorem satisfaction {A B : Signature} (f : A ⟶ B) (M : Model B) (p : Sentence A) :
    Sat M (sentenceMap f p) ↔ Sat (reduct f M) p := by
  cases p with
  | node n => rfl
  | edge e => rfl
  | sourceKnown e => simp only [sentenceMap, Sat, ← f.source, Option.isSome_map]
  | targetKnown e => simp only [sentenceMap, Sat, ← f.target, Option.isSome_map]

theorem wf_reduct {A B : Signature} (f : A ⟶ B) (M : Model B) (h : M.WellFormed) :
    (reduct f M).WellFormed := by
  intro e he n endpoint
  apply h (f.edge e) he (f.node n)
  rcases endpoint with hs | ht
  · exact .inl (by rw [← f.source, hs]; rfl)
  · exact .inr (by rw [← f.target, ht]; rfl)

theorem relation_forward {A B : Signature} (f : A ⟶ B) (M : Model B) {a b : A.Node}
    (h : (reduct f M).relation.edge a b) : M.relation.edge (f.node a) (f.node b) := by
  obtain ⟨e, he, hs, ht⟩ := h
  exact ⟨f.edge e, he, by rw [← f.source, hs]; rfl, by rw [← f.target, ht]; rfl⟩

theorem relation_iff {A B : Signature} (f : A ⟶ B) (M : Model B)
    (nodes : Function.Injective f.node) (edges : Function.Surjective f.edge) (a b : A.Node) :
    (reduct f M).relation.edge a b ↔ M.relation.edge (f.node a) (f.node b) := by
  refine ⟨relation_forward f M, ?_⟩
  rintro ⟨e', he', hs, ht⟩
  obtain ⟨e, rfl⟩ := edges e'
  refine ⟨e, he', ?_, ?_⟩
  · have eq := (f.source e).trans hs
    exact (Option.map_injective nodes) eq
  · have eq := (f.target e).trans ht
    exact (Option.map_injective nodes) eq

end Silmaril.Logic.Graph.Incidence.Proofs

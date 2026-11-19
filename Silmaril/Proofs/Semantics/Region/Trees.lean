module

public import Silmaril.Semantics.Region.Tree.Defs
public import Silmaril.Semantics.Region.Abstract.Thms

@[expose] public section
namespace Silmaril.Semantics.Region.Tree.Proofs

theorem full_annotated {V Seg Lab} (t : FullTree V Seg Lab) : FullyAnnotated (embedFull t) := by
  intro v s a h
  cases eq : t.data v with
  | label l => simp [embedFull, AnnotatedTree.mapAnn, NodeData.mapAnn, eq] at h
  | segment p l =>
    simp only [embedFull, AnnotatedTree.mapAnn, NodeData.mapAnn, eq, NodeData.segment.injEq] at h
    exact ⟨l, h.2.symm⟩

theorem embedFull_injective {V Seg Lab} : Function.Injective (@embedFull V Seg Lab) := by
  rintro ⟨s, f⟩ ⟨t, g⟩ eq
  have shapes := congrArg AnnotatedTree.shape eq
  have data := congrArg AnnotatedTree.data eq
  dsimp [embedFull, AnnotatedTree.mapAnn] at shapes data
  congr
  funext v
  have atv := congrFun data v
  cases hf : f v <;> cases hg : g v <;> simp_all [NodeData.mapAnn]

theorem embed_complete {V Seg Lab} (t : SegTree V Seg Lab) (h : FullyAnnotated t) :
    embedFull (complete t h) = t := by
  rcases t with ⟨s, f⟩
  apply congrArg (AnnotatedTree.mk s)
  funext v
  dsimp only [embedFull, AnnotatedTree.mapAnn, complete]
  split
  · rename_i l eq
    simpa only [NodeData.mapAnn] using eq.symm
  · rename_i p a eq
    have choice := Classical.choose_spec (h v p a eq)
    simp only [NodeData.mapAnn]
    exact (congrArg (NodeData.segment p) choice.symm).trans eq.symm

theorem fullyAnnotated_iff {V Seg Lab} (t : SegTree V Seg Lab) :
    FullyAnnotated t ↔ ∃ f, embedFull f = t := by
  constructor
  · intro h; exact ⟨complete t h, embed_complete t h⟩
  · rintro ⟨f, rfl⟩; exact full_annotated f

theorem erase_embedRootOnly {V Seg Lab} (r : RootOnlyRow V Seg Lab) :
    eraseRootOnly (embedRootOnly r) = r := by
  rcases r with ⟨e, xs, ⟨s, f⟩⟩
  apply congrArg (fun data => Boundary.mk e xs (AnnotatedTree.mk s data))
  funext v
  dsimp only [eraseRootOnly, embedRootOnly, Boundary.map, eraseAnnotations, AnnotatedTree.mapAnn]
  cases f v <;> simp [NodeData.mapAnn]

theorem labels_eq {V Seg Lab} (t : SegTree V Seg Lab) : t.labels = t.leafLabels ∪ t.entryLabels := by
  ext l
  constructor
  · rintro ⟨v, h⟩
    cases eq : t.data v with
    | label a =>
      have : a = l := Option.some.inj (by simpa [SegTree.labelAt, eq] using h)
      exact Or.inl ⟨v, this ▸ eq⟩
    | segment s a =>
      have : a = some l := by simpa [SegTree.labelAt, eq] using h
      exact Or.inr ⟨v, s, this ▸ eq⟩
  · rintro (⟨v, h⟩ | ⟨v, s, h⟩) <;> exact ⟨v, by simp [SegTree.labelAt, h]⟩

theorem toLabTree_labelAt {V Seg Lab} (t : SegTree V Seg Lab) (v : V) :
    t.toLabTree.labelAt v = t.labelAt v := by
  cases eq : t.data v <;> simp [SegTree.toLabTree, SegTree.labelAt, eq]

theorem uncurry_curry {Img Assum Tree} (M : RegionModel (Img × Assum) Tree) : uncurry (curry M) = M := by
  ext ⟨⟨i, a⟩, t⟩
  rfl

theorem curry_uncurry {Img Assum Tree} (P : RegionPred Img Assum Tree) : curry (uncurry P) = P := by
  funext i a t
  rfl

theorem curry_le_iff {Img Assum Tree} (M N : RegionModel (Img × Assum) Tree) :
    curry M ≤ curry N ↔ M ≤ N := by
  constructor
  · intro h j hj
    exact h j.1.1 j.1.2 j.2 hj
  · intro h i a t hp
    exact h hp

theorem image_holds {Context A B} (f : A → B) (M : RegionModel Context A) (c : Context) (b : B) :
    (image f M).Holds c b ↔ ∃ a, M.Holds c a ∧ f a = b := by
  constructor
  · rintro ⟨⟨d, a⟩, hm, eq⟩
    cases eq
    exact ⟨a, hm, rfl⟩
  · rintro ⟨a, hm, rfl⟩
    exact ⟨(c, a), hm, rfl⟩

theorem image_comp {Context A B C} (f : A → B) (g : B → C) (M : RegionModel Context A) :
    image g (image f M) = image (g ∘ f) M := by
  simp only [image, Abstract.forget, Set.image_image, Function.comp_def]

theorem image_iff_of_witnesses {Context A B} (f : A → B) (M : RegionModel Context A)
    (N : RegionModel Context B) (sound : Refines f M N) (complete : HasWitnesses f M N) : image f M = N := by
  ext ⟨c, b⟩
  change (image f M).Holds c b ↔ N.Holds c b
  rw [image_holds]
  exact ⟨fun ⟨a, hm, eq⟩ => eq ▸ sound c a hm, complete c b⟩

end Silmaril.Semantics.Region.Tree.Proofs

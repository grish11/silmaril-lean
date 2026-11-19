module

public import Silmaril.Semantics.Region.Tree.Defs
public import Silmaril.Semantics.Region.Abstract.Thms
import Silmaril.Proofs.Semantics.Region.Trees

@[expose] public section
namespace Silmaril.Semantics.Region.Tree

theorem full_annotated {V Seg Lab} (t : FullTree V Seg Lab) : FullyAnnotated (embedFull t) := Proofs.full_annotated t

theorem embedFull_injective {V Seg Lab} : Function.Injective (@embedFull V Seg Lab) := Proofs.embedFull_injective

theorem embed_complete {V Seg Lab} (t : SegTree V Seg Lab) (h : FullyAnnotated t) :
    embedFull (complete t h) = t := Proofs.embed_complete t h

theorem complete_embedFull {V Seg Lab} (t : FullTree V Seg Lab) :
    complete (embedFull t) (full_annotated t) = t :=
  embedFull_injective (embed_complete _ _)

theorem fullyAnnotated_iff {V Seg Lab} (t : SegTree V Seg Lab) :
    FullyAnnotated t ↔ ∃ f, embedFull f = t := Proofs.fullyAnnotated_iff t

theorem erase_embedRootOnly {V Seg Lab} (r : RootOnlyRow V Seg Lab) :
    eraseRootOnly (embedRootOnly r) = r := Proofs.erase_embedRootOnly r

theorem embedRootOnly_injective {V Seg Lab} : Function.Injective (@embedRootOnly V Seg Lab) := by
  intro a b h
  simpa only [erase_embedRootOnly] using congrArg eraseRootOnly h

theorem embed_eraseRootOnly_of_image {V Seg Lab} {r : TreeRow V Seg Lab}
    (h : ∃ bare, embedRootOnly bare = r) : embedRootOnly (eraseRootOnly r) = r := by
  obtain ⟨bare, rfl⟩ := h
  rw [erase_embedRootOnly]

theorem labels_eq {V Seg Lab} (t : SegTree V Seg Lab) : t.labels = t.leafLabels ∪ t.entryLabels := Proofs.labels_eq t

theorem toLabTree_labelAt {V Seg Lab} (t : SegTree V Seg Lab) (v : V) :
    t.toLabTree.labelAt v = t.labelAt v := Proofs.toLabTree_labelAt t v

theorem frontier_child_labeled {V Seg Lab} {t : SegTree V Seg Lab} {a b : Lab} :
    t.frontier.child a b → a ∈ t.labels ∧ b ∈ t.labels :=
  fun ⟨p, c, hp, hc, _⟩ => ⟨⟨p, hp⟩, ⟨c, hc⟩⟩

theorem frontier_root_labeled {V Seg Lab} {t : SegTree V Seg Lab} {a : Lab} :
    a ∈ t.frontier.roots → a ∈ t.labels := fun ⟨v, h, _⟩ => ⟨v, h⟩

theorem internal_ne_exit {Lab} (a b : Lab) : LabelRole.internal a ≠ LabelRole.exit b := by intro h; cases h

theorem pieceTree_labelAt {V Support Lab} (shape : Shape V) (pieces : V → RegionPiece Support Lab) (v : V) :
    (pieceTree shape pieces).labelAt v = some (pieces v).entry := rfl

theorem flatten_boundary {V Seg Lab} (r : TreeRow V Seg Lab) : r.flatten.boundary = r.boundary := rfl

theorem uncurry_curry {Img Assum Tree} (M : RegionModel (Img × Assum) Tree) : uncurry (curry M) = M :=
  Proofs.uncurry_curry M

theorem curry_uncurry {Img Assum Tree} (P : RegionPred Img Assum Tree) : curry (uncurry P) = P :=
  Proofs.curry_uncurry P

def curryEquiv {Img Assum Tree} : RegionModel (Img × Assum) Tree ≃ RegionPred Img Assum Tree where
  toFun := curry
  invFun := uncurry
  left_inv := uncurry_curry
  right_inv := curry_uncurry

theorem curry_le_iff {Img Assum Tree} (M N : RegionModel (Img × Assum) Tree) :
    curry M ≤ curry N ↔ M ≤ N := Proofs.curry_le_iff M N

def curryOrderIso {Img Assum Tree} : RegionModel (Img × Assum) Tree ≃o RegionPred Img Assum Tree where
  toEquiv := curryEquiv
  map_rel_iff' := curry_le_iff _ _

def lawfulCurryEquiv {Img Assum Tree} (rules : Abstract.Rules ((Img × Assum) × Tree)) :
    LawfulRegionModel rules ≃ CurriedLawfulModel rules where
  toFun M := ⟨curry M.val, by rw [uncurry_curry]; exact M.property⟩
  invFun P := ⟨uncurry P.val, P.property⟩
  left_inv M := Subtype.ext (uncurry_curry M.val)
  right_inv P := by cases P; rfl

instance {Img Assum Tree} (rules : Abstract.Rules ((Img × Assum) × Tree)) :
    CompleteLattice (CurriedLawfulModel rules) := (lawfulCurryEquiv rules).symm.completeLattice

theorem curried_lawful_le_iff {Img Assum Tree} {rules : Abstract.Rules ((Img × Assum) × Tree)}
    (M N : CurriedLawfulModel rules) : M ≤ N ↔ uncurry M.val ⊆ uncurry N.val := Iff.rfl

/-- The grouped and split context predicate signatures are genuinely equivalent. -/
def contextEquiv {Img Assum Tree} : ContextRegionPred (Img × Assum) Tree ≃ RegionPred Img Assum Tree where
  toFun P i a t := P (i, a) t
  invFun P c t := P c.1 c.2 t
  left_inv _ := rfl
  right_inv _ := rfl

example {Context Tree} : CompleteLattice (RegionModel Context Tree) := inferInstance
example {Img Assum Tree} : CompleteLattice (RegionPred Img Assum Tree) := inferInstance
example {Context Tree} (rules : Abstract.Rules (Context × Tree)) : CompleteLattice (LawfulRegionModel rules) := inferInstance

theorem image_holds {Context A B} (f : A → B) (M : RegionModel Context A) (c : Context) (b : B) :
    (image f M).Holds c b ↔ ∃ a, M.Holds c a ∧ f a = b := Proofs.image_holds f M c b

theorem tree_yields_image {Context A B} (f : A → B) (M : RegionModel Context A) (c : Context) (a : A)
    (h : M.Holds c a) : (image f M).Holds c (f a) := (image_holds f M c _).mpr ⟨a, h, rfl⟩

theorem image_comp {Context A B C} (f : A → B) (g : B → C) (M : RegionModel Context A) :
    image g (image f M) = image (g ∘ f) M := Proofs.image_comp f g M

theorem image_sSup {Context A B} (f : A → B) (models : Set (RegionModel Context A)) :
    image f (sSup models) = sSup (image f '' models) := Abstract.forget_sSup _ models

theorem image_iff_of_witnesses {Context A B} (f : A → B) (M : RegionModel Context A)
    (N : RegionModel Context B) (sound : Refines f M N) (complete : HasWitnesses f M N) : image f M = N :=
  Proofs.image_iff_of_witnesses f M N sound complete

/-- Tree → support/boundary → boundary equals direct boundary erasure. -/
theorem flat_boundary_image {Context V Seg Lab} (M : RegionModel Context (TreeRow V Seg Lab)) :
    image FlatRegion.boundary (image TreeRow.flatten M) = image TreeRow.boundary M := by
  rw [image_comp]
  rfl

end Silmaril.Semantics.Region.Tree

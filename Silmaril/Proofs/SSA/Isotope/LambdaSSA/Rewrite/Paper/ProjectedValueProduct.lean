module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Values.Product.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Values.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Tensor.Projections.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Product.Extensionality.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.ProductEta.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Iteration.Defs

/-! # Projection computations and uniqueness of projected copying values -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectedValueProduct.Default

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper (Eqv)
open Paper.TypeCategory CategoryTheory
open CfgEta.TypeCategory (productFstBranches productSndBranches seqValueBranches
  whiskerLeftRegion_typed whiskerRightRegion_typed)

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "obj" => ofType (τ := τ) (Φ := Φ)

private abbrev fstArrow (A B : τ) : obj (product A B) ⟶ obj A := ofRegion (productFstBranches A B)
private abbrev sndArrow (A B : τ) : obj (product A B) ⟶ obj B := ofRegion (productSndBranches A B)

private theorem branch_pair_fst {X A B : τ} {a b : Tm Φ}
    (ha : Tm.BranchValue [X] a A) (hb : Tm.BranchValue [X] b B) :
    ofRegion (.br (ℓ := 0) rfl (.pair ha hb)) ≫ fstArrow A B = ofRegion (.br (ℓ := 0) rfl ha) := by
  let hr := ValueBranches.br (Φ := Φ) (L := [product A B]) (ℓ := 0) rfl (.pair ha hb)
  let hs := productFstBranches (Φ := Φ) A B
  change ofRegion hr ≫ ofRegion hs = _
  rw [ofRegion_comp hr hs (seqValueBranches hr hs)]
  apply (ofRegion_eq_iff _ _).2
  exact .productBeta (.let₂Beta ha hb (.br rfl (.var (i := 1) rfl)))

private theorem branch_pair_snd {X A B : τ} {a b : Tm Φ}
    (ha : Tm.BranchValue [X] a A) (hb : Tm.BranchValue [X] b B) :
    ofRegion (.br (ℓ := 0) rfl (.pair ha hb)) ≫ sndArrow A B = ofRegion (.br (ℓ := 0) rfl hb) := by
  let hr := ValueBranches.br (Φ := Φ) (L := [product A B]) (ℓ := 0) rfl (.pair ha hb)
  let hs := productSndBranches (Φ := Φ) A B
  change ofRegion hr ≫ ofRegion hs = _
  rw [ofRegion_comp hr hs (seqValueBranches hr hs)]
  apply (ofRegion_eq_iff _ _).2
  exact .productBeta (.let₂Beta ha hb (.br rfl (.var (i := 0) rfl)))

private theorem diagonal_fst (X : τ) :
    diagonalArrow (Φ := Φ) X ≫ fstArrow X X = 𝟙 (obj X) :=
  (branch_pair_fst (.var rfl) (.var rfl)).trans (ofRegion_id X)

private theorem diagonal_snd (X : τ) :
    diagonalArrow (Φ := Φ) X ≫ sndArrow X X = 𝟙 (obj X) :=
  (branch_pair_snd (.var rfl) (.var rfl)).trans (ofRegion_id X)

private theorem whiskerLeft_discard_fst (A B : τ) :
    whiskerLeft (obj A) (discardArrow B) ≫ fstArrow A Silmaril.unit = fstArrow A B := by
  let hr : ValueBranches [B] (.br 0 .unit : Region Φ) [Silmaril.unit] := .br rfl .unit
  unfold fstArrow discardArrow
  rw [whiskerLeft_ofRegion]
  unfold tensorObj
  rw [ofRegion_comp _ _
    (seqValueBranches (whiskerLeftRegion_typed A hr) (productFstBranches A Silmaril.unit))]
  apply (ofRegion_eq_iff _ _).2
  apply Eqv.let₂ (A := A) (B := B) (.var rfl)
  change Eqv [B, A, product A B] (.let₂ (.pair (.var 1) (Tm.unit : Tm Φ)) (.br 0 (.var 1)))
    (.br 0 (.var 1)) [A]
  exact .productBeta (.let₂Beta (.var rfl) .unit
    (.br rfl (.var (i := 1) rfl)))

private theorem whiskerRight_discard_snd (A B : τ) :
    whiskerRight (discardArrow A) (obj B) ≫ sndArrow Silmaril.unit B = sndArrow A B := by
  let hr : ValueBranches [A] (.br 0 .unit : Region Φ) [Silmaril.unit] := .br rfl .unit
  unfold sndArrow discardArrow
  rw [whiskerRight_ofRegion]
  unfold tensorObj
  rw [ofRegion_comp _ _
    (seqValueBranches (whiskerRightRegion_typed B hr) (productSndBranches Silmaril.unit B))]
  apply (ofRegion_eq_iff _ _).2
  apply Eqv.let₂ (A := A) (B := B) (.var rfl)
  change Eqv [B, A, product A B] (.let₂ (.pair (Tm.unit : Tm Φ) (.var 0)) (.br 0 (.var 0)))
    (.br 0 (.var 0)) [B]
  exact .productBeta (.let₂Beta .unit (.var rfl) (.br rfl (.var (i := 0) rfl)))


private theorem guarded_discard (A B : τ) :
    Eqv [product A B] (.let₂ (.var 0) (.br 0 (.unit : Tm Φ))) (.br 0 .unit) [Silmaril.unit] := by
  let h : ValueBranches [product A B] (.let₂ (.var 0) (.br 0 (.unit : Tm Φ))) [Silmaril.unit] :=
    .let₂ (.var (i := 0) rfl : Tm.HasType [product A B] (.var 0) (product A B))
      (.br rfl .unit)
  apply (Paper.product_variable_eta_iff (i := 0) (A := A) (B := B)
    (rfl : At [product A B] 0 (product A B)) h.hasType (.br rfl .unit)).mp
  change Eqv [B, A, product A B] (.let₂ (.pair (.var 1) (.var 0)) (.br 0 (.unit : Tm Φ)))
    (.br 0 .unit) [Silmaril.unit]
  exact .productBeta (.let₂Beta (.var (i := 1) rfl : Tm.BranchValue _ _ A)
    (.var (i := 0) rfl : Tm.BranchValue _ _ B) (.br rfl .unit))

private theorem fst_discard (A B : τ) :
    fstArrow (Φ := Φ) A B ≫ discardArrow A = discardArrow (product A B) := by
  unfold fstArrow discardArrow
  rw [ofRegion_comp _ _ (seqValueBranches (productFstBranches A B) (.br rfl .unit))]
  exact (ofRegion_eq_iff _ _).2 (guarded_discard A B)

private theorem snd_discard (A B : τ) :
    sndArrow (Φ := Φ) A B ≫ discardArrow B = discardArrow (product A B) := by
  unfold sndArrow discardArrow
  rw [ofRegion_comp _ _ (seqValueBranches (productSndBranches A B) (.br rfl .unit))]
  exact (ofRegion_eq_iff _ _).2 (guarded_discard A B)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectedValueProduct.Default

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectedValueProduct

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.Extension.Singleton CategoryTheory
open CfgEta.TypeCategory (productFstBranches productSndBranches)

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

set_option hygiene false in
local notation "P" => projection Seed
set_option hygiene false in
local notation "obj" => ofType (Φ := Φ) Seed

set_option backward.isDefEq.respectTransparency false in
theorem pairing_reconstruct {X A B : τ} {p : obj X ⟶ obj (product A B)}
    (hp : ∃ p₀ : Paper.TypeCategory.ofType (Φ := Φ) X ⟶ Paper.TypeCategory.ofType (product A B),
      Paper.TypeCategory.CentralCopies p₀ ∧ (P).map p₀ = p) :
    pairArrows Seed (p ≫ productFst Seed A B) (p ≫ productSnd Seed A B) = p := by
  obtain ⟨p₀, hp₀, rfl⟩ := hp
  rw [← (P).map_comp, ← (P).map_comp, ← map_pairArrows]
  exact congrArg (P).map (Paper.TypeCategory.pairArrows_projections_of_preservesDiagonal p₀ hp₀.2)

set_option backward.isDefEq.respectTransparency false in
private theorem diagonal_fst (X : τ) :
    diagonalArrow Seed (obj X) ≫ productFst Seed X X = 𝟙 (obj X) := by
  rw [← (P).map_id]
  exact ((P).map_comp _ _).symm.trans (congrArg (P).map (Default.diagonal_fst X))

set_option backward.isDefEq.respectTransparency false in
private theorem diagonal_snd (X : τ) :
    diagonalArrow Seed (obj X) ≫ productSnd Seed X X = 𝟙 (obj X) := by
  rw [← (P).map_id]
  exact ((P).map_comp _ _).symm.trans (congrArg (P).map (Default.diagonal_snd X))

set_option backward.isDefEq.respectTransparency false in
private theorem discard_fst (A B : τ) :
    whiskerLeft Seed (obj A) (discardArrow Seed B) ≫ productFst Seed A Silmaril.unit = productFst Seed A B := by
  exact ((P).map_comp _ _).symm.trans
    (congrArg (P).map (Default.whiskerLeft_discard_fst A B))

set_option backward.isDefEq.respectTransparency false in
private theorem discard_snd (A B : τ) :
    whiskerRight Seed (discardArrow Seed A) (obj B) ≫ productSnd Seed Silmaril.unit B = productSnd Seed A B := by
  exact ((P).map_comp _ _).symm.trans
    (congrArg (P).map (Default.whiskerRight_discard_snd A B))

set_option backward.isDefEq.respectTransparency false in
private theorem active_fst {X A : τ} (B : τ) (f : obj X ⟶ obj A) :
    whiskerRight Seed f (obj B) ≫ productFst Seed A B = productFst Seed X B ≫ f := by
  obtain ⟨f, rfl⟩ := (P).map_surjective f
  exact ((P).map_comp _ _).symm.trans ((congrArg (P).map
    (Paper.TypeCategory.whiskerRight_productFst B f)).trans ((P).map_comp _ _))

set_option backward.isDefEq.respectTransparency false in
private theorem active_snd {X B : τ} (A : τ) (g : obj X ⟶ obj B) :
    whiskerLeft Seed (obj A) g ≫ productSnd Seed A B = productSnd Seed A X ≫ g := by
  obtain ⟨g, rfl⟩ := (P).map_surjective g
  exact ((P).map_comp _ _).symm.trans ((congrArg (P).map
    (Paper.TypeCategory.whiskerLeft_productSnd A g)).trans ((P).map_comp _ _))

set_option backward.isDefEq.respectTransparency false in
theorem pairing_fst_of_discard {X A B : τ} (f : obj X ⟶ obj A) (g : obj X ⟶ obj B)
    (hg : g ≫ discardArrow Seed B = discardArrow Seed X) :
    pairArrows Seed f g ≫ productFst Seed A B = f := by
  unfold pairArrows
  simp only [Category.assoc]
  rw [← discard_fst Seed A B, ← Category.assoc (whiskerLeft Seed (obj A) g),
    ← (whiskerLeftFunctor Seed (obj A)).map_comp, hg, discard_fst Seed A X,
    active_fst Seed X f, ← Category.assoc, diagonal_fst Seed X, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
theorem pairing_snd_of_discard {X A B : τ} (f : obj X ⟶ obj A) (g : obj X ⟶ obj B)
    (hf : f ≫ discardArrow Seed A = discardArrow Seed X) :
    pairArrows Seed f g ≫ productSnd Seed A B = g := by
  have hu : Tm.BranchValue [A] (Tm.unit : Tm Φ) Silmaril.unit := .unit
  have hc : WhiskerCentral Seed (discardArrow Seed A) := (map_centralCopies Seed
    ⟨Paper.TypeCategory.whiskerCentral_ofRegion_branchValue hu,
      Paper.TypeCategory.pairArrows_copy_branchValue hu⟩).1
  have swap := (hc g).1
  unfold pairArrows
  simp only [Category.assoc]
  rw [← discard_snd Seed A B, ← Category.assoc (whiskerLeft Seed (obj A) g),
    ← swap]
  simp only [Category.assoc]
  rw [← Category.assoc (whiskerRight Seed f (obj X)),
    ← (whiskerRightFunctor Seed (obj X)).map_comp, hf, active_snd Seed Silmaril.unit g,
    ← Category.assoc (whiskerRight Seed (discardArrow Seed X) (obj X)), discard_snd Seed X X,
    ← Category.assoc, diagonal_snd Seed X, Category.id_comp]


theorem fst_discard (A B : τ) :
    productFst Seed A B ≫ discardArrow Seed A = discardArrow Seed (product A B) :=
  ((P).map_comp _ _).symm.trans (congrArg (P).map (Default.fst_discard A B))

theorem snd_discard (A B : τ) :
    productSnd Seed A B ≫ discardArrow Seed B = discardArrow Seed (product A B) :=
  ((P).map_comp _ _).symm.trans (congrArg (P).map (Default.snd_discard A B))

variable {ε : Type w} [HasEff Φ ε] (pe : ε)

set_option backward.isDefEq.respectTransparency false in
private theorem projected_pairing_branchValue {X A B : τ} {a b : Tm Φ}
    (ha : Tm.BranchValue [X] a A) (hb : Tm.BranchValue [X] b B) :
    pairArrows Seed (ofRegion Seed (.br (ℓ := 0) rfl ha)) (ofRegion Seed (.br (ℓ := 0) rfl hb)) =
      ofRegion Seed (.br (ℓ := 0) rfl (.pair ha hb)) := by
  rw [← map_pairArrows]
  exact congrArg (P).map (Paper.TypeCategory.pairArrows_branchValue ha hb)

set_option backward.isDefEq.respectTransparency false in
theorem projected_branchValue_mem {X A : τ} {a : Tm Φ} (ha : Tm.BranchValue [X] a A) :
    ProjectedCopyingReturn Seed pe (ofRegion Seed (.br (ℓ := 0) rfl ha)) := by
  have h := Paper.TypeCategory.copyingPureReturn_branchValue pe ha
  exact ⟨⟨_, h.1.1, rfl⟩, ⟨_, ⟨h.1.2, h.2⟩, rfl⟩⟩

set_option backward.isDefEq.respectTransparency false in
private theorem projected_branchValue_discard {X A : τ} {a : Tm Φ} (ha : Tm.BranchValue [X] a A) :
    ofRegion Seed (.br (ℓ := 0) rfl ha) ≫ discardArrow Seed A = discardArrow Seed X :=
  ((P).map_comp _ _).symm.trans (congrArg (P).map (Paper.TypeCategory.discard_comp_branchValue ha))

set_option backward.isDefEq.respectTransparency false in
theorem projections_ext {X A B : τ} {p q : obj X ⟶ obj (product A B)}
    (hp : ProjectedCopyingReturn Seed pe p) (hq : ProjectedCopyingReturn Seed pe q)
    (hl : p ≫ productFst Seed A B = q ≫ productFst Seed A B) (hr : p ≫ productSnd Seed A B = q ≫ productSnd Seed A B) :
    p = q :=
  (pairing_reconstruct Seed hp.2).symm.trans
    ((congrArg₂ (pairArrows Seed) hl hr).trans (pairing_reconstruct Seed hq.2))

set_option backward.isDefEq.respectTransparency false in
theorem constructor_pair_existsUnique {X A B : τ} {a b : Tm Φ}
    (ha : Tm.BranchValue [X] a A) (hb : Tm.BranchValue [X] b B) :
    ∃! p : obj X ⟶ obj (product A B),
      ProjectedCopyingReturn Seed pe p ∧
        p ≫ productFst Seed A B = ofRegion Seed (.br (ℓ := 0) rfl ha) ∧
        p ≫ productSnd Seed A B = ofRegion Seed (.br (ℓ := 0) rfl hb) := by
  let p := ofRegion Seed (.br (ℓ := 0) rfl (Tm.BranchValue.pair ha hb))
  have hmem : ProjectedCopyingReturn Seed pe p := projected_branchValue_mem Seed pe (.pair ha hb)
  have hp := projected_pairing_branchValue Seed ha hb
  have hl : p ≫ productFst Seed A B = _ := hp ▸ pairing_fst_of_discard Seed _ _
    (projected_branchValue_discard Seed hb)
  have hr : p ≫ productSnd Seed A B = _ := hp ▸ pairing_snd_of_discard Seed _ _
    (projected_branchValue_discard Seed ha)
  exact ⟨p, ⟨hmem, hl, hr⟩, fun q hq => projections_ext Seed pe hq.1 hmem
    (hq.2.1.trans hl.symm) (hq.2.2.trans hr.symm)⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectedValueProduct

module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.Selected.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.BinaryLet.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Singleton.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Direct.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Naturality.Thms
import Silmaril.Semantics.Categories.Freyd.CentralUnit.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution.Renaming.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution.Singleton.Thms

/-! # Denotation of the selected product-return annotations -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SelectedProductDenotation

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithComputedProductProducers.Intrinsic
open Paper.SingletonReification.BinaryLet (literal_let₂_selected)
open CategoryTheory CategoryTheory.Limits
open Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel
  extend_comp extend_map extend_postmap pair_pre_map retainLeft_pre_map bind_pre_map pair_maps_eq_map_lift
  bind_assoc_capture duplicate_central_of_tensor_eqToIso)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (extend retainLeft retainedContext duplicate)
open CartesianMonoidalCategory (fst snd lift toUnit)
open CfgEta.TypeCategory (returnRegion returnRegion_typed)
open SingletonDispatcher (labelInject_payload)
open scoped MonoidalCategory

local notation "bindArrow" => Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind
local notation "pairArrow" => Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.pair

universe u v m n x y

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type m} {C : Type n} [Category.{x} V] [Category.{y} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ]

open MonoidalCategory

omit [FreydCategory.CentralUnit J] in
private theorem pair_eq_ordered {R A B : V}
    (f : J.obj R ⟶ J.obj A) (g : J.obj R ⟶ J.obj B) :
    pairArrow J f g = extend J f ≫ J.map (BraidedCategory.braiding R A).hom ≫ retainLeft J (R := A) g := by
  have tail : lift (fst (R ⊗ A) B ≫ snd R A) (snd (R ⊗ A) B) = snd R A ▷ B := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have swap : lift (𝟙 (R ⊗ A)) (fst R A) ≫ (snd R A ▷ R) = (BraidedCategory.braiding R A).hom := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  unfold Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.pair
    Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind retainedContext
  rw [extend_comp, extend_map, tail]
  simp only [Category.assoc]
  rw [← retainLeft_pre_map J (snd R A), ← J.map_comp_assoc, swap]

omit [FreydCategory.CentralUnit J] in
theorem orderedPair_eq_pair {X A B : τ} (f : J.obj (M.obj X) ⟶ J.obj (M.obj A))
    (g : J.obj (M.obj X) ⟶ J.obj (M.obj B)) :
    orderedPair J M f g = pairArrow J f g ≫ J.map (M.productIso A B).inv := by
  rw [pair_eq_ordered J]
  simp only [orderedPair, Category.assoc]

omit [FreydCategory.CentralUnit J] in
private theorem input_denotes (X : τ) :
    Denotes J M (.var (i := 0) rfl : Tm.HasType [X] (.var 0 : Tm Φ) X)
      (J.map (λ_ (M.obj X)).hom) := by
  simpa only [lookup, ctxObj, CartesianMonoidalCategory.leftUnitor_hom] using
    (Denotes.var (J := J) (M := M) (Φ := Φ) (i := 0) (rfl : At [X] 0 X))

private theorem extend_snd {R A : V} (f : J.obj R ⟶ J.obj A) :
    extend J f ≫ J.map (snd R A) = f := by
  simp only [extend, PremonoidalCategory.leftTensor, PremonoidalCategory.id_whiskerRight,
    Category.id_comp, Category.assoc]
  rw [FreydCategory.whiskerLeft_snd J R f, ← J.map_comp_assoc]
  simp [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.duplicate]

private theorem bind_exit {R A B : V} (f : J.obj R ⟶ J.obj A) (k : A ⟶ B) :
    bindArrow J f (J.map (snd R A) ≫ J.map k) = f ≫ J.map k := by
  unfold Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind
  rw [← Category.assoc, extend_snd J]

private noncomputable def unpackInput (A B : τ) :
    ctxObj M [product A B] ⟶ ctxObj M [B, A, product A B] :=
  let E := ctxObj M [product A B]
  lift (𝟙 E) (λ_ (M.obj (product A B))).hom ≫
    ((𝟙 E) ⊗ₘ (M.productIso A B).hom) ≫ (ctxPairIso M [product A B] A B).hom

set_option backward.isDefEq.respectTransparency false in
omit [SymmetricCategory V] [DistributiveTensor V] in
private theorem unpack_fst (A B : τ) :
    unpackInput M A B ≫ lookup M 1 (rfl : At [B, A, product A B] 1 A) =
      (λ_ (M.obj (product A B))).hom ≫ (M.productIso A B).hom ≫ fst (M.obj A) (M.obj B) := by
  let E := ctxObj M [product A B]
  change _ ≫ (fst (E ⊗ M.obj A) (M.obj B) ≫ snd E (M.obj A)) = _
  have h : (ctxPairIso M [product A B] A B).hom ≫ fst (E ⊗ M.obj A) (M.obj B) ≫ snd E (M.obj A) =
      snd E (M.obj A ⊗ M.obj B) ≫ fst (M.obj A) (M.obj B) :=
    CartesianMonoidalCategory.associator_inv_fst_snd E (M.obj A) (M.obj B)
  simp only [unpackInput, Category.assoc, h]
  dsimp only [E]
  rw [CartesianMonoidalCategory.tensorHom_snd_assoc, CartesianMonoidalCategory.lift_snd_assoc]

set_option backward.isDefEq.respectTransparency false in
omit [SymmetricCategory V] [DistributiveTensor V] in
private theorem unpack_snd (A B : τ) :
    unpackInput M A B ≫ lookup M 0 (rfl : At [B, A, product A B] 0 B) =
      (λ_ (M.obj (product A B))).hom ≫ (M.productIso A B).hom ≫ snd (M.obj A) (M.obj B) := by
  let E := ctxObj M [product A B]
  change _ ≫ snd (E ⊗ M.obj A) (M.obj B) = _
  have h : (ctxPairIso M [product A B] A B).hom ≫ snd (E ⊗ M.obj A) (M.obj B) =
      snd E (M.obj A ⊗ M.obj B) ≫ snd (M.obj A) (M.obj B) :=
    CartesianMonoidalCategory.associator_inv_snd E (M.obj A) (M.obj B)
  simp only [unpackInput, Category.assoc, h]
  dsimp only [E]
  rw [CartesianMonoidalCategory.tensorHom_snd_assoc, CartesianMonoidalCategory.lift_snd_assoc]

set_option backward.isDefEq.respectTransparency false in
omit [FreydCategory.CentralUnit J] in
private theorem unpack_selected {A B D : τ} {b : Tm Φ}
    {hb : Tm.HasType [B, A, product A B] b D}
    {f : J.obj (ctxObj M [B, A, product A B]) ⟶ J.obj (M.obj D)}
    (d : Denotes J M hb f) :
    Denotes J M (.let₂ (.var (i := 0) rfl) hb) (J.map (unpackInput M A B) ≫ f) := by
  simpa only [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind, extend_map,
    unpackInput, Category.assoc, ← J.map_comp_assoc] using
      Denotes.let₂ (input_denotes J M (product A B)) d

set_option backward.isDefEq.respectTransparency false in
omit [FreydCategory.CentralUnit J] in
private theorem destructure_selected {A B D : τ} {t : Tm Φ}
    {ht : Tm.HasType [product A B] t D}
    {f : J.obj (M.obj (product A B)) ⟶ J.obj (M.obj D)}
    (d : Denotes J M ht (J.map (λ_ (M.obj (product A B))).hom ≫ f)) :
    Denotes J M (Paper.RetainedLet.unpackTerm_typed (Paper.PackedBody.applyPackedTerm_typed ht))
      (J.map (λ_ (M.obj (product A B))).hom ≫ f) := by
  let P := product A B
  let pack := lift (lookup M 1 (rfl : At [B, A, P] 1 A)) (lookup M 0 (rfl : At [B, A, P] 0 B)) ≫
    (M.productIso A B).inv
  let ρ := Silmaril.DeBruijn.lift (Silmaril.DeBruijn.lift Nat.succ)
  let σ : Nat → Tm Φ := Tm.consSubst (.pair (.var 1) (.var 0)) (Tm.var ∘ (Nat.succ ∘ Nat.succ))
  have dp : Denotes J M (.pair (.var (i := 1) rfl) (.var (i := 0) rfl) :
      Tm.HasType [B, A, P] ((σ 0).rename ρ) P) (J.map pack) := by
    simpa only [pair_maps_eq_map_lift, ← J.map_comp, pack] using
      Denotes.pair (Denotes.var (J := J) (M := M) (Φ := Φ) (rfl : At [B, A, P] 1 A))
        (Denotes.var (rfl : At [B, A, P] 0 B))
  have bodyGraph := d.substSingleton J M (fun i => (σ i).rename ρ) dp
  rw [← Tm.rename_subst] at bodyGraph
  obtain ⟨_, db⟩ := bodyGraph
  have cancel : unpackInput M A B ≫ pack = (λ_ (M.obj (product A B))).hom := by
    simp only [pack, ← Category.assoc _ _ (M.productIso A B).inv,
      CartesianMonoidalCategory.comp_lift, unpack_fst, unpack_snd]
    rw [← CartesianMonoidalCategory.comp_lift, ← CartesianMonoidalCategory.comp_lift]
    simp
  have du := unpack_selected J M db
  simpa only [Category.assoc, ← J.map_comp_assoc, Iso.inv_hom_id, Category.comp_id, cancel, P] using du

set_option backward.isDefEq.respectTransparency false in
theorem term_selected {X D : τ} (t : Term Φ X D) :
    Denotes J M t.elaborate.property (J.map (λ_ (M.obj X)).hom ≫ t.targetArrow J M) := by
  induction t with
  | @input X => simpa only [Term.elaborate, Term.targetArrow, Category.comp_id] using input_denotes J M _
  | @unit X =>
    have hunit : (λ_ (M.obj X)).hom ≫ toUnit (M.obj X) = toUnit (ctxObj M [X]) :=
      CartesianMonoidalCategory.isTerminalTensorUnit.hom_ext _ _
    simp only [Term.elaborate, Term.targetArrow, ← J.map_comp, reassoc_of% hunit]
    exact .unit
  | call p a ih =>
    simpa only [Term.elaborate, Term.targetArrow, Category.assoc] using Denotes.op ih
  | @pair X A B a b ia ib =>
    have d := Denotes.pair ia ib
    rw [pair_pre_map J ((λ_ (M.obj X)).hom), pair_eq_ordered J] at d
    simpa only [Term.elaborate, Term.targetArrow, orderedPair, Category.assoc] using d
  | @seq X A D a b ia ib =>
    let k := snd (ctxObj M [X]) (M.obj A) ≫ (λ_ (M.obj A)).inv
    let ρ := (Ren.wk [] X).lift A
    have hk : ∀ ⦃i B⦄ (hi : At [A] i B), k ≫ lookup M i hi = lookup M _ (ρ hi) := by
      intro i B hi
      cases i with
      | zero =>
        cases Option.some.inj hi
        change k ≫ snd (𝟙_ V) (M.obj A) = snd (ctxObj M [X]) (M.obj A)
        dsimp only [k]
        rw [← CartesianMonoidalCategory.leftUnitor_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      | succ i => simp [At] at hi
    have db := ib.rename J M ρ hk
    have cancel : J.map (λ_ (M.obj A)).inv ≫ J.map (λ_ (M.obj A)).hom = 𝟙 _ := by
      rw [← J.map_comp, Iso.inv_hom_id, J.map_id]
    simp only [k, J.map_comp_assoc, reassoc_of% cancel] at db
    have both := Denotes.let₁ ia db
    simpa only [Term.elaborate, Term.targetArrow, Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind,
      reassoc_of% (extend_snd J _), Category.assoc] using both
  | fst A B =>
    have d := unpack_selected J M (Denotes.var (J := J) (M := M) (Φ := Φ)
      (rfl : At [B, A, product A B] 1 A))
    simpa only [Term.elaborate, Term.targetArrow, ← J.map_comp, unpack_fst] using d
  | snd A B =>
    have d := unpack_selected J M (Denotes.var (J := J) (M := M) (Φ := Φ)
      (rfl : At [B, A, product A B] 0 B))
    simpa only [Term.elaborate, Term.targetArrow, ← J.map_comp, unpack_snd] using d
  | destructure _ _ body ih =>
    exact destructure_selected J M ih

/-- A lowered return forwards a variable to its continuation through unary binders. -/
private inductive ReturnChain : Region Φ → Prop where
  | br (label i : Nat) : ReturnChain (.br label (.var i))
  | let₁ {a : Tm Φ} {r : Region Φ} : ReturnChain r → ReturnChain (.let₁ a r)

private theorem ReturnChain.rename {r : Region Φ} (h : ReturnChain r) (ρ : Nat → Nat) :
    ReturnChain (r.renameVars ρ) := by
  induction h generalizing ρ with
  | br label i => exact .br label (ρ i)
  | let₁ _ ih => exact .let₁ (ih (Silmaril.DeBruijn.lift ρ))

private theorem ReturnChain.subst {r : Region Φ} (h : ReturnChain r) (σ : Nat → Tm Φ)
    (hσ : ∀ i, ∃ j, σ i = .var j) : ReturnChain (r.substVars σ) := by
  induction h generalizing σ with
  | br label i =>
    obtain ⟨j, hj⟩ := hσ i
    change ReturnChain (.br label (σ i))
    rw [hj]
    exact .br label j
  | let₁ _ ih =>
    apply ReturnChain.let₁ (ih _ ?_)
    intro i
    cases i with
    | zero => exact ⟨0, rfl⟩
    | succ i =>
      obtain ⟨j, hj⟩ := hσ i
      exact ⟨j + 1, by simp [Tm.liftSubst, hj, Tm.rename]⟩

private theorem ReturnChain.lsubst {r : Region Φ} (h : ReturnChain r) (σ : Nat → Region Φ)
    (hσ : ∀ i, ReturnChain (σ i)) : ReturnChain (r.lsubst σ) := by
  induction h generalizing σ with
  | br label i =>
    apply (hσ label).subst
    intro n
    cases n with
    | zero => exact ⟨i, rfl⟩
    | succ n => exact ⟨n, rfl⟩
  | let₁ _ ih => exact .let₁ (ih _ (fun i => (hσ i).rename _))

private theorem lowered_chain (a : Tm Φ) : ReturnChain (returnRegion a) := by
  induction a with
  | let₁ a b ia ib => exact ia.lsubst _ (fun _ => ib)
  | _ => exact .let₁ (.br 0 0)

variable (shared : ∀ E S : V, ∃ h : J.obj E ⊗ J.obj S = J.obj (E ⊗ S),
  Functor.StrongPremonoidal.tensorIso (J := J) E S = eqToIso h)

include shared in
set_option backward.isDefEq.respectTransparency false in
omit [FreydCategory.CentralUnit J] in
private theorem lsubst_selected {Γ L K : VCtx τ} {r : Region Φ} {hr : Region.HasType Γ r L}
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)}
    (df : RegionDenotes J M hr f) (chain : ReturnChain r) {σ : Nat → Region Φ}
    {k : J.obj (ctxObj M Γ ⊗ labelObj M L) ⟶ J.obj (labelObj M K)}
    (dk : ContinuationDenotes J M σ k) :
    ∃ ht : Region.HasType Γ (r.lsubst σ) K, RegionDenotes J M ht (bindArrow J f k) := by
  induction df generalizing K σ with
  | br da =>
    cases chain
    cases da with
    | var hi => exact RegionDenotes.branch_lsubst J M dk (.var hi) _
  | let₁ da _ ih =>
    cases chain with
    | let₁ body =>
      obtain ⟨_, db⟩ := ih body (dk.weakenCapture J M _)
      have central (E : V) : PremonoidalCategory.IsCentral (J.map (duplicate E) ≫
          (Functor.StrongPremonoidal.tensorIso (J := J) E E).inv) := by
        obtain ⟨h, e⟩ := shared E E
        exact duplicate_central_of_tensor_eqToIso J E h e
      rw [bind_assoc_capture J (central _)]
      exact ⟨_, .let₁ da db⟩
  | _ => cases chain

set_option backward.isDefEq.respectTransparency false in
private theorem bound_selected {Γ : VCtx τ} {D : τ} {a : Tm Φ} {ht : Tm.HasType Γ a D}
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj D)} (dt : Denotes J M ht f) :
    RegionDenotes J M (.let₁ ht (.br (L := [D]) (ℓ := 0) rfl (.var (i := 0) rfl)))
      (f ≫ J.map (labelInject M 0 (L := [D]) rfl)) := by
  have d := RegionDenotes.let₁ dt
    (RegionDenotes.br (h := (rfl : At [D] 0 D))
      (Denotes.var (i := 0) (rfl : At (D :: Γ) 0 D)))
  simpa only [lookup, ctxObj, bind_exit J] using d

include shared in
set_option backward.isDefEq.respectTransparency false in
omit [FreydCategory.CentralUnit J] in
private theorem lowered_let_selected {Γ : VCtx τ} {A B : τ} {a b : Tm Φ}
    {ha : Tm.HasType Γ a A} {hb : Tm.HasType (A :: Γ) b B}
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj A)}
    {g : J.obj (ctxObj M (A :: Γ)) ⟶ J.obj (M.obj B)}
    (da : RegionDenotes J M (returnRegion_typed ha).hasType
      (f ≫ J.map (labelInject M 0 (L := [A]) rfl)))
    (db : RegionDenotes J M (returnRegion_typed hb).hasType
      (g ≫ J.map (labelInject M 0 (L := [B]) rfl))) :
    RegionDenotes J M (returnRegion_typed (.let₁ ha hb)).hasType
      (bindArrow J f g ≫ J.map (labelInject M 0 (L := [B]) rfl)) := by
  let E := ctxObj M Γ
  let k := J.map (E ◁ singletonLabelPayload M A) ≫ g ≫ J.map (labelInject M 0 (L := [B]) rfl)
  have dk : ContinuationDenotes J M (Γ := Γ) (L := [A]) (K := [B]) (fun _ => returnRegion b) k := by
    intro i T hi
    cases i with
    | zero =>
      cases Option.some.inj hi
      refine ⟨(returnRegion_typed hb).hasType, ?_⟩
      have cancel : J.map ((𝟙 E) ⊗ₘ labelInject M 0 (L := [A]) rfl) ≫
          J.map (E ◁ singletonLabelPayload M A) = 𝟙 _ := by
        rw [← J.map_comp, MonoidalCategory.id_tensorHom, ← MonoidalCategory.whiskerLeft_comp,
          labelInject_payload, MonoidalCategory.whiskerLeft_id, J.map_id]
      dsimp only [k, E]
      dsimp only [E] at cancel
      rw [reassoc_of% cancel]
      exact db
    | succ i => simp [At] at hi
  obtain ⟨_, d⟩ := lsubst_selected J M shared da (lowered_chain a) dk
  simpa only [k, E, Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind, extend_postmap,
    Category.assoc, ← J.map_comp_assoc, ← MonoidalCategory.whiskerLeft_comp,
    labelInject_payload, MonoidalCategory.whiskerLeft_id, J.map_id, Category.id_comp] using d

include shared in
set_option backward.isDefEq.respectTransparency false in
private theorem lowered_selected {Γ : VCtx τ} {D : τ} {a : Tm Φ} {ht : Tm.HasType Γ a D}
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj D)} (d : Denotes J M ht f) :
    RegionDenotes J M (returnRegion_typed ht).hasType (f ≫ J.map (labelInject M 0 (L := [D]) rfl)) := by
  induction a generalizing Γ D with
  | let₁ a b ia ib =>
    cases d with
    | let₁ da db =>
      rename_i A fa ha fb hb
      exact lowered_let_selected J M shared (ha := ha) (hb := hb) (ia da) (ib db)
  | _ => exact bound_selected J M d

set_option backward.isDefEq.respectTransparency false in
include shared in
theorem program_selected {X D : τ} (p : Program Φ X D) :
    RegionDenotes J M p.elaborate.property.hasType
      (J.map (λ_ (M.obj X)).hom ≫ p.targetArrow J M ≫ J.map (labelInject M 0 (L := [D]) rfl)) := by
  induction p with
  | returned t =>
    simpa only [Program.elaborate, Program.targetArrow, Category.assoc] using
      lowered_selected J M shared (term_selected J M t)
  | branchInput =>
    simpa only [Program.elaborate, Program.targetArrow, Category.id_comp] using
      RegionDenotes.br (h := (rfl : At [_] 0 _)) (input_denotes J M _)
  | @let₂ X D A B a body ih =>
    let P := product A B
    have step := literal_let₂_selected J M a.elaborate.property body.elaborate.property (term_selected J M a) ih
    have cancel : J.map (λ_ (M.obj (product X P))).inv ≫ J.map (λ_ (M.obj (product X P))).hom = 𝟙 _ := by
      rw [← J.map_comp, Iso.inv_hom_id, J.map_id]
    dsimp only [P] at cancel
    simp only [reassoc_of% cancel] at step
    have bindChange := bind_pre_map J ((λ_ (M.obj X)).hom) (a.targetArrow J M)
      (J.map (M.productIso X P).inv ≫ body.targetArrow J M ≫ J.map (labelInject M 0 (L := [D]) rfl))
    simp only [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind] at bindChange
    simp only [Program.elaborate, Program.targetArrow, Category.assoc]
    rw [← bindChange]
    simpa only [Category.assoc] using step

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SelectedProductDenotation

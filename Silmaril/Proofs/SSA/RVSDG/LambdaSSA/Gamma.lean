module

public import Silmaril.SSA.RVSDG.LambdaSSA.Gamma.Categorical.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.Selector.Thms

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Proofs

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory (fst snd lift toUnit)
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA (Tm)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical (ctxObj lookup Denotes)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (caseWithContext splitMapCoprod)

universe u v d h c k
variable {τ : Type u} {Φ : Type v} [TypeFormers τ] [HasTy Φ τ]

theorem switchTyping {Γ : List τ} {A : τ} (n : Nat) (p : Port Γ (selectorType n))
    (arms : Fin (n + 1) → Port Γ A) : Tm.HasType Γ (switch (Φ := Φ) n p arms) A := by
  induction n generalizing Γ with
  | zero => exact .var (index_at (arms 0))
  | succ n ih =>
    exact .case (.var (index_at p)) (.var (index_at (.tail (arms 0)))) (ih .head fun i => .tail (arms i.succ))

section Categories

variable {D : Type d} {C : Type c} [Category.{h} D] [CartesianMonoidalCategory D]
  [HasFiniteCoproducts D] [SymmetricCategory D] [DistributiveTensor D]
  [Category.{k} C] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts C] [DistributivePremonoidalCategory C]
  (J : D ⥤ C) [DistributiveFreydCategory J]

noncomputable def valueCase {R A B Y : D}
    (q : R ⟶ A ⨿ B) (l : R ⊗ A ⟶ Y) (r : R ⊗ B ⟶ Y) : R ⟶ Y :=
  lift (𝟙 _) q ≫ (DistributiveTensor.leftIso R A B).inv ≫ coprod.desc l r

private theorem copair_map {A B Y : D} (l : A ⟶ Y) (r : B ⟶ Y) :
    splitMapCoprod J A B ≫ coprod.desc (J.map l) (J.map r) = J.map (coprod.desc l r) := by
  apply (cancel_epi (coprodComparison J A B)).mp
  simp only [splitMapCoprod, IsIso.hom_inv_id_assoc]
  apply coprod.hom_ext
  · simp [← J.map_comp]
  · simp [← J.map_comp]

theorem valueCase_map {R A B Y : D}
    (q : R ⟶ A ⨿ B) (l : R ⊗ A ⟶ Y) (r : R ⊗ B ⟶ Y) :
    caseWithContext J (J.map q) (J.map l) (J.map r) = J.map (valueCase q l r) := by
  unfold caseWithContext valueCase
  rw [copair_map J, ← J.map_comp, Categorical.freyd_bind_map]

omit [SymmetricCategory D] in
private theorem case_left {X R A B Y : D} (env : X ⟶ R) (q : R ⟶ A ⨿ B)
    (l : R ⊗ A ⟶ Y) (r : R ⊗ B ⟶ Y) (a : X ⟶ A)
    (eq : env ≫ q = a ≫ coprod.inl) :
    env ≫ valueCase q l r = lift env a ≫ l := by
  have step : (R ◁ (coprod.inl : A ⟶ A ⨿ B)) ≫ (DistributiveTensor.leftIso R A B).inv =
      coprod.inl := by
    rw [← DistributiveTensor.inl_leftHom]
    change (_ ≫ (DistributiveTensor.leftIso R A B).hom) ≫ _ = _
    simp
  simp only [valueCase, ← Category.assoc env, CartesianMonoidalCategory.comp_lift, Category.comp_id, eq]
  rw [← CartesianMonoidalCategory.lift_whiskerLeft, Category.assoc, ← Category.assoc (R ◁ _), step]
  simp

omit [SymmetricCategory D] in
private theorem case_right {X R A B Y : D} (env : X ⟶ R) (q : R ⟶ A ⨿ B)
    (l : R ⊗ A ⟶ Y) (r : R ⊗ B ⟶ Y) (b : X ⟶ B)
    (eq : env ≫ q = b ≫ coprod.inr) :
    env ≫ valueCase q l r = lift env b ≫ r := by
  have step : (R ◁ (coprod.inr : B ⟶ A ⨿ B)) ≫ (DistributiveTensor.leftIso R A B).inv =
      coprod.inr := by
    rw [← DistributiveTensor.inr_leftHom]
    change (_ ≫ (DistributiveTensor.leftIso R A B).hom) ≫ _ = _
    simp
  simp only [valueCase, ← Category.assoc env, CartesianMonoidalCategory.comp_lift, Category.comp_id, eq]
  rw [← CartesianMonoidalCategory.lift_whiskerLeft, Category.assoc, ← Category.assoc (R ◁ _), step]
  simp

variable (M : TypeModel τ D) [InstructionModel J M Φ]

set_option backward.isDefEq.respectTransparency false in
theorem switch_sound {Γ : List τ} {A : τ} (n : Nat) (p : Port Γ (selectorType n))
    (arms : Fin (n + 1) → Port Γ A) :
    ∃ f : ctxObj M Γ ⟶ M.obj A, Denotes J M (switchTyping (Φ := Φ) n p arms) (J.map f) ∧
      ∀ {X : D} (env : X ⟶ ctxObj M Γ) (i : Fin (n + 1)),
        env ≫ lookup M (index p) (index_at p) = toUnit X ≫ selectorTag M n i →
        env ≫ f = env ≫ lookup M (index (arms i)) (index_at (arms i)) := by
  induction n generalizing Γ with
  | zero =>
    exact ⟨lookup M (index (arms 0)) (index_at (arms 0)), .var _, fun _ i _ => by rw [Fin.eq_zero i]⟩
  | succ n ih =>
    obtain ⟨right, dr, hr⟩ := ih (Γ := selectorType n :: Γ) .head (fun i => .tail (arms i.succ))
    let left := lookup M (index (.tail (arms 0) : Port (unit :: Γ) A)) (index_at (.tail (arms 0)))
    let read := lookup M (index p) (index_at p)
    let iso := M.coprodIso unit (selectorType n)
    refine ⟨valueCase (read ≫ iso.hom) left right, ?_, ?_⟩
    · rw [← valueCase_map J, J.map_comp]
      exact .case (.var _) (.var _) dr
    · intro X env i
      refine Fin.cases ?_ (fun j => ?_) i
      · intro hi
        have htag : env ≫ (read ≫ iso.hom) = (toUnit X ≫ M.unitIso.inv) ≫ coprod.inl := by
          rw [← Category.assoc, hi]
          simp [selectorTag, iso, selectorType, Category.assoc]
        rw [case_left env _ _ _ _ htag]
        change lift env _ ≫ (fst _ _ ≫ lookup M (index (arms 0)) (index_at (arms 0))) = _
        simp
      · intro hi
        have htag : env ≫ (read ≫ iso.hom) = (toUnit X ≫ selectorTag M n j) ≫ coprod.inr := by
          rw [← Category.assoc, hi]
          simp [selectorTag, iso, selectorType, Category.assoc]
        rw [case_right env _ _ _ _ htag, hr _ j]
        · change lift env _ ≫ (fst _ _ ≫ lookup M (index (arms j.succ)) (index_at (arms j.succ))) = _
          simp
        · change lift env (toUnit X ≫ selectorTag M n j) ≫ snd _ _ = _
          simp

section Wiring

variable (m : Categorical.Model (Opcode (τ := τ) Φ) D)

set_option backward.isDefEq.respectTransparency false in
omit [TypeFormers τ] [HasFiniteCoproducts D] [SymmetricCategory D] [DistributiveTensor D] in
private theorem readWiresOf {X : D} {args : Ports (Ty τ)} {past : List (Ports (Ty τ))}
    (ports : Ports (Ty τ)) (route : ∀ {t : Ty τ}, Port ports t → Origin args past t)
    (env : X ⟶ m.scope args past) (f : X ⟶ m.ports ports)
    (h : ∀ {t : Ty τ} (p : Port ports t),
      env ≫ Categorical.readOrigin m (route p) = f ≫ Categorical.project m p) :
    env ≫ Categorical.readWires m (wiresOf ports route) = f := by
  induction ports with
  | nil => exact CartesianMonoidalCategory.toUnit_unique _ _
  | cons t ports ih =>
    change env ≫ lift (Categorical.readOrigin m (route .head)) _ = _
    rw [CartesianMonoidalCategory.comp_lift]
    apply CartesianMonoidalCategory.hom_ext
    · rw [CartesianMonoidalCategory.lift_fst]
      exact h .head
    · rw [CartesianMonoidalCategory.lift_snd]
      apply ih
      intro t p
      exact (h (.tail p)).trans (Category.assoc _ _ _).symm

set_option backward.isDefEq.respectTransparency false in
omit [TypeFormers τ] [HasFiniteCoproducts D] [SymmetricCategory D] [DistributiveTensor D] in
private theorem gamma_graph_value {Γ : List τ} {A : τ} (extra : Nat)
    (arms : Fin (extra + 2) → Port Γ A) (i : Fin (extra + 2)) :
    Categorical.selectorLeg (m.selectors.tag i) ≫
        (gammaTerm (Φ := Φ) extra arms).denote m ≫ (ρ_ (m.value A)).hom =
      Categorical.project m (inputPort (arms i)) := by
  let args := PortType.control (extra + 2) :: inputs Γ
  let arm (j : Fin (extra + 2)) : m.ports (inputs Γ) ⟶ m.ports [.value A] :=
    (Term.ret (.cons (.arg (inputPort (arms j))) .nil) :
      Term (Opcode Φ) (inputs Γ) [] [] [.value A]).denote m
  let read : m.scope args [] ⟶ m.ports args :=
    Categorical.readWires m (wiresOf args Origin.arg)
  have hread : (ρ_ (m.ports args)).inv ≫ read = 𝟙 _ := by
    refine readWiresOf m (past := []) args Origin.arg (ρ_ (m.ports args)).inv (𝟙 _) ?_
    intro t p
    simp [Categorical.readOrigin, Categorical.Model.locals]
  let run := Categorical.dispatch m.selectors arm
  let pass : m.scope args [] ⟶ m.ports [.value A] := read ≫ run
  have hret : Categorical.extendScope m pass ≫
      Categorical.readWires m (.cons (.output ⟨0, Nat.zero_lt_succ _⟩ .head) .nil) =
      pass := by
    unfold Categorical.extendScope
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Categorical.readWires, Categorical.readOrigin, Categorical.appendScope,
        Categorical.appendLocal, Categorical.project, Category.assoc, CartesianMonoidalCategory.lift_fst]
      let X := m.ports args
      let Y := m.ports [.value A]
      change lift (𝟙 (X ⊗ 𝟙_ D)) pass ≫ (α_ X (𝟙_ D) Y).hom ≫
        (X ◁ ((λ_ Y).hom ≫ (ρ_ Y).inv)) ≫
        snd X (Y ⊗ 𝟙_ D) ≫ fst Y (𝟙_ D) ≫ fst (m.value A) (𝟙_ D) = _
      simp [Category.assoc, CartesianMonoidalCategory.leftUnitor_hom]
      exact CartesianMonoidalCategory.lift_snd_assoc
        (𝟙 (X ⊗ 𝟙_ D)) pass (fst (m.value A) (𝟙_ D))
    · exact CartesianMonoidalCategory.toUnit_unique _ _
  change Categorical.selectorLeg (m.selectors.tag i) ≫
      ((ρ_ (m.ports args)).inv ≫
        Categorical.extendScope m pass ≫ Categorical.readWires m _) ≫ _ = _
  rw [hret]
  have hpass : (ρ_ (m.ports args)).inv ≫ pass = run := by
    simp [pass, ← Category.assoc, hread]
  rw [hpass, ← Category.assoc, Categorical.dispatch_leg]
  simp [arm, Term.denote, Term.denoteOpen, Categorical.readWires, Categorical.readOrigin,
    CartesianMonoidalCategory.rightUnitor_hom, Categorical.Model.locals, Categorical.portsObj]

end Wiring

set_option backward.isDefEq.respectTransparency false in
theorem gamma_sound (sel : Categorical.Selectors D)
    (prim : ∀ f : Φ, M.obj (instrSrc f) ⟶ M.obj (instrTrg f))
    {Γ : List τ} {A : τ} (extra : Nat) (arms : Fin (extra + 2) → Port Γ A) :
    ∃ f : ctxObj M (selectorType (extra + 1) :: Γ) ⟶ M.obj A,
      Denotes J M (switchTyping (Φ := Φ) (extra + 1) .head (fun i => .tail (arms i))) (J.map f) ∧
      gammaEntryMap M sel prim extra Γ ≫ f =
        (gammaTerm (Φ := Φ) extra arms).denote (valueModel M sel prim) ≫ (ρ_ (M.obj A)).hom := by
  obtain ⟨f, d, hs⟩ := switch_sound (Φ := Φ) J M (extra + 1) .head (fun i => .tail (arms i))
  refine ⟨f, d, ?_⟩
  apply (sel.colimit (extra + 2) ((valueModel M sel prim).ports (inputs Γ))).hom_ext
  rintro ⟨i⟩
  let X := (valueModel M sel prim).ports (inputs Γ)
  let env := Categorical.selectorLeg (sel.tag i) ≫ gammaEntryMap M sel prim extra Γ
  have htag : env ≫ snd _ _ =
      toUnit ((valueModel M sel prim).ports (inputs Γ)) ≫ selectorTag M (extra + 1) i := by
    have cancel : sel.tag i ≫ (selectorIso M sel (extra + 1)).inv = selectorTag M (extra + 1) i := by
      rw [← selectorIso_tag M sel (extra + 1) i, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    simp only [env, gammaEntryMap, Categorical.selectorLeg, Category.assoc,
      CartesianMonoidalCategory.lift_snd]
    change lift (toUnit X ≫ sel.tag i) (𝟙 X) ≫ fst (sel.obj (extra + 2)) X ≫
      (selectorIso M sel (extra + 1)).inv = toUnit X ≫ selectorTag M (extra + 1) i
    rw [CartesianMonoidalCategory.lift_fst_assoc, Category.assoc, cancel]
  have hpayload : env ≫ fst _ _ = entryMap M Γ sel prim := by
    simp only [env, gammaEntryMap, Categorical.selectorLeg, Category.assoc,
      CartesianMonoidalCategory.lift_fst]
    change lift (toUnit X ≫ sel.tag i) (𝟙 X) ≫ snd (sel.obj (extra + 2)) X ≫
      entryMap M Γ sel prim = entryMap M Γ sel prim
    rw [CartesianMonoidalCategory.lift_snd_assoc, Category.id_comp]
  change Categorical.selectorLeg (sel.tag i) ≫ (gammaEntryMap M sel prim extra Γ ≫ f) = _
  rw [← Category.assoc, hs env i htag]
  change env ≫ (fst _ _ ≫ lookup M (index (arms i)) (index_at (arms i))) = _
  rw [← Category.assoc, hpayload, entryMap_lookup]
  exact (gamma_graph_value (valueModel M sel prim) extra arms i).symm

theorem gamma_related_sound (sel : Categorical.Selectors D)
    (prim : ∀ f : Φ, M.obj (instrSrc f) ⟶ M.obj (instrTrg f))
    {Γ : List τ} {A : τ} {extra : Nat} {t : Tm Φ}
    {rv : Term (Opcode Φ) (.control (extra + 2) :: inputs Γ) [] [[.value A]] [.value A]}
    (rel : GammaRelated extra t rv) (ht : Tm.HasType (selectorType (extra + 1) :: Γ) t A) :
    ∃ f : ctxObj M (selectorType (extra + 1) :: Γ) ⟶ M.obj A,
      Denotes J M ht (J.map f) ∧
      gammaEntryMap M sel prim extra Γ ≫ f =
        rv.denote (valueModel M sel prim) ≫ (ρ_ (M.obj A)).hom := by
  cases rel with
  | intro arms => exact gamma_sound J M sel prim extra arms

end Categories

end Silmaril.SSA.RVSDG.LambdaSSA.Proofs

module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.OriginalInstitution.Defs
import Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.OriginalInstitution
public import Silmaril.Logic.Institution.Hets.LogicGraph
public import Mathlib.CategoryTheory.Limits.Cones

@[expose] public section

/-! Sound original-rule consequence, actual capacity models and the finite/apex Hets family. -/

namespace Silmaril.Logic.TypeTheory.IntensionalMLTT.OriginalInstitution

open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Metatheory

/-- A finite stage's proof data are exactly the existing original bounded hypothetical trees. -/
def Proof.finiteEquiv (n : ℕ) (H : Set ScopedTyping) (q : ScopedTyping) :
    Proof (n : Stage) H q ≃ BoundedDerivationH n H q.Γ q.term q.carrier where
  toFun d := ⟨d.val, WithTop.coe_le_coe.mp d.property⟩
  invFun d := ⟨d.val, WithTop.coe_le_coe.mpr d.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- Apex proof data are exactly the unchanged unbounded original hypothetical trees. -/
def Proof.topEquiv (H : Set ScopedTyping) (q : ScopedTyping) :
    Proof ⊤ H q ≃ DerivationH H q.Γ q.term q.carrier where
  toFun := Subtype.val
  invFun d := ⟨d, le_top⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := rfl

/-- Every actual stage proof is valid in each admitted concrete capacity. -/
theorem Proof.sound {stage capacity : Stage} {H : Set ScopedTyping} {q : ScopedTyping}
    (d : Proof stage H q) (hCap : stage ≤ capacity)
    (hH : ∀ r ∈ H, CapacityValid capacity r) : CapacityValid capacity q :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.OriginalInstitution.proof_sound d hCap hH

/-- All original rules with actual typing hypotheses are sound at every finite/apex stage. -/
theorem logic_sound (stage : Stage) : (logic stage).Sound :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.OriginalInstitution.logic_sound stage

/-- The proof system's institution is the previously defined actual realizability institution. -/
theorem logic_toInst (stage : Stage) : (logic stage).toInst = bundled stage := rfl

/-- Every finite or full stage has its actual concrete interpretation at that same capacity. -/
def canonicalModel (stage : Stage) : (room stage).Mod := Discrete.mk ⟨stage, le_refl stage⟩

/-- The actual full code hierarchy is also an admitted model at every smaller syntax stage. -/
def fullModel (stage : Stage) : (room stage).Mod := Discrete.mk ⟨⊤, le_top⟩

theorem model_nonempty (stage : Stage) : Nonempty (room stage).Mod := ⟨canonicalModel stage⟩

/-- Every model admitted at the apex uses the actual full hierarchy. -/
theorem top_capacity (T : Model ⊤) : T.val = ⊤ := le_antisymm le_top T.property

/-- Finite-cap satisfaction is actual Code-cap validity of the scoped source typing judgment. -/
theorem finite_satisfaction {n cap : ℕ} (h : n ≤ cap) (q : Sentence (n : Stage)) :
    (room (n : Stage)).Sat (Discrete.mk ⟨(cap : Stage), WithTop.coe_le_coe.mpr h⟩) q ↔
      RawRealizability.ValidAt cap q.val.Γ q.val.term q.val.carrier := Iff.rfl

/-- Full-cap models use the actual unrestricted realizability interpretation. -/
theorem full_satisfaction (stage : Stage) (q : Sentence stage) :
    (room stage).Sat (fullModel stage) q ↔
      RawRealizability.Valid q.val.Γ q.val.term q.val.carrier := Iff.rfl

/-- Apex satisfaction is the proved actual full-hierarchy interpretation. -/
theorem apex_satisfaction (T : Model ⊤) (q : Sentence ⊤) :
    (room ⊤).Sat (Discrete.mk T) q ↔
      RawRealizability.Valid q.val.Γ q.val.term q.val.carrier := by
  change CapacityValid T.val q.val ↔ _
  rw [top_capacity T]
  rfl

/-- Universe count zero is below every finite or full stage. -/
theorem zero_le_stage (stage : Stage) : ((0 : ℕ) : Stage) ≤ stage := by
  cases stage with
  | none => exact le_top
  | some n => exact WithTop.coe_le_coe.mpr (Nat.zero_le n)

/-- A closed original zero sentence, already bounded at universe count zero. -/
def zeroSentence (stage : Stage) : Sentence stage :=
  ⟨⟨0, .nil, .zero, .nat⟩, by
    simpa [ScopedTyping.universeBound, Context.universeBound, Term.universeBound]
      using zero_le_stage stage⟩

/-- A closed bounded Empty sentence supplies a concrete nontriviality witness. -/
def emptySentence (stage : Stage) : Sentence stage :=
  ⟨⟨0, .nil, .zero, .empty⟩, by
    simpa [ScopedTyping.universeBound, Context.universeBound, Term.universeBound]
      using zero_le_stage stage⟩

/-- The original zero proof remains available even at stage zero. -/
theorem zero_derivable (stage : Stage) :
    (logic stage).Derives (Discrete.mk ()) ∅ (zeroSentence stage) := by
  change Nonempty (Proof stage (Subtype.val '' (∅ : Set (Sentence stage)))
    (⟨0, .nil, .zero, .nat⟩ : ScopedTyping))
  refine ⟨⟨.zero .nil, ?_⟩⟩
  simpa [DerivationH.universeBudget, ContextDerivationH.universeBudget,
    Context.universeBound, Term.universeBound] using zero_le_stage stage

/-- No actual finite or full model validates the closed Empty sentence. -/
theorem empty_not_valid (capacity : Stage) :
    ¬ CapacityValid capacity (⟨0, .nil, .zero, .empty⟩ : ScopedTyping) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.OriginalInstitution.empty_not_valid capacity

/-- Every original finite/apex consequence system is nontrivial in its actual canonical model. -/
theorem logic_consistent (stage : Stage) : ((logic stage).er (Discrete.mk ())).Consistent ∅ := by
  refine ⟨emptySentence stage, ?_⟩
  intro h
  have hSat : CapacityValid stage (emptySentence stage).val :=
    logic_sound stage (Discrete.mk ()) ∅ (emptySentence stage) h (canonicalModel stage)
      (fun _ hq => False.elim hq)
  exact empty_not_valid stage (by simpa only [emptySentence] using hSat)

/-- Empty-hypothesis finite-stage consequence recovers the original bounded source calculus. -/
theorem finite_derives_empty_iff (n : ℕ) (q : Sentence (n : Stage)) :
    (logic (n : Stage)).Derives (Discrete.mk ()) ∅ q ↔
      Nonempty (BoundedDerivation n q.val.Γ q.val.term q.val.carrier) := by
  change Nonempty (Proof (n : Stage) (Subtype.val '' (∅ : Set (Sentence (n : Stage)))) q.val) ↔ _
  rw [Set.image_empty]
  constructor
  · rintro ⟨d⟩
    exact ⟨((Proof.finiteEquiv n ∅ q.val) d).toOriginal⟩
  · rintro ⟨d⟩
    exact ⟨(Proof.finiteEquiv n ∅ q.val).symm (.ofOriginal d)⟩

/-- Empty-hypothesis apex consequence is exactly unchanged original typing. -/
theorem top_derives_empty_iff (q : Sentence ⊤) :
    (logic ⊤).Derives (Discrete.mk ()) ∅ q ↔ Typing q.val.Γ q.val.term q.val.carrier := by
  change Nonempty (Proof ⊤ (Subtype.val '' (∅ : Set (Sentence ⊤))) q.val) ↔ _
  rw [Set.image_empty]
  constructor
  · rintro ⟨d⟩
    exact ⟨((Proof.topEquiv ∅ q.val) d).erase⟩
  · rintro ⟨d⟩
    exact ⟨(Proof.topEquiv ∅ q.val).symm (.ofOriginal d)⟩

/-- The logic inclusion has exactly the proved semantic institution comorphism. -/
theorem inclusionLogic_toInst {stage more : Stage} (h : stage ≤ more) :
    (inclusionLogic h).toInstCoHom = inclusion h := rfl

@[simp] theorem inclusion_refl (stage : Stage) :
    inclusion (le_refl stage) = Inst.CoHom.id (bundled stage) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.OriginalInstitution.inclusion_refl stage

@[simp] theorem inclusion_comp {stage more most : Stage} (h : stage ≤ more) (k : more ≤ most) :
    inclusion (h.trans k) = Inst.CoHom.comp (inclusion h) (inclusion k) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.OriginalInstitution.inclusion_comp h k

/-- All finite stages and the actual full-hierarchy apex form a `CoIns` family. -/
noncomputable def family : Stage ⥤ CoIns.{0, 0, 0, 0, 0} where
  obj := bundled
  map f := inclusion (leOfHom f)
  map_id stage := inclusion_refl stage
  map_comp f g := inclusion_comp (leOfHom f) (leOfHom g)

/-- The original consequence institutions and their actual-capacity maps form a Hets graph. -/
noncomputable def hetsGraph : LogicGraph.{0, 0, 0, 0, 0, 0, 0} :=
  IndexedCoInst.toLogicGraph family

/-- The finite part of the original realizability institution family. -/
noncomputable def finiteFamily : ℕ ⥤ CoIns.{0, 0, 0, 0, 0} where
  obj n := bundled (n : Stage)
  map f := inclusion (WithTop.coe_le_coe.mpr (leOfHom f))
  map_id n := inclusion_refl (n : Stage)
  map_comp f g := inclusion_comp (WithTop.coe_le_coe.mpr (leOfHom f))
    (WithTop.coe_le_coe.mpr (leOfHom g))

/-- Each finite original typing institution maps into the actual full-hierarchy apex. -/
noncomputable def fromFinite (n : ℕ) : Inst.CoHom (bundled (n : Stage)) (bundled ⊤) :=
  inclusion le_top

/-- All routes into the full-hierarchy apex retain the same source sentence and capacity. -/
theorem fromFinite_comp {n m : ℕ} (h : n ≤ m) :
    Inst.CoHom.comp (inclusion (WithTop.coe_le_coe.mpr h)) (fromFinite m) = fromFinite n := rfl

/-- The actual full-hierarchy interpretation is a cocone over the finite original institutions. -/
noncomputable def cocone : Limits.Cocone finiteFamily where
  pt := bundled ⊤
  ι := {
    app := fromFinite
    naturality := by intro n m f; rfl }

theorem family_finite (n : ℕ) : family.obj (n : Stage) = bundled (n : Stage) := rfl

theorem family_top : family.obj ⊤ = bundled ⊤ := rfl

/-- Every apex sentence is already bounded at a concrete finite syntax stage. -/
theorem sentence_finite_capture (q : Sentence ⊤) :
    ∃ n, ∃ r : Sentence (n : Stage), includeSentence (show (n : Stage) ≤ ⊤ from le_top) r = q :=
  ⟨q.val.universeBound, ⟨q.val, le_refl _⟩, Subtype.ext rfl⟩

/-- Every empty-hypothesis apex derivation is already an actual finite-stage derivation. -/
theorem top_proof_finite_capture {q : Sentence ⊤}
    (h : (logic ⊤).Derives (Discrete.mk ()) ∅ q) :
    ∃ n, ∃ r : Sentence (n : Stage),
      (logic (n : Stage)).Derives (Discrete.mk ()) ∅ r ∧
      includeSentence (show (n : Stage) ≤ ⊤ from le_top) r = q := by
  rcases (top_derives_empty_iff q).mp h with ⟨d⟩
  let bound : BoundedDerivation d.universeBudget q.val.Γ q.val.term q.val.carrier :=
    ⟨d, Nat.le_refl _⟩
  let hypothetical : BoundedDerivationH d.universeBudget ∅ q.val.Γ q.val.term q.val.carrier :=
    .ofOriginal bound
  have hBound : q.val.universeBound ≤ d.universeBudget := by
    simpa only [ScopedTyping.UsesBelow] using hypothetical.usesBelow
  let r : Sentence (d.universeBudget : Stage) := ⟨q.val, WithTop.coe_le_coe.mpr hBound⟩
  exact ⟨d.universeBudget, r, (finite_derives_empty_iff d.universeBudget r).mpr ⟨bound⟩, Subtype.ext rfl⟩

/-- Exact satisfaction preservation retains the actual finite or full interpretation. -/
theorem inclusion_satisfaction {stage more : Stage} (h : stage ≤ more)
    (T : Model more) (q : Sentence stage) :
    (room more).Sat (Discrete.mk T) (includeSentence h q) ↔
      (room stage).Sat ((modelReduct h).obj (Discrete.mk T)) q := Iff.rfl

/-- Semantic consequences transport along every finite/apex inclusion. -/
theorem inclusion_entails {stage more : Stage} (h : stage ≤ more)
    {H : Set (Sentence stage)} {q : Sentence stage} (hq : (room stage).Entails H q) :
    (room more).Entails (includeSentence h '' H) (includeSentence h q) :=
  (inclusion h).entails_map (S := Discrete.mk ()) hq

end Silmaril.Logic.TypeTheory.IntensionalMLTT.OriginalInstitution

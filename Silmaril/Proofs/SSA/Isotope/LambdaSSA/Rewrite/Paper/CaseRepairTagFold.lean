module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Laws.CaseRepair.TagFold.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Laws.CaseRepair.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Uniformity.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Replay.Operand.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.EntryLet.Obstruction.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Coproducts.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Coproducts.Finite.Thms

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CaseRepairTagFold

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.Extension.Singleton
open Paper.Extension.Singleton.CaseRepair.TagFold

local notation "restoreBinary" => Paper.Extension.Singleton.CaseRepair.restore

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "Comp" => Paper.TypeCategory (τ := τ) Φ

@[reassoc (attr := simp)]
theorem inj_fold {n : Nat} {D : Comp}
    {tags : Cofan (fun _ : Fin n => D)} (ht : IsColimit tags) (i : Fin n) : tags.inj i ≫ fold ht = 𝟙 D :=
  Cofan.IsColimit.fac ht _ i

@[reassoc (attr := simp)]
theorem inj_restore {n : Nat} {B D : Comp}
    {tags : Cofan (fun _ : Fin n => D)} (ht : IsColimit tags) (p : tags.pt ⟶ B ⨿ D) (i : Fin n) :
    tags.inj i ≫ restore ht p = tags.inj i ≫ p ≫ coprod.map (𝟙 B) (tags.inj i) :=
  Cofan.IsColimit.fac ht _ i

theorem restore_post {n : Nat} {B D : Comp}
    {tags : Cofan (fun _ : Fin n => D)} (ht : IsColimit tags) (p : tags.pt ⟶ B ⨿ D) :
    restore ht p ≫ coprod.map (𝟙 B) (fold ht) = p := by
  apply Cofan.IsColimit.hom_ext ht _ _
  intro i
  simp only [inj_restore_assoc, coprod.map_map, inj_fold,
    coprod.map_id_id, Category.comp_id]

theorem recover_iff {n : Nat} {B D : Comp}
    {tags : Cofan (fun _ : Fin n => D)} (ht : IsColimit tags) (f : tags.pt ⟶ B ⨿ tags.pt) :
    restore ht (f ≫ coprod.map (𝟙 B) (fold ht)) = f ↔ PreservesTag f := by
  constructor
  · intro eq i
    refine ⟨tags.inj i ≫ f ≫ coprod.map (𝟙 B) (fold ht), ?_⟩
    have arm := congrArg (fun a => tags.inj i ≫ a) eq
    rw [inj_restore] at arm
    simpa only [Category.assoc] using arm.symm
  · intro arms
    apply Cofan.IsColimit.hom_ext ht _ _
    intro i
    obtain ⟨step, eq⟩ := arms i
    have row : tags.inj i ≫ f ≫ coprod.map (𝟙 B) (fold ht) = step := by
      rw [← Category.assoc, eq, Category.assoc, coprod.map_map, Category.id_comp, inj_fold,
        coprod.map_id_id, Category.comp_id]
    rw [inj_restore, ← Category.assoc, row, eq]

theorem binary_obligations {A B D : Comp} (split : D ⨿ D ≅ A)
    (h : A ⟶ D) (f : A ⟶ B ⨿ A) (p : A ⟶ B ⨿ D)
    (hl : (coprod.inl ≫ split.hom) ≫ h = 𝟙 D)
    (hr : (coprod.inr ≫ split.hom) ≫ h = 𝟙 D)
    (left right : D ⟶ B ⨿ D)
    (fl : (coprod.inl ≫ split.hom) ≫ f = left ≫ coprod.map (𝟙 B) (coprod.inl ≫ split.hom))
    (fr : (coprod.inr ≫ split.hom) ≫ f = right ≫ coprod.map (𝟙 B) (coprod.inr ≫ split.hom)) :
    let restoreTag := restoreBinary split (coprod.inl ≫ split.hom) (coprod.inr ≫ split.hom)
    restoreTag (f ≫ coprod.map (𝟙 B) h) = f ∧
      restoreTag p ≫ coprod.map (𝟙 B) h = p := by
  constructor
  · apply (cancel_epi split.hom).1
    apply coprod.hom_ext
    · have row : (coprod.inl ≫ split.hom) ≫ (f ≫ coprod.map (𝟙 B) h) = left := by
        rw [← Category.assoc, fl, Category.assoc, coprod.map_map, Category.id_comp, hl,
          coprod.map_id_id, Category.comp_id]
      rw [Paper.Extension.Singleton.CaseRepair.restore, Iso.hom_inv_id_assoc, coprod.inl_desc]
      simpa only [Category.assoc] using
        (congrArg (fun a => a ≫ coprod.map (𝟙 B) (coprod.inl ≫ split.hom)) row).trans fl.symm
    · have row : (coprod.inr ≫ split.hom) ≫ (f ≫ coprod.map (𝟙 B) h) = right := by
        rw [← Category.assoc, fr, Category.assoc, coprod.map_map, Category.id_comp, hr,
          coprod.map_id_id, Category.comp_id]
      rw [Paper.Extension.Singleton.CaseRepair.restore, Iso.hom_inv_id_assoc, coprod.inr_desc]
      simpa only [Category.assoc] using
        (congrArg (fun a => a ≫ coprod.map (𝟙 B) (coprod.inr ≫ split.hom)) row).trans fr.symm
  · apply (Paper.Extension.Singleton.CaseRepair.restore_post_iff split _ _ h p).2
    constructor <;> simp only [hl, hr, coprod.map_id_id, Category.comp_id]

variable (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

local notation "J" => projection Seed

private theorem projection_hom_ext {n : Nat} {D : Comp}
    {tags : Cofan (fun _ : Fin n => D)} (ht : IsColimit tags) {X : TypeCategory Seed}
    {k l : (J).obj tags.pt ⟶ X}
    (eq : ∀ i, (J).map (tags.inj i) ≫ k = (J).map (tags.inj i) ≫ l) : k = l :=
  (isColimitOfPreserves (J) ht).hom_ext (fun i => eq i.as)

theorem map_recover_iff {n : Nat} {B D : Comp}
    {tags : Cofan (fun _ : Fin n => D)} (ht : IsColimit tags) (f : tags.pt ⟶ B ⨿ tags.pt) :
    (J).map (restore ht (f ≫ coprod.map (𝟙 B) (fold ht))) = (J).map f ↔
      ∀ i, (J).map ((tags.inj i ≫ f) ≫ coprod.map (𝟙 B) (fold ht ≫ tags.inj i)) =
        (J).map (tags.inj i ≫ f) := by
  let f' := restore ht (f ≫ coprod.map (𝟙 B) (fold ht))
  have row (i : Fin n) :
      tags.inj i ≫ f' = (tags.inj i ≫ f) ≫ coprod.map (𝟙 B) (fold ht ≫ tags.inj i) := by
    dsimp only [f']
    simp only [inj_restore, Category.assoc, coprod.map_map, Category.id_comp]
  change (J).map f' = (J).map f ↔ _
  constructor
  · intro eq i
    rw [← row, (J).map_comp, eq, (J).map_comp]
  · intro eq
    apply projection_hom_ext Seed ht
    intro i
    rw [← (J).map_comp, ← (J).map_comp, row, eq]

theorem repairSource {n : Nat} {B D : Comp}
    {tags : Cofan (fun _ : Fin n => D)} (ht : IsColimit tags) (f : tags.pt ⟶ B ⨿ tags.pt) (g : D ⟶ B ⨿ D)
    (arms : PreservesTag f)
    (square : projectStep Seed f ≫ coprod.map (𝟙 ((J).obj B)) ((J).map (fold ht)) =
      (J).map (fold ht) ≫ projectStep Seed g) :
    let f' := restore ht (fold ht ≫ g)
    projectStep Seed f' = projectStep Seed f ∧
      f' ≫ coprod.map (𝟙 B) (fold ht) = fold ht ≫ g := by
  have eq := (projectSquare_iff Seed f g (fold ht)).1 square
  have mapRestore : (J).map (restore ht (f ≫ coprod.map (𝟙 B) (fold ht))) =
      (J).map (restore ht (fold ht ≫ g)) := by
    apply projection_hom_ext Seed ht
    intro i
    rw [← (J).map_comp, ← (J).map_comp, inj_restore, inj_restore]
    simp only [(J).map_comp] at eq ⊢
    rw [eq]
  rw [(recover_iff ht f).2 arms] at mapRestore
  refine ⟨?_, restore_post ht _⟩
  change (J).map (restore ht (fold ht ≫ g)) ≫ _ = (J).map f ≫ _
  rw [← mapRestore]

theorem uniformity {n : Nat} {B D : Comp}
    {tags : Cofan (fun _ : Fin n => D)} (ht : IsColimit tags)
    (constructor : ∀ i, Paper.TypeCategory.ConstructorReturn (tags.inj i))
    (f : tags.pt ⟶ B ⨿ tags.pt) (g : D ⟶ B ⨿ D)
    (arms : PreservesTag f)
    (square : projectStep Seed f ≫ coprod.map (𝟙 ((J).obj B)) ((J).map (fold ht)) =
      (J).map (fold ht) ≫ projectStep Seed g) :
    iterateChosen Seed (projectStep Seed f) = (J).map (fold ht) ≫ iterateChosen Seed (projectStep Seed g) := by
  obtain ⟨repair, _⟩ := repairSource Seed ht f g arms square
  rw [← repair]
  apply projection_hom_ext Seed ht
  intro i
  have comm : g ≫ coprod.map (𝟙 B) (tags.inj i) = tags.inj i ≫ restore ht (fold ht ≫ g) := by
    rw [inj_restore, ← Category.assoc, inj_fold_assoc]
  rw [← uniformity_of_constructor_square Seed (constructor i) g _ comm,
    ← Category.assoc, ← Functor.map_comp, inj_fold, (J).map_id, Category.id_comp]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CaseRepairTagFold

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CaseRepairTagFold.Example

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.TypeCategory
open Paper.Extension.Singleton
open Paper.Extension.Singleton.CaseRepair.TagFold (fold PreservesTag)

open Paper.EntryLetObstruction (U flatRequest movedRequest flatRequest_typed movedRequest_typed
  flatRequest_arrow_ne_moved)
open SequencingObstruction (Instruction)

private abbrev Bit : Ty Empty := Silmaril.coprod U U
private abbrev X := ofType (Φ := Instruction) U
private abbrev D := ofType (Φ := Instruction) Bit
private abbrev tags : Cofan (fun _ : Fin 2 => D) :=
  Cofan.mk (ofType (Φ := Instruction) (Silmaril.coprod Bit Bit))
    (Fin.cases (sumCofan Bit Bit).inl (fun _ => (sumCofan Bit Bit).inr))

private noncomputable def tagsColimit : IsColimit tags := Cofan.IsColimit.mk tags
  (fun s => (sumCofanIsColimit Bit Bit).desc (BinaryCofan.mk (s.inj 0) (s.inj 1)))
  (fun s i => by
    refine Fin.cases ?_ (Fin.cases ?_ (fun j => j.elim0)) i
    · exact (sumCofanIsColimit Bit Bit).fac _ ⟨WalkingPair.left⟩
    · exact (sumCofanIsColimit Bit Bit).fac _ ⟨WalkingPair.right⟩)
  (fun s m hm => by
    apply BinaryCofan.IsColimit.hom_ext (sumCofanIsColimit Bit Bit)
    · exact (hm 0).trans ((sumCofanIsColimit Bit Bit).fac (BinaryCofan.mk (s.inj 0) (s.inj 1)) ⟨WalkingPair.left⟩).symm
    · exact (hm 1).trans ((sumCofanIsColimit Bit Bit).fac (BinaryCofan.mk (s.inj 0) (s.inj 1)) ⟨WalkingPair.right⟩).symm)

private theorem tag_constructor (i : Fin 2) : ConstructorReturn (tags.inj i) := by
  refine Fin.cases ?_ (Fin.cases ?_ (fun j => j.elim0)) i
  · exact ⟨.inl (.var 0), .inl (.var rfl), sumCofan_inl Bit Bit⟩
  · exact ⟨.inr (.var 0), .inr (.var rfl), sumCofan_inr Bit Bit⟩

private abbrev zero : X ⟶ D := (sumCofan U U).inl
private abbrev one : X ⟶ D := (sumCofan U U).inr

private theorem zero_sumIso : zero ≫ (sumIso U U).hom = (coprod.inl : X ⟶ X ⨿ X) :=
  Paper.TypeCategory.sumCofan_inl_sumIso_hom U U

private theorem one_sumIso : one ≫ (sumIso U U).hom = (coprod.inr : X ⟶ X ⨿ X) :=
  Paper.TypeCategory.sumCofan_inr_sumIso_hom U U

private noncomputable def step (run : X ⟶ X) : D ⟶ X ⨿ D :=
  (sumIso U U).hom ≫ coprod.desc (run ≫ one ≫ coprod.inr) (run ≫ zero ≫ coprod.inr)

-- In either case the request runs before recurrence with the flipped retained bit.
private theorem step_zero (run : X ⟶ X) : zero ≫ step run = run ≫ one ≫ coprod.inr := by
  rw [step, ← Category.assoc, zero_sumIso, coprod.inl_desc]

example (run : X ⟶ X) : one ≫ step run = run ≫ zero ≫ coprod.inr := by
  rw [step, ← Category.assoc, one_sumIso, coprod.inr_desc]

private abbrev flat : X ⟶ X := ofRegion flatRequest_typed
private abbrev moved : X ⟶ X := ofRegion movedRequest_typed
private noncomputable abbrev target := step flat

private noncomputable def row : Fin 2 → (D ⟶ X ⨿ D) :=
  Fin.cases (step moved) (fun _ => target)

private noncomputable def source : tags.pt ⟶ X ⨿ tags.pt :=
  Cofan.IsColimit.desc tagsColimit (fun i => row i ≫ coprod.map (𝟙 X) (tags.inj i))

private theorem source_arm (i : Fin 2) :
    tags.inj i ≫ source = row i ≫ coprod.map (𝟙 X) (tags.inj i) :=
  Cofan.IsColimit.fac tagsColimit _ i

private abbrev Seed := Paper.WithEntryLet.Step (τ := Ty Empty) (Φ := Instruction)

local notation "J" => projection Seed

private theorem observed_arm (i : Fin 2) :
    tags.inj i ≫ (source ≫ coprod.map (𝟙 X) (fold tagsColimit)) = row i := by
  rw [← Category.assoc, source_arm, Category.assoc, coprod.map_map, Category.id_comp,
    inj_fold, coprod.map_id_id, Category.comp_id]

private theorem corrected_request : (J).map moved = (J).map flat := by
  have move : Paper.WithEntryLet.Site.here.move flatRequest = some movedRequest := rfl
  exact ((Paper.Extension.Singleton.ofRegion_eq_iff Seed flatRequest_typed movedRequest_typed).2
    (Paper.WithEntryLet.Site.move_sound .here flatRequest_typed move).2).symm

private theorem corrected_row (i : Fin 2) : (J).map (row i) = (J).map target := by
  refine Fin.cases ?_ (fun _ => rfl) i
  change (J).map (step moved) = (J).map (step flat)
  unfold step
  rw [(J).map_comp, (J).map_comp]
  apply congrArg ((J).map (sumIso U U).hom ≫ ·)
  apply projection_map_desc_congr Seed <;> simp only [(J).map_comp, corrected_request]

private theorem corrected_square :
    projectStep Seed source ≫ coprod.map (𝟙 ((J).obj X)) ((J).map (fold tagsColimit)) =
      (J).map (fold tagsColimit) ≫ projectStep Seed target := by
  apply (projectSquare_iff Seed _ _ _).2
  apply projection_hom_ext Seed tagsColimit
  intro i
  rw [← (J).map_comp, ← (J).map_comp, observed_arm, inj_fold_assoc]
  exact corrected_row i

-- Forgetting both tags after selecting the first retained input exposes the
-- diagnostic distinction between the two standard Paper computations.
example : source ≫ coprod.map (𝟙 X) (fold tagsColimit) ≠ fold tagsColimit ≫ target := by
  intro eq
  have arm := congrArg (fun a => tags.inj 0 ≫ a) eq
  rw [observed_arm, inj_fold_assoc] at arm
  change step moved = step flat at arm
  have input := congrArg (fun a => zero ≫ a) arm
  rw [step_zero, step_zero] at input
  let eraseBit : D ⟶ X := (sumIso U U).hom ≫ coprod.desc (𝟙 X) (𝟙 X)
  let out : X ⨿ D ⟶ X := coprod.desc (𝟙 X) eraseBit
  have remove : one ≫ coprod.inr ≫ out = 𝟙 X := by
    dsimp only [out, eraseBit]
    rw [coprod.inr_desc, ← Category.assoc, one_sumIso, coprod.inr_desc]
  have result := congrArg (fun a => a ≫ out) input
  apply flatRequest_arrow_ne_moved
  simpa only [Category.assoc, remove, Category.comp_id] using result.symm

example : iterateChosen Seed (projectStep Seed source) =
    (J).map (fold tagsColimit) ≫ iterateChosen Seed (projectStep Seed target) :=
  uniformity Seed tagsColimit tag_constructor source target (fun i => ⟨row i, source_arm i⟩)
    corrected_square

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CaseRepairTagFold.Example

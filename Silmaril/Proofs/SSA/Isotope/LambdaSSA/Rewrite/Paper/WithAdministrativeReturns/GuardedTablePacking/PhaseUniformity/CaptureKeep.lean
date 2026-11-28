module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.LatchSource

/-! # Keeping a captured input that the rows of a dispatcher use only at a return -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity (Eqv Step)
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open Paper.WithCaseBind.BitQuery (signature)
open Paper.TypeCategory (ofType ofRegion iterate sumIso phaseFold classFold coprod_desc_ofRegion
  iterate_uniformity_ofBranchValue)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)

local notation "N" => Step (τ := Ty Empty) (Φ := signature.Instr) false
local notation "π" => Paper.Extension.Singleton.projection (Step (τ := Ty Empty) (Φ := signature.Instr) false)

set_option backward.isDefEq.respectTransparency false
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (seqValueBranches caseValueBranches)
open Paper.TypeCategory (ofRegion_id ofRegion_comp)
open Paper.Extension.Singleton (iterateSum iterateSum_map)
open Paper.Extension.Singleton.ValueCoproducts (exactCopair)
open Paper.Extension.Singleton.Generation (exactCopair_ofRegion)

local notation "QLit" => Paper.Extension.Singleton.ofRegion (Step (τ := Ty Empty) (Φ := signature.Instr) false)
local notation "U" => (Ty.unit : Ty Empty)
open Paper.TypeCategory (iterate_roll)
open Silmaril.DeBruijn (lift)
open CfgEta.TypeCategory.Retained (distributorRegion distributorRegion_typed)
open CfgEta.TypeCategory (productSndBranches whiskerLeftRegion whiskerLeftRegion_typed)
open Paper.TypeCategory (whiskerLeft whiskerLeft_comp whiskerLeft_id whiskerLeft_ofRegion whiskerLeftFunctor
  tensorObj leftCoproductComparisonIso leftCoproductComparisonIso_hom leftCoproductComparisonIso_inv
  leftCoproductDistributor)
open Paper.TypeCategory.Projection (productSnd iterate_projected_whiskerLeft)
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback
  (packedReadbackRep dispatcherRep orderedRow emptyDispatchRep)
open Paper.TypeCategory (sumInl sumInr blockRoute blockStep iterate_blockStep iterate_fixpoint)
open Paper.TypeCategory (whiskerLeft_iterate iterate_naturality)

/-! ## A dispatcher of two lifted rows with any tail -/

section General

variable {X A₀ A₁ D E : Ty Empty} {ρ₀ ρ₁ dR β₀ β₁ K : Region signature.Instr}

local notation "Z" => ofType (Φ := signature.Instr) X
local notation "P" => Silmaril.coprod A₀ (Silmaril.coprod A₁ Silmaril.empty)
local notation "S" => Silmaril.product X (Silmaril.coprod A₀ (Silmaril.coprod A₁ Silmaril.empty))

/-- A lifted row with a tail `K` whose arrow is the inverse comparison
followed by `g` on the return side. -/
theorem gen_row {A : Ty Empty} {β : Region signature.Instr}
    (hK : ValueBranches [Silmaril.product X (Silmaril.coprod E P)] K [Silmaril.coprod D S])
    (g : tensorObj Z (ofType E) ⟶ ofType (Φ := signature.Instr) D)
    (hKg : ofRegion hK ≫ (sumIso (Φ := signature.Instr) D S).hom =
      whiskerLeft Z (sumIso (Φ := signature.Instr) E P).hom ≫
        ((leftCoproductComparisonIso Z (ofType E) (ofType P)).inv ≫ coprod.map g (𝟙 (tensorObj Z (ofType P)))))
    (hβ : ValueBranches [A] β [Silmaril.coprod E P]) :
    whiskerLeft Z (ofRegion hβ ≫ (sumIso (Φ := signature.Instr) E P).hom) ≫
        ((leftCoproductComparisonIso Z (ofType E) (ofType P)).inv ≫ coprod.map g (𝟙 (tensorObj Z (ofType P)))) =
      ofRegion (seqValueBranches (whiskerLeftRegion_typed X hβ) hK) ≫
        (sumIso (Φ := signature.Instr) D S).hom := by
  rw [whiskerLeft_comp, whiskerLeft_ofRegion, Category.assoc, ← hKg, ← Category.assoc,
    ofRegion_comp (whiskerLeftRegion_typed X hβ) hK (seqValueBranches (whiskerLeftRegion_typed X hβ) hK)]

/-- The dead row of the empty tail, for any tail `K`. -/
theorem gen_dead
    (hK : ValueBranches [Silmaril.product X (Silmaril.coprod E P)] K [Silmaril.coprod D S])
    (g : tensorObj Z (ofType E) ⟶ ofType (Φ := signature.Instr) D)
    (hKg : ofRegion hK ≫ (sumIso (Φ := signature.Instr) D S).hom =
      whiskerLeft Z (sumIso (Φ := signature.Instr) E P).hom ≫
        ((leftCoproductComparisonIso Z (ofType E) (ofType P)).inv ≫ coprod.map g (𝟙 (tensorObj Z (ofType P)))))
    (hd : ValueBranches [Silmaril.empty] dR [Silmaril.coprod D S]) :
    whiskerLeft Z ((Paper.TypeCategory.emptyIsInitial (Φ := signature.Instr)).to (ofType E ⨿ ofType P)) ≫
        ((leftCoproductComparisonIso Z (ofType E) (ofType P)).inv ≫ coprod.map g (𝟙 (tensorObj Z (ofType P)))) =
      ofRegion (seqValueBranches (productSndBranches X Silmaril.empty) hd) ≫
        (sumIso (Φ := signature.Instr) D S).hom := by
  obtain ⟨k, hk, ek⟩ := Paper.TypeCategory.exists_ofRegion
    ((Paper.TypeCategory.emptyIsInitial (Φ := signature.Instr)).to (ofType E ⨿ ofType P) ≫
      (sumIso (Φ := signature.Instr) E P).inv)
  have e : (Paper.TypeCategory.emptyIsInitial (Φ := signature.Instr)).to (ofType E ⨿ ofType P) =
      ofRegion hk ≫ (sumIso (Φ := signature.Instr) E P).hom := by
    rw [← ek, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [e, gen_row hK g hKg hk]
  exact congrArg (· ≫ (sumIso (Φ := signature.Instr) D S).hom)
    (tensor_empty_ext (seqValueBranches (whiskerLeftRegion_typed X hk) hK)
      (seqValueBranches (productSndBranches X Silmaril.empty) hd))

/-- A dispatcher of two rows that are capture-free rows whiskered by the
captured input and followed by a tail `K` is the whiskered capture-free
step followed by that tail. Default Paper. -/
theorem two_row_lifted
    (hK : ValueBranches [Silmaril.product X (Silmaril.coprod E P)] K [Silmaril.coprod D S])
    (g : tensorObj Z (ofType E) ⟶ ofType (Φ := signature.Instr) D)
    (hKg : ofRegion hK ≫ (sumIso (Φ := signature.Instr) D S).hom =
      whiskerLeft Z (sumIso (Φ := signature.Instr) E P).hom ≫
        ((leftCoproductComparisonIso Z (ofType E) (ofType P)).inv ≫ coprod.map g (𝟙 (tensorObj Z (ofType P)))))
    (hρ₀ : ValueBranches [Silmaril.product X A₀] ρ₀ [Silmaril.coprod D S])
    (hρ₁ : ValueBranches [Silmaril.product X A₁] ρ₁ [Silmaril.coprod D S])
    (hd : ValueBranches [Silmaril.empty] dR [Silmaril.coprod D S])
    (hβ₀ : ValueBranches [A₀] β₀ [Silmaril.coprod E P])
    (hβ₁ : ValueBranches [A₁] β₁ [Silmaril.coprod E P])
    (e₀ : ofRegion hρ₀ = ofRegion (seqValueBranches (whiskerLeftRegion_typed X hβ₀) hK))
    (e₁ : ofRegion hρ₁ = ofRegion (seqValueBranches (whiskerLeftRegion_typed X hβ₁) hK))
    (hdisp : ValueBranches [S] (twoRows ρ₀ ρ₁ dR) [Silmaril.coprod D S]) :
    ofRegion hdisp ≫ (sumIso (Φ := signature.Instr) D S).hom =
      (whiskerLeft Z (freeStep hβ₀ hβ₁) ≫ (leftCoproductComparisonIso Z (ofType E) (ofType P)).inv) ≫
        coprod.map g (𝟙 (tensorObj Z (ofType P))) := by
  have hdead := seqValueBranches (productSndBranches X Silmaril.empty) hd
  have hin := caseValueBranches hρ₁ hdead
  have hmid := seqValueBranches (distributorRegion_typed X A₁ Silmaril.empty) hin
  have hout := caseValueBranches hρ₀ hmid
  have left : ofRegion hdisp ≫ (sumIso (Φ := signature.Instr) D S).hom =
      (ofRegion (τ := Ty Empty) (distributorRegion_typed X A₀ (Silmaril.coprod A₁ Silmaril.empty)) ≫
        (sumIso (τ := Ty Empty) (Φ := signature.Instr) (Silmaril.product X A₀)
          (Silmaril.product X (Silmaril.coprod A₁ Silmaril.empty))).hom) ≫
        coprod.desc (ofRegion hρ₀ ≫ (sumIso (Φ := signature.Instr) D S).hom)
          ((ofRegion (τ := Ty Empty) (distributorRegion_typed X A₁ Silmaril.empty) ≫
            (sumIso (τ := Ty Empty) (Φ := signature.Instr) (Silmaril.product X A₁)
              (Silmaril.product X Silmaril.empty)).hom) ≫
            coprod.desc (ofRegion hρ₁ ≫ (sumIso (Φ := signature.Instr) D S).hom)
              (ofRegion hdead ≫ (sumIso (Φ := signature.Instr) D S).hom)) := by
    rw [← ofRegion_comp (distributorRegion_typed X A₀ (Silmaril.coprod A₁ Silmaril.empty)) hout hdisp,
      ← coprod_desc_ofRegion hρ₀ hmid, ← ofRegion_comp (distributorRegion_typed X A₁ Silmaril.empty) hin hmid,
      ← coprod_desc_ofRegion hρ₁ hdead]
    simp only [Category.assoc, coprod.desc_comp]
  rw [left, e₀, e₁, ← gen_row hK g hKg hβ₀, ← gen_row hK g hKg hβ₁, ← gen_dead hK g hKg hd]
  unfold freeStep
  rw [whisker_sum, whisker_sum]
  simp only [Category.assoc, coprod.desc_comp]

/-- Such a dispatcher iterates as the whiskered capture-free loop
followed by `g`: iteration strength and naturality. -/
theorem two_row_keep
    (hK : ValueBranches [Silmaril.product X (Silmaril.coprod E P)] K [Silmaril.coprod D S])
    (g : tensorObj Z (ofType E) ⟶ ofType (Φ := signature.Instr) D)
    (hKg : ofRegion hK ≫ (sumIso (Φ := signature.Instr) D S).hom =
      whiskerLeft Z (sumIso (Φ := signature.Instr) E P).hom ≫
        ((leftCoproductComparisonIso Z (ofType E) (ofType P)).inv ≫ coprod.map g (𝟙 (tensorObj Z (ofType P)))))
    (hρ₀ : ValueBranches [Silmaril.product X A₀] ρ₀ [Silmaril.coprod D S])
    (hρ₁ : ValueBranches [Silmaril.product X A₁] ρ₁ [Silmaril.coprod D S])
    (hd : ValueBranches [Silmaril.empty] dR [Silmaril.coprod D S])
    (hβ₀ : ValueBranches [A₀] β₀ [Silmaril.coprod E P])
    (hβ₁ : ValueBranches [A₁] β₁ [Silmaril.coprod E P])
    (e₀ : ofRegion hρ₀ = ofRegion (seqValueBranches (whiskerLeftRegion_typed X hβ₀) hK))
    (e₁ : ofRegion hρ₁ = ofRegion (seqValueBranches (whiskerLeftRegion_typed X hβ₁) hK))
    (hdisp : ValueBranches [S] (twoRows ρ₀ ρ₁ dR) [Silmaril.coprod D S]) :
    iterate (ofRegion hdisp ≫ (sumIso (Φ := signature.Instr) D S).hom) =
      whiskerLeft Z (iterate (freeStep hβ₀ hβ₁)) ≫ g := by
  exact (congrArg Paper.TypeCategory.iterate
      (two_row_lifted hK g hKg hρ₀ hρ₁ hd hβ₀ hβ₁ e₀ e₁ hdisp)).trans
    ((iterate_naturality (whiskerLeft Z (freeStep hβ₀ hβ₁) ≫
        (leftCoproductComparisonIso Z (ofType E) (ofType P)).inv) g).symm.trans
      (congrArg (· ≫ g) (whiskerLeft_iterate Z (freeStep hβ₀ hβ₁))))

end General

/-! ## Two blocks at a sum: the back-edge block forwards to the header -/

section Bekic

variable {A E : Ty Empty} {body hd : Region signature.Instr}

theorem tagHeadG_typed :
    ValueBranches [A] (.br 0 (.inl (.var 0)) : Region signature.Instr)
      [Silmaril.coprod A (Silmaril.coprod A Silmaril.empty)] :=
  .br rfl (.inl (.var rfl))

theorem latchStepG_typed :
    ValueBranches [A] (latchStep : Region signature.Instr)
      [Silmaril.coprod E (Silmaril.coprod A (Silmaril.coprod A Silmaril.empty))] :=
  .br rfl (.inr (.inl (.var rfl)))

local notation "P'" => Silmaril.coprod A Silmaril.empty
local notation "T2" => Silmaril.coprod A (Silmaril.coprod A Silmaril.empty)

theorem retInlG_typed :
    ValueBranches [E] (.br 0 (.inl (.var 0)) : Region signature.Instr) [Silmaril.coprod E T2] :=
  .br rfl (.inl (.var rfl))

theorem tagLatchG_typed :
    ValueBranches [A] (.br 0 (.inr (.inr (.inl (.var 0)))) : Region signature.Instr)
      [Silmaril.coprod E T2] :=
  .br rfl (.inr (.inr (.inl (.var rfl))))

/-- The header row of the two blocks: exit, or enter the back-edge block. -/
noncomputable def headRowG (b : ofType (Φ := signature.Instr) A ⟶ ofType E ⨿ ofType A) :
    ofType (Φ := signature.Instr) A ⟶ (ofType E ⨿ ofType A) ⨿ ofType P' :=
  b ≫ coprod.desc (coprod.inl ≫ coprod.inl) (sumInl A Silmaril.empty ≫ coprod.inr)

/-- The back-edge row: go to the header. -/
noncomputable def latchRowG :
    ofType (Φ := signature.Instr) P' ⟶ (ofType E ⨿ ofType A) ⨿ ofType P' :=
  (sumIso (Φ := signature.Instr) A Silmaril.empty).hom ≫
    coprod.desc (coprod.inr ≫ coprod.inl) ((Paper.TypeCategory.emptyIsInitial (Φ := signature.Instr)).to _)

theorem tagHeadG_arrow : ofRegion (tagHeadG_typed (A := A)) = sumInl (Φ := signature.Instr) A P' :=
  (br_inl (.var rfl)).trans ((congrArg (· ≫ _) (ofRegion_id A)).trans (Category.id_comp _))

theorem latchStepG_arrow :
    ofRegion (latchStepG_typed (A := A) (E := E)) ≫ (sumIso (Φ := signature.Instr) E T2).hom =
      sumInl (Φ := signature.Instr) A P' ≫ coprod.inr := by
  have e : ofRegion (latchStepG_typed (A := A) (E := E)) = ofRegion tagHeadG_typed ≫
      (coprod.inr ≫ (sumIso (Φ := signature.Instr) E T2).inv) := br_inr (.inl (.var rfl))
  rw [e, tagHeadG_arrow]
  simp

theorem tagLatchG_arrow :
    ofRegion tagLatchG_typed = (sumInl (Φ := signature.Instr) A Silmaril.empty ≫ sumInr A P') ≫
      (coprod.inr ≫ (sumIso (Φ := signature.Instr) E T2).inv) := by
  have e₁ : ofRegion tagLatchG_typed =
      ofRegion (r := .br 0 (.inr (.inl (.var 0)))) (.br (L := [T2]) rfl (.inr (.inl (.var rfl)))) ≫
        (coprod.inr ≫ (sumIso (Φ := signature.Instr) E T2).inv) := br_inr (.inr (.inl (.var rfl)))
  have e₂ : ofRegion (r := (.br 0 (.inr (.inl (.var 0))) : Region signature.Instr))
      (.br (L := [T2]) (Γ := [A]) rfl (.inr (.inl (.var rfl)))) =
      ofRegion (r := .br 0 (.inl (.var 0))) (.br (L := [P']) rfl (.inl (.var rfl))) ≫
        (coprod.inr ≫ (sumIso (Φ := signature.Instr) A P').inv) := br_inr (.inl (.var rfl))
  have e₃ : ofRegion (r := (.br 0 (.inl (.var 0)) : Region signature.Instr))
      (.br (L := [P']) (Γ := [A]) rfl (.inl (.var rfl))) = sumInl (Φ := signature.Instr) A Silmaril.empty :=
    (br_inl (.var rfl)).trans ((congrArg (· ≫ _) (ofRegion_id A)).trans (Category.id_comp _))
  rw [e₁, e₂, e₃]
  rfl

/-- The capture-free step on the tags is the joined step of the two rows. -/
theorem free_blockStepG (hbody : ValueBranches [A] body [Silmaril.coprod E A])
    (hhd : ValueBranches [A] hd [Silmaril.coprod E T2])
    (eh : ofRegion hhd = ofRegion hbody ≫
      ofRegion (caseValueBranches (retInlG_typed (A := A) (E := E)) tagLatchG_typed)) :
    freeStep hhd (latchStepG_typed (A := A) (E := E)) =
      blockStep A P' (headRowG (ofRegion hbody ≫ (sumIso (Φ := signature.Instr) E A).hom))
        (latchRowG (A := A) (E := E)) := by
  have ea : ofRegion hhd ≫ (sumIso (Φ := signature.Instr) E T2).hom =
      headRowG (ofRegion hbody ≫ (sumIso (Φ := signature.Instr) E A).hom) ≫ blockRoute A P' E := by
    have retInl_arrow : ofRegion retInlG_typed = coprod.inl ≫ (sumIso (Φ := signature.Instr) E T2).inv :=
      (br_inl (.var rfl)).trans ((congrArg (· ≫ _) (ofRegion_id E)).trans (Category.id_comp _))
    rw [eh, ← coprod_desc_ofRegion retInlG_typed tagLatchG_typed, retInl_arrow, tagLatchG_arrow]
    unfold headRowG blockRoute
    simp only [Category.assoc]
    congr 2
    apply coprod.hom_ext
    · simp
    · simp
  have eb : (sumIso (Φ := signature.Instr) A Silmaril.empty).hom ≫
      coprod.desc (ofRegion (latchStepG_typed (A := A) (E := E)) ≫ (sumIso (Φ := signature.Instr) E T2).hom)
        ((Paper.TypeCategory.emptyIsInitial (Φ := signature.Instr)).to _) =
      (latchRowG (A := A) (E := E)) ≫ blockRoute A P' E := by
    unfold latchRowG
    rw [Category.assoc, latchStepG_arrow]
    congr 1
    apply coprod.hom_ext
    · unfold blockRoute
      simp
    · exact (Paper.TypeCategory.emptyIsInitial (Φ := signature.Instr)).hom_ext _ _
  exact congrArg ((sumIso (Φ := signature.Instr) A P').hom ≫ ·) (congrArg₂ coprod.desc ea eb)

/-- Iterating the back-edge row goes to the header. -/
theorem latch_iterateG :
    iterate (latchRowG (A := A) (E := E)) = (sumIso (Φ := signature.Instr) A Silmaril.empty).hom ≫
      coprod.desc coprod.inr ((Paper.TypeCategory.emptyIsInitial (Φ := signature.Instr)).to _) := by
  refine (iterate_fixpoint (latchRowG (A := A) (E := E))).trans ?_
  unfold latchRowG
  rw [Category.assoc]
  congr 1
  apply coprod.hom_ext
  · simp
  · exact (Paper.TypeCategory.emptyIsInitial (Φ := signature.Instr)).hom_ext _ _

/-- With the back-edge block solved, the header row is its own step. -/
theorem head_solvedG (b : ofType (Φ := signature.Instr) A ⟶ ofType E ⨿ ofType A) :
    headRowG b ≫ coprod.desc (𝟙 _) (iterate (latchRowG (A := A) (E := E))) = b := by
  rw [latch_iterateG (A := A) (E := E)]
  unfold headRowG sumInl
  rw [Category.assoc]
  refine (congrArg (b ≫ ·) ?_).trans (Category.comp_id _)
  apply coprod.hom_ext <;> simp

/-- The capture-free loop on the tags, entered at the header, is the
loop of the header's step. Default Paper: Bekič for two blocks at an
exact sum. -/
theorem bekic_two (hbody : ValueBranches [A] body [Silmaril.coprod E A])
    (hhd : ValueBranches [A] hd [Silmaril.coprod E T2])
    (eh : ofRegion hhd = ofRegion hbody ≫
      ofRegion (caseValueBranches (retInlG_typed (A := A) (E := E)) tagLatchG_typed)) :
    ofRegion tagHeadG_typed ≫ iterate (freeStep hhd (latchStepG_typed (A := A) (E := E))) =
      iterate (ofRegion hbody ≫ (sumIso (Φ := signature.Instr) E A).hom) := by
  rw [tagHeadG_arrow, free_blockStepG hbody hhd eh,
    (iterate_blockStep A P' (headRowG (ofRegion hbody ≫ (sumIso (Φ := signature.Instr) E A).hom))
      (latchRowG (A := A) (E := E))).1,
    head_solvedG]

end Bekic

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables

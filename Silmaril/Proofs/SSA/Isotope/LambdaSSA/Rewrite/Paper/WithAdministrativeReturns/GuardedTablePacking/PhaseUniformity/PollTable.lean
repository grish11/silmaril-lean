module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Packed.Product.Flat.BitEntry.PollTable.Defs
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.BitEntry

/-! # Certificates for the two-block polling fragment -/

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
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback (carryExit)

/-! ## The flat graph -/

theorem poll_flat_typed (d : PollTable) :
    LambdaSSA.FiniteCFG.HasType (.snoc .nil Bit) (fun _ : Fin 2 => Bit) (fun _ : Fin 1 => Bit) d.flat where
  entry := by
    obtain ⟨_, _, start⟩ := d
    cases start <;> exact .br (i := _) .bv
  block := fun i => by
    have h : ∀ (l : Bool) (b₁ b₂ : PollLeaf),
        LambdaSSA.Flat.HasType (SSA.FiniteSum.append (fun _ : Fin 2 => Bit) (fun _ : Fin 1 => Bit))
          (.snoc (.snoc .nil Bit) Bit) (pollFlatBlock l b₁ b₂) := by
      intro l b₁ b₂
      rcases b₁ with _ | (_ | _) <;> rcases b₂ with _ | (_ | _) <;>
        exact .case (A := Bit) (B := Bit) (.op .bv) (.br (i := _) .bv) (.br (i := _) .bv)
    exact h _ _ _

/-! ## The free row of a block and the readback row -/

/-- A leaf with its exit tagged: return the payload, or continue at the
tag of a block. -/
def freeLeaf : PollLeaf → Region signature.Instr
  | .exit => .br 0 (.inl (.var 0))
  | .goto false => .br 0 (.inr (.inl (.var 0)))
  | .goto true => .br 0 (.inr (.inr (.inl (.var 0))))

theorem freeLeaf_typed {Γ : VCtx (Ty Empty)} :
    (b : PollLeaf) → ValueBranches (Bit :: Γ) (freeLeaf b) [Silmaril.coprod Bit CaptTags]
  | .exit => .br rfl (.inl (.var rfl))
  | .goto false => .br rfl (.inr (.inl (.var rfl)))
  | .goto true => .br rfl (.inr (.inr (.inl (.var rfl))))

/-- The capture-free step of a block on its parameter. -/
def freeRow (l : Bool) (b₁ b₂ : PollLeaf) : Region signature.Instr :=
  .case (.op (.ask l) (.var 0)) (freeLeaf b₁) (freeLeaf b₂)

theorem freeRow_typed (l : Bool) (b₁ b₂ : PollLeaf) :
    ValueBranches [Bit] (freeRow l b₁ b₂) [Silmaril.coprod Bit CaptTags] :=
  .case (A := Bit) (B := Bit) (.op (.var (i := 0) rfl)) (freeLeaf_typed b₁) (freeLeaf_typed b₂)

/-- The row of a table block in the packed readback. -/
def rowOf (r : Region signature.Instr) : Region signature.Instr :=
  Paper.RetainedLet.unpackBody (r.lsubst (carryExit 1 2))

/-- A free leaf, whiskered by the captured input and followed by `dropCase`. -/
def liftFree (X : Region signature.Instr) : Region signature.Instr :=
  ((X.renameVars (lift (lift (Nat.succ ∘ Nat.succ)))).lsubst
      (liftLSubstVars (fun _ => .br 0 (.pair (.var 2) (.var 0))))).lsubst
    (liftLSubstVars (liftLSubstVars (liftLSubstVars (fun _ => dropCase.renameVars (lift Nat.succ)))))

/-- A leaf of a readback row. -/
def rbLeaf (ℓ : Nat) : Region signature.Instr :=
  ((((carryExit 1 2 ℓ : Region signature.Instr).renameVars (lift Nat.succ)).substVars
    (Tm.singleSubst (.var 0))).renameVars (lift (lift (lift Nat.succ))))

theorem leaf_lift :
    (b : PollLeaf) → Paper.Eqv [Bit, Bit, Bit, Silmaril.product Bit Bit] (liftFree (freeLeaf b)) (rbLeaf b.idx)
      [Silmaril.coprod Bit CaptState]
  | .exit => drop_inl (X := Bit) (A := CaptTags) (i := 2) rfl (.var (i := 0) rfl)
  | .goto false => drop_inr (X := Bit) (B := Bit) (i := 2) rfl (.inl (.var (i := 0) rfl))
  | .goto true => drop_inr (X := Bit) (B := Bit) (i := 2) rfl (.inr (.inl (.var (i := 0) rfl)))

/-- The readback row of a block is its free row whiskered by the captured
input and followed by `dropCase`. Default Paper. -/
theorem row_lift (l : Bool) (b₁ b₂ : PollLeaf) :
    Paper.Eqv [Silmaril.product Bit Bit] (seqRegion (whiskerLeftRegion (freeRow l b₁ b₂)) dropCase)
      (rowOf (pollBlock l b₁ b₂)) [Silmaril.coprod Bit CaptState] :=
  .let₂ (A := Bit) (B := Bit) (.var rfl)
    (.case (A := Bit) (B := Bit) (.op (.var (i := 0) rfl)) (leaf_lift b₁) (leaf_lift b₂))

/-! ## The readback as a capture-free loop on the tags -/

theorem free_typed (d : PollTable) (c : Bool) :
    ValueBranches [Bit] (freeRow (d.label c) (d.branch c false) (d.branch c true))
      [Silmaril.coprod Bit CaptTags] :=
  freeRow_typed _ _ _

theorem row0_typed (d : PollTable) :
    ValueBranches [Silmaril.product Bit Bit] (rowOf (d.blocks 0)) [Silmaril.coprod Bit CaptState] :=
  (orderedRow (fun _ : Fin 2 => Bit) d.blocks_typed ⟨0, by simp⟩).property

theorem row1_typed (d : PollTable) :
    ValueBranches [Silmaril.product Bit Bit] (rowOf (d.blocks 1)) [Silmaril.coprod Bit CaptState] :=
  (orderedRow (fun _ : Fin 2 => Bit) d.blocks_typed ⟨1, by simp⟩).property

theorem row0_lifted (d : PollTable) :
    ofRegion (row0_typed d) = ofRegion (seqValueBranches (whiskerLeftRegion_typed Bit (free_typed d false))
      (dropCase_typed (X := Bit) (B := Bit) (A := CaptTags))) :=
  (Paper.TypeCategory.ofRegion_eq_iff _ _).mpr
    (row_lift (d.label false) (d.branch false false) (d.branch false true)).symm

theorem row1_lifted (d : PollTable) :
    ofRegion (row1_typed d) = ofRegion (seqValueBranches (whiskerLeftRegion_typed Bit (free_typed d true))
      (dropCase_typed (X := Bit) (B := Bit) (A := CaptTags))) :=
  (Paper.TypeCategory.ofRegion_eq_iff _ _).mpr
    (row_lift (d.label true) (d.branch true false) (d.branch true true)).symm

theorem poll_disp_typed (d : PollTable) :
    ValueBranches [CaptState] (twoRows (rowOf (d.blocks 0)) (rowOf (d.blocks 1)) captDead.val)
      [Silmaril.coprod Bit CaptState] :=
  (dispatcherRep Bit (List.ofFn fun _ : Fin 2 => Bit) (orderedRow (fun _ : Fin 2 => Bit)
    d.blocks_typed)).property

/-- The tag of a block. -/
def rowTag : Bool → Tm signature.Instr
  | false => .inl (.var 0)
  | true => .inr (.inl (.var 0))

theorem rowTag_typed : (c : Bool) → Tm.BranchValue [Bit] (rowTag c) CaptTags
  | false => .inl (.var rfl)
  | true => .inr (.inl (.var rfl))

theorem rowTagR_typed (c : Bool) : ValueBranches [Bit] (.br 0 (rowTag c) : Region signature.Instr) [CaptTags] :=
  .br rfl (rowTag_typed c)

/-- A readback entered at a tag is the capture-free loop entered at that tag. -/
theorem rb_core (d : PollTable) {t : Tm signature.Instr} (ht : Tm.BranchValue [Bit] t CaptTags)
    (shape : ofRegion d.readback.property =
      ofRegion (seqValueBranches
        (ValueBranches.br (ℓ := 0) (L := [Silmaril.coprod Bit CaptState]) rfl (.inr (.pair (.var (i := 0) rfl) ht)))
        (caseValueBranches idBit (loopRegion_typed (poll_disp_typed d))))) :
    ofRegion d.readback.property =
      ofRegion (r := .br 0 t) (.br rfl ht) ≫ iterate (freeStep (free_typed d false) (free_typed d true)) := by
  have hloop := loopRegion_typed (poll_disp_typed d)
  have ha : Tm.BranchValue [Bit] (.pair (.var 0) t : Tm signature.Instr) CaptState := .pair (.var rfl) ht
  have hbr : ValueBranches [Bit] (.br 0 (.pair (.var 0) t) : Region signature.Instr) [CaptState] := .br rfl ha
  have s₁ := case_inr_arrow ha idBit hloop
  have s₂ := ofRegion_comp hbr hloop (seqValueBranches hbr hloop)
  have s₃ := iterate_exact (poll_disp_typed d)
  have s₄ := two_row_drop (row0_typed d) (row1_typed d) captDead.property (free_typed d false) (free_typed d true)
    (row0_lifted d) (row1_lifted d) (poll_disp_typed d)
  have hbody : Region.HasType [CaptTags, Bit, Bit] (.br 0 (.var 0) : Region signature.Instr) [CaptTags] :=
    (ValueBranches.br (ℓ := 0) rfl (.var rfl)).hasType
  have s₅ : ofRegion hbr ≫ productSnd (ofType (Φ := signature.Instr) Bit) (ofType CaptTags) =
      ofRegion (r := .br 0 t) (.br rfl ht) :=
    (ofRegion_comp hbr (productSndBranches Bit CaptTags)
      (seqValueBranches hbr (productSndBranches Bit CaptTags))).trans
      ((Paper.TypeCategory.ofRegion_eq_iff _ _).mpr
        (.productBeta (.let₂Beta (A := Bit) (B := CaptTags) (.var rfl) ht hbody)))
  exact shape.trans (s₁.trans (s₂.symm.trans ((congrArg (ofRegion hbr ≫ ·) (s₃.symm.trans s₄)).trans
    ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ iterate (freeStep (free_typed d false) (free_typed d true))) s₅)))))

theorem readback_tag (d : PollTable) :
    ofRegion d.readback.property =
      ofRegion (rowTagR_typed d.start) ≫ iterate (freeStep (free_typed d false) (free_typed d true)) := by
  obtain ⟨label, branch, start⟩ := d
  cases start
  · exact rb_core _ (.inl (.var (i := 0) rfl)) rfl
  · exact rb_core _ (.inr (.inl (.var (i := 0) rfl))) rfl

/-! ## The tags and the packed state of two rows -/

local notation "P'" => Silmaril.coprod Bit Silmaril.empty

theorem tag_arrow_false : ofRegion (rowTagR_typed false) = sumInl (Φ := signature.Instr) Bit P' :=
  tagHeadG_arrow (A := Bit)

theorem tag_arrow_true :
    ofRegion (rowTagR_typed true) = sumInl (Φ := signature.Instr) Bit Silmaril.empty ≫ sumInr Bit P' :=
  (br_inr (X := Bit) (A := Bit) (B := P') (.inl (.var rfl))).trans
    (congrArg (· ≫ (coprod.inr ≫ (sumIso (Φ := signature.Instr) Bit P').inv))
      ((br_inl (.var rfl)).trans ((congrArg (· ≫ _) (ofRegion_id Bit)).trans (Category.id_comp _))))

section FreeTags

variable {β₀ β₁ : Region signature.Instr} (h₀ : ValueBranches [Bit] β₀ [Silmaril.coprod Bit CaptTags])
  (h₁ : ValueBranches [Bit] β₁ [Silmaril.coprod Bit CaptTags])

theorem free_tag_false :
    ofRegion (rowTagR_typed false) ≫ freeStep h₀ h₁ =
      ofRegion h₀ ≫ (sumIso (Φ := signature.Instr) Bit CaptTags).hom := by
  rw [tag_arrow_false]
  unfold freeStep sumInl
  simp
  rfl

theorem free_tag_true :
    ofRegion (rowTagR_typed true) ≫ freeStep h₀ h₁ =
      ofRegion h₁ ≫ (sumIso (Φ := signature.Instr) Bit CaptTags).hom := by
  rw [tag_arrow_true]
  unfold freeStep sumInl sumInr
  simp
  rfl

end FreeTags

/-- From a packed state to its tag. -/
def untag (i : Fin 2) : Region signature.Instr :=
  seqRegion (unpackExits [Bit]) (.br 0 (rowTag (pairBit i)))

theorem untag_typed (i : Fin 2) : ValueBranches [State] (untag i) [CaptTags] :=
  seqRegion_typed unpack_typed (rowTagR_typed (pairBit i))

noncomputable def toTags : ofType (Φ := signature.Instr) (States 1) ⟶ ofType CaptTags :=
  ofRegion (dispatch_typed 1 untag_typed)

theorem state_toTags (c : Bool) :
    (ofRegion bitState_typed ≫ injArr 1 (pairIdx c)) ≫ toTags = ofRegion (rowTagR_typed c) := by
  cases c <;>
    exact (Category.assoc _ _ _).trans
      ((congrArg (ofRegion bitState_typed ≫ ·) (inj_dispatch 1 untag_typed _)).trans
        ((congrArg (ofRegion bitState_typed ≫ ·)
          (ofRegion_comp unpack_typed (rowTagR_typed _) (untag_typed _)).symm).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (· ≫ ofRegion (rowTagR_typed _)) pack_unpack).trans (Category.id_comp _)))))

/-- From a tag to the packed state. -/
def toStatesR : Region signature.Instr :=
  .case (.var 0) (.br 0 (.inl (.inl (.var 0))))
    (.case (.var 0) (.br 0 (.inr (.inl (.var 0)))) (.br 0 (.inl (.inl (.inl .unit)))))

theorem deadState_typed :
    ValueBranches [Silmaril.empty] (.br 0 (.inl (.inl (.inl .unit))) : Region signature.Instr) [States 1] :=
  .br rfl (.inl (.inl (.inl .unit)))

theorem toStates_typed : ValueBranches [CaptTags] toStatesR [States 1] :=
  caseValueBranches (injBit_typed false) (caseValueBranches (injBit_typed true) deadState_typed)

theorem tag_toStates : (c : Bool) → ofRegion (rowTagR_typed c) ≫ ofRegion toStates_typed = ofRegion (injBit_typed c)
  | false =>
    (ofRegion_comp (rowTagR_typed false) toStates_typed (seqValueBranches (rowTagR_typed false) toStates_typed)).trans
      ((case_inl_arrow (X := Bit) (t := (.var 0 : Tm signature.Instr)) (.var (i := 0) rfl) (injBit_typed false)
        (caseValueBranches (injBit_typed true) deadState_typed)).trans
        ((ofRegion_comp idBit (injBit_typed false) (seqValueBranches idBit (injBit_typed false))).symm.trans
          (by rw [ofRegion_id, Category.id_comp])))
  | true =>
    (ofRegion_comp (rowTagR_typed true) toStates_typed (seqValueBranches (rowTagR_typed true) toStates_typed)).trans
      ((case_inr_arrow (X := Bit) (A := Bit) (t := (.inl (.var 0) : Tm signature.Instr)) (.inl (.var (i := 0) rfl))
        (injBit_typed false) (caseValueBranches (injBit_typed true) deadState_typed)).trans
        ((case_inl_arrow (X := Bit) (B := Silmaril.empty) (t := (.var 0 : Tm signature.Instr)) (.var (i := 0) rfl)
          (injBit_typed true) deadState_typed).trans
          ((ofRegion_comp idBit (injBit_typed true) (seqValueBranches idBit (injBit_typed true))).symm.trans
            (by rw [ofRegion_id, Category.id_comp]))))

/-- A tag sent to the packed state and back is the tag. -/
theorem tags_roundtrip : ofRegion toStates_typed ≫ toTags = 𝟙 (ofType (Φ := signature.Instr) CaptTags) := by
  have a := coprod_desc_ofRegion (injBit_typed false) (caseValueBranches (injBit_typed true) deadState_typed)
  have b := coprod_desc_ofRegion (injBit_typed true) deadState_typed
  have s₀ : ofRegion (injBit_typed false) ≫ toTags = sumInl (Φ := signature.Instr) Bit P' :=
    (congrArg (· ≫ toTags) (injBit_arrow false)).trans ((state_toTags false).trans tag_arrow_false)
  have s₁ : ofRegion (injBit_typed true) ≫ toTags =
      sumInl (Φ := signature.Instr) Bit Silmaril.empty ≫ sumInr Bit P' :=
    (congrArg (· ≫ toTags) (injBit_arrow true)).trans ((state_toTags true).trans tag_arrow_true)
  have e : ofRegion toStates_typed = (sumIso (Φ := signature.Instr) Bit P').hom ≫
      coprod.desc (ofRegion (injBit_typed false)) ((sumIso (Φ := signature.Instr) Bit Silmaril.empty).hom ≫
        coprod.desc (ofRegion (injBit_typed true)) (ofRegion deadState_typed)) :=
    a.symm.trans (congrArg (fun v => (sumIso (Φ := signature.Instr) Bit P').hom ≫
      coprod.desc (ofRegion (injBit_typed false)) v) b.symm)
  have hdesc : coprod.desc (ofRegion (injBit_typed false)) ((sumIso (Φ := signature.Instr) Bit Silmaril.empty).hom ≫
      coprod.desc (ofRegion (injBit_typed true)) (ofRegion deadState_typed)) ≫ toTags =
      (sumIso (Φ := signature.Instr) Bit P').inv := by
    apply coprod.hom_ext
    · rw [← Category.assoc, coprod.inl_desc]
      exact s₀
    · rw [← Category.assoc, coprod.inr_desc, Category.assoc]
      refine (Iso.eq_inv_comp _).mp ?_
      apply coprod.hom_ext
      · rw [← Category.assoc, coprod.inl_desc]
        exact s₁.trans (Category.assoc _ _ _)
      · exact (Paper.TypeCategory.emptyIsInitial (Φ := signature.Instr)).hom_ext _ _
  exact (congrArg (· ≫ toTags) e).trans ((Category.assoc _ _ _).trans
    ((congrArg ((sumIso (Φ := signature.Instr) Bit P').hom ≫ ·) hdesc).trans (Iso.hom_inv_id _)))

/-! ## One row: the free row and the router row -/

theorem goVar_typed (c : Bool) :
    ValueBranches [Bit] (.br 0 (.inr (injTm 1 (pairIdx c) (.inl (.var 0)))) : Region signature.Instr)
      [Silmaril.coprod Bit (States 1)] :=
  .br rfl (.inr (injTm_typed (.inl (.var rfl)) 1 (pairIdx c)))

/-- A tagged leaf, sent to the packed state, is the two actions of the
leaf on the two payloads. Default Paper: a Bit is the case of its two
constructors. -/
theorem pollLeaf_post : (b : PollLeaf) →
    ofRegion (seqValueBranches (freeLeaf_typed (Γ := []) b) (postRegion_typed (B := Bit) toStates_typed)) =
      ofRegion (caseValueBranches (act_typed 1 (b.toAct false)) (act_typed 1 (b.toAct true)))
  | .exit =>
    (ofRegion_comp (freeLeaf_typed (Γ := []) .exit) (postRegion_typed (B := Bit) toStates_typed) _).symm.trans
      ((postR_inl toStates_typed (.var (i := 0) rfl)).trans (bit_eta _))
  | .goto false =>
    (ofRegion_comp (freeLeaf_typed (Γ := []) (.goto false))
      (postRegion_typed (B := Bit) toStates_typed) _).symm.trans
      ((postR_inr toStates_typed (rowTag_typed false)).trans
        ((congrArg (· ≫ (coprod.inr ≫ (sumIso (Φ := signature.Instr) Bit (States 1)).inv))
          (tag_toStates false)).trans
          ((br_inr (injTm_typed (.inl (.var (i := 0) rfl)) 1 (pairIdx false))).symm.trans
            (bit_eta (goVar_typed false)))))
  | .goto true =>
    (ofRegion_comp (freeLeaf_typed (Γ := []) (.goto true))
      (postRegion_typed (B := Bit) toStates_typed) _).symm.trans
      ((postR_inr toStates_typed (rowTag_typed true)).trans
        ((congrArg (· ≫ (coprod.inr ≫ (sumIso (Φ := signature.Instr) Bit (States 1)).inv))
          (tag_toStates true)).trans
          ((br_inr (injTm_typed (.inl (.var (i := 0) rfl)) 1 (pairIdx true))).symm.trans
            (bit_eta (goVar_typed true)))))

theorem route_left (ac : Bool → Bool → Act 1) :
    ofRegion (seqValueBranches brInl_typed (routerRoute_typed 1 ac)) =
      ofRegion (caseValueBranches (act_typed 1 (ac false false)) (act_typed 1 (ac false true))) :=
  (case_inl_arrow (X := Bit) (B := State) (t := (.var 0 : Tm signature.Instr)) (.var (i := 0) rfl)
    (bitSplit_typed 1 _ _) (stateSplit_typed 1 _ _)).trans
    ((ofRegion_comp idBit (bitSplit_typed 1 _ _) (seqValueBranches idBit (bitSplit_typed 1 _ _))).symm.trans
      (by rw [ofRegion_id, Category.id_comp]))

theorem route_right (ac : Bool → Bool → Act 1) :
    ofRegion (seqValueBranches brInrInl_typed (routerRoute_typed 1 ac)) =
      ofRegion (caseValueBranches (act_typed 1 (ac true false)) (act_typed 1 (ac true true))) :=
  (case_inr_arrow (X := Bit) (A := Bit) (t := (.inl (.var 0) : Tm signature.Instr))
    (.inl (.var (i := 0) rfl)) (bitSplit_typed 1 _ _) (stateSplit_typed 1 _ _)).trans
    ((case_inl_arrow (X := Bit) (B := Silmaril.empty) (t := (.var 0 : Tm signature.Instr)) (.var (i := 0) rfl)
      (bitSplit_typed 1 _ _) (dead_typed 1)).trans
      ((ofRegion_comp idBit (bitSplit_typed 1 _ _) (seqValueBranches idBit (bitSplit_typed 1 _ _))).symm.trans
        (by rw [ofRegion_id, Category.id_comp])))

/-- The free row of a block, sent to the packed state, is the packed
request of its label followed by the routing of its actions. Default
Paper: congruence under the request. -/
theorem free_row_step (l : Bool) (b₁ b₂ : PollLeaf) :
    ofRegion (seqValueBranches (freeRow_typed l b₁ b₂) (postRegion_typed (B := Bit) toStates_typed)) =
      ofRegion (seqValueBranches (labelPoll l).program.typed.packExits
        (routerRoute_typed 1 (leafAct b₁ b₂))) := by
  have left := Paper.Eqv.renameVars ((Paper.TypeCategory.ofRegion_eq_iff _ _).mp
    ((pollLeaf_post b₁).trans (route_left (leafAct b₁ b₂)).symm)) (headerRen (S := Bit))
  have right := Paper.Eqv.renameVars ((Paper.TypeCategory.ofRegion_eq_iff _ _).mp
    ((pollLeaf_post b₂).trans (route_right (leafAct b₁ b₂)).symm)) (headerRen (S := Bit))
  have hop : Tm.HasType [Bit] (.op (.ask l) (.var 0) : Tm signature.Instr) (Silmaril.coprod Bit Bit) :=
    .op (.var (i := 0) rfl)
  rcases b₁ with _ | (_ | _) <;> rcases b₂ with _ | (_ | _) <;>
    exact (Paper.TypeCategory.ofRegion_eq_iff _ _).mpr (Paper.Eqv.case hop left right)

theorem row_poll (l : Bool) (ac : Bool → Bool → Act 1) :
    ofRegion bitState_typed ≫ ofRegion (routerRow_typed 1 (labelPoll l).program ac) =
      ofRegion (seqValueBranches (labelPoll l).program.typed.packExits (routerRoute_typed 1 ac)) := by
  rw [← ofRegion_comp (step_typed (labelPoll l).program) (routerRoute_typed 1 ac)
      (routerRow_typed 1 (labelPoll l).program ac),
    ← ofRegion_comp unpack_typed (labelPoll l).program.typed.packExits (step_typed (labelPoll l).program),
    ← Category.assoc, ← Category.assoc, pack_unpack, Category.id_comp]
  exact ofRegion_comp (labelPoll l).program.typed.packExits (routerRoute_typed 1 ac) _

/-! ## The loop on the tags and the packed loop of the router table -/

theorem conj_row (d : PollTable) (c : Bool) :
    ofRegion (rowTagR_typed c) ≫ (freeStep (free_typed d false) (free_typed d true) ≫
        coprod.map (𝟙 _) (ofRegion toStates_typed)) =
      (ofRegion bitState_typed ≫ ofRegion (d.router.rows_typed (pairIdx c))) ≫
        (sumIso (Φ := signature.Instr) Bit (States 1)).hom := by
  have pa := post_arrow (X := CaptTags) (Y := States 1) toStates_typed
  cases c
  · have key : ofRegion (free_typed d false) ≫ ((sumIso (Φ := signature.Instr) Bit CaptTags).hom ≫
        coprod.map (𝟙 _) (ofRegion toStates_typed) ≫ (sumIso (Φ := signature.Instr) Bit (States 1)).inv) =
        ofRegion bitState_typed ≫ ofRegion (d.router.rows_typed (pairIdx false)) :=
      (congrArg (ofRegion (free_typed d false) ≫ ·) pa.symm).trans
        ((ofRegion_comp (free_typed d false) (postRegion_typed (B := Bit) toStates_typed) _).trans
          ((free_row_step (d.label false) (d.branch false false) (d.branch false true)).trans
            (row_poll (d.label false) (leafAct (d.branch false false) (d.branch false true))).symm))
    rw [← Category.assoc, free_tag_false, ← key]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · have key : ofRegion (free_typed d true) ≫ ((sumIso (Φ := signature.Instr) Bit CaptTags).hom ≫
        coprod.map (𝟙 _) (ofRegion toStates_typed) ≫ (sumIso (Φ := signature.Instr) Bit (States 1)).inv) =
        ofRegion bitState_typed ≫ ofRegion (d.router.rows_typed (pairIdx true)) :=
      (congrArg (ofRegion (free_typed d true) ≫ ·) pa.symm).trans
        ((ofRegion_comp (free_typed d true) (postRegion_typed (B := Bit) toStates_typed) _).trans
          ((free_row_step (d.label true) (d.branch true false) (d.branch true true)).trans
            (row_poll (d.label true) (leafAct (d.branch true false) (d.branch true true))).symm))
    rw [← Category.assoc, free_tag_true, ← key]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The step on the tags, conjugated by the two maps, is the dispatcher
step of the router table. -/
theorem conj_step (d : PollTable) :
    toTags ≫ (freeStep (free_typed d false) (free_typed d true) ≫ coprod.map (𝟙 _) (ofRegion toStates_typed)) =
      ofRegion (dispatch_typed 1 d.router.rows_typed) ≫ (sumIso (Φ := signature.Instr) Bit (States 1)).hom := by
  have main : ∀ c : Bool,
      ofRegion bitState_typed ≫ injArr 1 (pairIdx c) ≫ toTags ≫
          (freeStep (free_typed d false) (free_typed d true) ≫ coprod.map (𝟙 _) (ofRegion toStates_typed)) =
        ofRegion bitState_typed ≫ injArr 1 (pairIdx c) ≫
          ofRegion (dispatch_typed 1 d.router.rows_typed) ≫ (sumIso (Φ := signature.Instr) Bit (States 1)).hom :=
    fun c => by
      have r := inj_dispatch 1 d.router.rows_typed (pairIdx c)
      have t := (congrArg (· ≫ (freeStep (free_typed d false) (free_typed d true) ≫
        coprod.map (𝟙 _) (ofRegion toStates_typed))) (state_toTags c)).trans (conj_row d c)
      rw [← r] at t
      simpa only [Category.assoc] using t
  apply inj_ext 1
  intro i
  apply state_ext_bit
  match i with
  | 0 => exact main false
  | 1 => exact main true

theorem poll_free_loop (d : PollTable) :
    iterate (ofRegion (dispatch_typed 1 d.router.rows_typed) ≫ (sumIso (Φ := signature.Instr) Bit (States 1)).hom) =
      toTags ≫ iterate (freeStep (free_typed d false) (free_typed d true)) := by
  have roll := iterate_roll toTags
    (freeStep (free_typed d false) (free_typed d true) ≫ coprod.map (𝟙 _) (ofRegion toStates_typed))
  have back : (freeStep (free_typed d false) (free_typed d true) ≫
      coprod.map (𝟙 _) (ofRegion toStates_typed)) ≫ coprod.map (𝟙 _) toTags =
      freeStep (free_typed d false) (free_typed d true) := by
    simp only [Category.assoc, coprod.map_map, Category.comp_id, tags_roundtrip, coprod.map_id_id]
    exact Category.comp_id _
  rw [← conj_step d, roll, back]

/-- The packed readback is the router table entered at the start row,
on the input as its Bit. Default Paper. -/
theorem poll_readback_entered (d : PollTable) :
    ofRegion d.readback.property =
      ofRegion bitState_typed ≫ ofRegion (d.router.entered_typed (pairIdx d.start)) :=
  (readback_tag d).trans
    ((congrArg (· ≫ iterate (freeStep (free_typed d false) (free_typed d true))) (state_toTags d.start).symm).trans
      ((Category.assoc _ _ _).trans
        ((congrArg ((ofRegion bitState_typed ≫ injArr 1 (pairIdx d.start)) ≫ ·)
          ((poll_free_loop d).symm.trans (iterate_exact (dispatch_typed 1 d.router.rows_typed)))).trans
          ((Category.assoc _ _ _).trans (congrArg (ofRegion bitState_typed ≫ ·)
            (dispatchEntered_arrow d.router.rows_typed (pairIdx d.start)).symm)))))

theorem poll_readback_eqv (d : PollTable) :
    Paper.Eqv [Bit] d.readback.val (seqRegion (.br 0 (.inl (.var 0))) (d.router.entered (pairIdx d.start))) [Bit] :=
  (Paper.TypeCategory.ofRegion_eq_iff d.readback.property
    (seqRegion_typed bitState_typed (d.router.entered_typed (pairIdx d.start)))).mp
    ((poll_readback_entered d).trans (ofRegion_comp bitState_typed (d.router.entered_typed (pairIdx d.start)) _))

/-! ## The source, its certificate and completeness -/

theorem poll_source_readback (d : PollTable) :
    Paper.WithAdministrativeReturns.WithGuardedTablePacking.Eqv false [Bit] d.source d.readback.val [Bit] :=
  Paper.WithAdministrativeReturns.WithGuardedTablePacking.pack false (fun _ : Fin 2 => Bit)
    (startEntry_typed d.start) d.blocks_typed

theorem poll_source_entered (d : PollTable) :
    Paper.WithAdministrativeReturns.WithGuardedTablePacking.Eqv false [Bit] d.source
      (seqRegion (.br 0 (.inl (.var 0))) (d.router.entered (pairIdx d.start))) [Bit] :=
  (poll_source_readback d).trans (.paper (poll_readback_eqv d))

theorem q_poll_source (d : PollTable) :
    QLit d.source_typed = QLit bitState_typed ≫ QLit (d.router.entered_typed (pairIdx d.start)) :=
  ((Paper.Extension.Singleton.ofRegion_eq_iff N d.source_typed
    (seqRegion_typed bitState_typed (d.router.entered_typed (pairIdx d.start)))).2
    (Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.ofTablePacking false
      (poll_source_entered d))).trans (q_comp bitState_typed (d.router.entered_typed (pairIdx d.start)))

theorem poll_spin (d : PollTable) :
    Router.ofSpin (fun i => some (d.label (pairBit i))) d.act = d.router := rfl

/-- The certificate: at each constant input the source is its router
table entered at the start row with that input. -/
theorem poll_bitPointed (d : PollTable) :
    BitPointed d.source (fun i => some (d.label (pairBit i))) d.act (fun _ => pairIdx d.start) := by
  intro q
  rw [poll_spin]
  apply (Paper.Extension.Singleton.ofRegion_eq_iff N (atInput_typed q d.source_typed)
    (constEntry_typed q (d.router.entered_typed (pairIdx d.start)))).1
  exact (q_comp (bitU_typed q) d.source_typed).trans
    ((congrArg (QLit (bitU_typed q) ≫ ·) (q_poll_source d)).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ QLit (d.router.entered_typed (pairIdx d.start)))
          (((π).map_comp _ _).symm.trans (congrArg (π).map (const_arrow q).symm))).trans
          (q_comp (const_typed q) (d.router.entered_typed (pairIdx d.start))).symm)))

open Paper.WithAdministrativeReturns.WithGuardedTablePacking (Valid) in
/-- Two sources of the fragment are equal at the source entry exactly
when they are valid in every supported model. -/
theorem poll_complete (d d' : PollTable) :
    Eqv false [Bit] d.source d'.source [Bit] ↔ Valid d.source_typed.hasType d'.source_typed.hasType :=
  bit_source_complete (tidy_of_labelled fun _ => Option.some_ne_none _)
    (tidy_of_labelled fun _ => Option.some_ne_none _) d.source_typed d'.source_typed
    (poll_bitPointed d) (poll_bitPointed d')

/-- Two sources are equal exactly when their router tables are equal at
the start rows. -/
theorem poll_eqv_iff_entered (d d' : PollTable) :
    Eqv false [Bit] d.source d'.source [Bit] ↔
      Eqv false [State] (d.router.entered (pairIdx d.start)) (d'.router.entered (pairIdx d'.start)) [Bit] := by
  have he := d.router.entered_typed (pairIdx d.start)
  have he' := d'.router.entered_typed (pairIdx d'.start)
  constructor
  · intro e
    apply (Paper.Extension.Singleton.ofRegion_eq_iff N he he').1
    apply q_state_ext he he'
    exact (q_comp bitState_typed he).trans ((q_poll_source d).symm.trans
      (((Paper.Extension.Singleton.ofRegion_eq_iff N d.source_typed d'.source_typed).2 e).trans
        ((q_poll_source d').trans (q_comp bitState_typed he').symm)))
  · intro e
    apply (Paper.Extension.Singleton.ofRegion_eq_iff N d.source_typed d'.source_typed).1
    exact (q_poll_source d).trans ((congrArg (QLit bitState_typed ≫ ·)
      ((Paper.Extension.Singleton.ofRegion_eq_iff N he he').2 e)).trans (q_poll_source d').symm)

/-- Exactly when the two tables are bisimilar from their start rows. -/
theorem poll_eqv_iff_bisim (d d' : PollTable) :
    Eqv false [Bit] d.source d'.source [Bit] ↔
      ∃ R : Fin 2 → Fin 2 → Prop, (∀ x y, R x y → d.label (pairBit x) = d'.label (pairBit y)) ∧
        (∀ x y, R x y → ∀ tag pl, Act.Rel R (d.act x tag pl) (d'.act y tag pl)) ∧
        R (pairIdx d.start) (pairIdx d'.start) :=
  (poll_eqv_iff_entered d d').trans
    (Router.labels_eqv_iff (fun i => d.label (pairBit i)) d.act (fun i => d'.label (pairBit i)) d'.act
      (pairIdx d.start) (pairIdx d'.start))

/-! ## Tables with different row actions -/

theorem self_swap (l : Bool) : Eqv false [Bit] (selfTable l).source (swapTable l).source [Bit] :=
  (poll_eqv_iff_bisim _ _).2 ⟨fun _ _ => True, fun _ _ _ => rfl, fun _ _ _ tag _ => by
    cases tag
    · exact rfl
    · exact ⟨rfl, trivial⟩, trivial⟩

theorem self_never (l l' : Bool) : ¬ Eqv false [Bit] (selfTable l).source (neverTable l').source [Bit] :=
  fun e => by
    obtain ⟨R, -, ha, r⟩ := (poll_eqv_iff_bisim _ _).1 e
    exact ha _ _ r false false

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables

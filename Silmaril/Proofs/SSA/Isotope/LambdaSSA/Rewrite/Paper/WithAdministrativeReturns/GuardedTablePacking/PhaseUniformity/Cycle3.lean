module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Packed.Product.Flat.BitEntry.Tags.Cycle.Defs
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.TagsRouter

/-! # The certificate of a cycle of three polling blocks -/

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

theorem cyc3_flat_typed (l : Bool) :
    LambdaSSA.FiniteCFG.HasType (.snoc .nil Bit) (fun _ : Fin 3 => Bit) (fun _ : Fin 1 => Bit) (cycleFlat l) where
  entry := .br (i := 0) .bv
  block := fun i => match i with
    | 0 => .case (A := Bit) (B := Bit) (.op .bv) (.br (i := 3) .bv) (.br (i := 1) .bv)
    | 1 => .case (A := Bit) (B := Bit) (.op .bv) (.br (i := 3) .bv) (.br (i := 2) .bv)
    | 2 => .case (A := Bit) (B := Bit) (.op .bv) (.br (i := 3) .bv) (.br (i := 0) .bv)

/-! ## The rows of the readback -/

/-- A capture-free leaf, whiskered by the captured input and followed by
`dropCase`. -/
def liftLeaf (x : Region signature.Instr) : Region signature.Instr :=
  ((x.renameVars (lift (lift (Nat.succ ∘ Nat.succ)))).lsubst
      (liftLSubstVars (fun _ => .br 0 (.pair (.var 2) (.var 0))))).lsubst
    (liftLSubstVars (liftLSubstVars (liftLSubstVars (fun _ => dropCase.renameVars (lift Nat.succ)))))

/-- A leaf of a readback row of a table with three blocks. -/
def rbLeaf3 (ℓ : Nat) : Region signature.Instr :=
  ((((carryExit 1 3 ℓ : Region signature.Instr).renameVars (lift Nat.succ)).substVars
    (Tm.singleSubst (.var 0))).renameVars (lift (lift (lift Nat.succ))))

theorem cyc_exit_lift :
    Paper.Eqv [Bit, Bit, Bit, Silmaril.product Bit Bit] (liftLeaf (.br 0 (.inl (.var 0)))) (rbLeaf3 3)
      [Silmaril.coprod Bit (Silmaril.product Bit (BitTags 2))] :=
  drop_inl (X := Bit) (A := BitTags 2) (i := 2) rfl (.var (i := 0) rfl)

theorem cyc_goto_lift : (j : Fin 3) →
    Paper.Eqv [Bit, Bit, Bit, Silmaril.product Bit Bit]
      (liftLeaf (.br 0 (.inr (packedExitArg j.val (.var 0))))) (rbLeaf3 j.val)
      [Silmaril.coprod Bit (Silmaril.product Bit (BitTags 2))]
  | 0 => drop_inr (X := Bit) (B := Bit) (i := 2) rfl (.inl (.var (i := 0) rfl))
  | 1 => drop_inr (X := Bit) (B := Bit) (i := 2) rfl (.inr (.inl (.var (i := 0) rfl)))
  | 2 => drop_inr (X := Bit) (B := Bit) (i := 2) rfl (.inr (.inr (.inl (.var (i := 0) rfl))))

/-- The readback row of a block is its capture-free row whiskered by the
captured input and followed by `dropCase`. Default Paper. -/
theorem cyc_row_lift (l : Bool) (i : Fin 3) :
    Paper.Eqv [Silmaril.product Bit Bit] (seqRegion (whiskerLeftRegion (cycleFree l i)) dropCase)
      (Paper.RetainedLet.unpackBody ((cycleBlocks l i).lsubst (carryExit 1 3)))
      [Silmaril.coprod Bit (Silmaril.product Bit (BitTags 2))] :=
  .let₂ (A := Bit) (B := Bit) (.var rfl)
    (.case (A := Bit) (B := Bit) (.op (.var (i := 0) rfl)) cyc_exit_lift (cyc_goto_lift (cycNext i)))

/-! ## From tags to states -/

theorem dead3_typed :
    ValueBranches [Silmaril.empty] (.br 0 (.inl (.inl (.inl .unit))) : Region signature.Instr) [States 2] :=
  .br rfl (.inl (.inl (.inl .unit)))

noncomputable def cycR2 :
    {r : Region signature.Instr // ValueBranches [Silmaril.coprod Bit Silmaril.empty] r [States 2]} :=
  ⟨_, caseValueBranches (rowState_typed (K := 2) 2) dead3_typed⟩

noncomputable def cycR1 : {r : Region signature.Instr //
    ValueBranches [Silmaril.coprod Bit (Silmaril.coprod Bit Silmaril.empty)] r [States 2]} :=
  ⟨_, caseValueBranches (rowState_typed (K := 2) 1) cycR2.property⟩

/-- From a tag of three blocks to a state of three rows. -/
noncomputable def toStates3 : {r : Region signature.Instr // ValueBranches [BitTags 2] r [States 2]} :=
  ⟨_, caseValueBranches (rowState_typed (K := 2) 0) cycR1.property⟩

theorem seq_idBit {D : Ty Empty} {k : Region signature.Instr} (h : ValueBranches [Bit] k [D]) :
    ofRegion (seqValueBranches idBit h) = ofRegion h :=
  (ofRegion_comp idBit h (seqValueBranches idBit h)).symm.trans (by rw [ofRegion_id, Category.id_comp])

theorem cyc_tags : (i : Fin 3) →
    ofRegion (bitTag_typed (K := 2) i) ≫ ofRegion toStates3.property = ofRegion (rowState_typed (K := 2) i)
  | 0 =>
    (ofRegion_comp (bitTag_typed (K := 2) 0) toStates3.property
      (seqValueBranches (bitTag_typed (K := 2) 0) toStates3.property)).trans
      ((case_inl_arrow (X := Bit) (t := (.var 0 : Tm signature.Instr)) (.var (i := 0) rfl)
        (rowState_typed (K := 2) 0) cycR1.property).trans (seq_idBit _))
  | 1 =>
    (ofRegion_comp (bitTag_typed (K := 2) 1) toStates3.property
      (seqValueBranches (bitTag_typed (K := 2) 1) toStates3.property)).trans
      ((case_inr_arrow (X := Bit) (A := Bit) (t := (.inl (.var 0) : Tm signature.Instr)) (.inl (.var (i := 0) rfl))
        (rowState_typed (K := 2) 0) cycR1.property).trans
        ((case_inl_arrow (X := Bit) (t := (.var 0 : Tm signature.Instr)) (.var (i := 0) rfl)
          (rowState_typed (K := 2) 1) cycR2.property).trans (seq_idBit _)))
  | 2 =>
    (ofRegion_comp (bitTag_typed (K := 2) 2) toStates3.property
      (seqValueBranches (bitTag_typed (K := 2) 2) toStates3.property)).trans
      ((case_inr_arrow (X := Bit) (A := Bit) (t := (.inr (.inl (.var 0)) : Tm signature.Instr))
        (.inr (.inl (.var (i := 0) rfl))) (rowState_typed (K := 2) 0) cycR1.property).trans
        ((case_inr_arrow (X := Bit) (A := Bit) (t := (.inl (.var 0) : Tm signature.Instr))
          (.inl (.var (i := 0) rfl)) (rowState_typed (K := 2) 1) cycR2.property).trans
          ((case_inl_arrow (X := Bit) (B := Silmaril.empty) (t := (.var 0 : Tm signature.Instr))
            (.var (i := 0) rfl) (rowState_typed (K := 2) 2) dead3_typed).trans (seq_idBit _))))

/-! ## One row: the capture-free row and the router row -/

section AnyK

variable {K : Nat}

theorem route_leftK (ac : Bool → Bool → Act K) :
    ofRegion (seqValueBranches brInl_typed (routerRoute_typed K ac)) =
      ofRegion (caseValueBranches (act_typed K (ac false false)) (act_typed K (ac false true))) :=
  (case_inl_arrow (X := Bit) (B := State) (t := (.var 0 : Tm signature.Instr)) (.var (i := 0) rfl)
    (bitSplit_typed K _ _) (stateSplit_typed K _ _)).trans (seq_idBit _)

theorem route_rightK (ac : Bool → Bool → Act K) :
    ofRegion (seqValueBranches brInrInl_typed (routerRoute_typed K ac)) =
      ofRegion (caseValueBranches (act_typed K (ac true false)) (act_typed K (ac true true))) :=
  (case_inr_arrow (X := Bit) (A := Bit) (t := (.inl (.var 0) : Tm signature.Instr))
    (.inl (.var (i := 0) rfl)) (bitSplit_typed K _ _) (stateSplit_typed K _ _)).trans
    ((case_inl_arrow (X := Bit) (B := Silmaril.empty) (t := (.var 0 : Tm signature.Instr)) (.var (i := 0) rfl)
      (bitSplit_typed K _ _) (dead_typed K)).trans (seq_idBit _))

theorem row_pollK (l : Bool) (ac : Bool → Bool → Act K) :
    ofRegion bitState_typed ≫ ofRegion (routerRow_typed K (labelPoll l).program ac) =
      ofRegion (seqValueBranches (labelPoll l).program.typed.packExits (routerRoute_typed K ac)) := by
  rw [← ofRegion_comp (step_typed (labelPoll l).program) (routerRoute_typed K ac)
      (routerRow_typed K (labelPoll l).program ac),
    ← ofRegion_comp unpack_typed (labelPoll l).program.typed.packExits (step_typed (labelPoll l).program),
    ← Category.assoc, ← Category.assoc, pack_unpack, Category.id_comp]
  exact ofRegion_comp (labelPoll l).program.typed.packExits (routerRoute_typed K ac) _

end AnyK

theorem cycExit_typed :
    ValueBranches [Bit] (.br 0 (.inl (.var 0)) : Region signature.Instr) [Silmaril.coprod Bit (BitTags 2)] :=
  .br rfl (.inl (.var rfl))

theorem cycGoto_typed (j : Fin 3) :
    ValueBranches [Bit] (.br 0 (.inr (packedExitArg j.val (.var 0))) : Region signature.Instr)
      [Silmaril.coprod Bit (BitTags 2)] :=
  .br rfl (.inr (cycTag_value j))

theorem goVar3_typed (j : Fin 3) :
    ValueBranches [Bit] (.br 0 (.inr (injTm 2 j (.inl (.var 0)))) : Region signature.Instr)
      [Silmaril.coprod Bit (States 2)] :=
  .br rfl (.inr (injTm_typed (.inl (.var rfl)) 2 j))

theorem goVar3_eta : (j : Fin 3) →
    ofRegion (goVar3_typed j) =
      ofRegion (caseValueBranches (act_typed 2 (.go j false)) (act_typed 2 (.go j true)))
  | 0 => bit_eta (goVar3_typed 0)
  | 1 => bit_eta (goVar3_typed 1)
  | 2 => bit_eta (goVar3_typed 2)

theorem cyc_leaf_exit :
    ofRegion (seqValueBranches cycExit_typed (postRegion_typed (B := Bit) toStates3.property)) =
      ofRegion (caseValueBranches (act_typed 2 (.ret false)) (act_typed 2 (.ret true))) :=
  (ofRegion_comp cycExit_typed (postRegion_typed (B := Bit) toStates3.property) _).symm.trans
    ((postR_inl toStates3.property (.var (i := 0) rfl)).trans (bit_eta _))

theorem cyc_leaf_goto (j : Fin 3) :
    ofRegion (seqValueBranches (cycGoto_typed j) (postRegion_typed (B := Bit) toStates3.property)) =
      ofRegion (caseValueBranches (act_typed 2 (.go j false)) (act_typed 2 (.go j true))) :=
  (ofRegion_comp (cycGoto_typed j) (postRegion_typed (B := Bit) toStates3.property) _).symm.trans
    ((postR_inr toStates3.property (cycTag_value (Γ := []) j)).trans
      ((congrArg (· ≫ (coprod.inr ≫ (sumIso (Φ := signature.Instr) Bit (States 2)).inv)) (cyc_tags j)).trans
        ((br_inr (injTm_typed (.inl (.var (i := 0) rfl)) 2 j)).symm.trans (goVar3_eta j))))

/-- The capture-free row of a block, sent to the packed state, is the
packed request followed by the routing of the row's actions. -/
theorem cyc_row_step (l : Bool) (i : Fin 3) :
    ofRegion (seqValueBranches (cycleFree_typed l i) (postRegion_typed (B := Bit) toStates3.property)) =
      ofRegion (seqValueBranches (labelPoll l).program.typed.packExits (routerRoute_typed 2 (cycleAct i))) := by
  have left := Paper.Eqv.renameVars ((Paper.TypeCategory.ofRegion_eq_iff _ _).mp
    (cyc_leaf_exit.trans (route_leftK (cycleAct i)).symm)) (headerRen (S := Bit))
  have right := Paper.Eqv.renameVars ((Paper.TypeCategory.ofRegion_eq_iff _ _).mp
    ((cyc_leaf_goto (cycNext i)).trans (route_rightK (cycleAct i)).symm)) (headerRen (S := Bit))
  have hop : Tm.HasType [Bit] (.op (.ask l) (.var 0) : Tm signature.Instr) (Silmaril.coprod Bit Bit) :=
    .op (.var (i := 0) rfl)
  rcases i with ⟨_ | _ | _ | n, hi⟩
  · exact (Paper.TypeCategory.ofRegion_eq_iff _ _).mpr (Paper.Eqv.case hop left right)
  · exact (Paper.TypeCategory.ofRegion_eq_iff _ _).mpr (Paper.Eqv.case hop left right)
  · exact (Paper.TypeCategory.ofRegion_eq_iff _ _).mpr (Paper.Eqv.case hop left right)
  · exact absurd hi (by omega)

theorem cyc_step (l : Bool) (i : Fin 3) :
    ofRegion (cycleFree_typed l i) ≫ ((sumIso (Φ := signature.Instr) Bit (BitTags 2)).hom ≫
        coprod.map (𝟙 _) (ofRegion toStates3.property)) =
      (ofRegion bitState_typed ≫ ofRegion ((cycleRouter l).rows_typed i)) ≫
        (sumIso (Φ := signature.Instr) Bit (States 2)).hom := by
  have pa := post_arrow (X := BitTags 2) (Y := States 2) toStates3.property
  have key : ofRegion (cycleFree_typed l i) ≫ ((sumIso (Φ := signature.Instr) Bit (BitTags 2)).hom ≫
      coprod.map (𝟙 _) (ofRegion toStates3.property) ≫ (sumIso (Φ := signature.Instr) Bit (States 2)).inv) =
      ofRegion bitState_typed ≫ ofRegion ((cycleRouter l).rows_typed i) :=
    (congrArg (ofRegion (cycleFree_typed l i) ≫ ·) pa.symm).trans
      ((ofRegion_comp (cycleFree_typed l i) (postRegion_typed (B := Bit) toStates3.property) _).trans
        ((cyc_row_step l i).trans (row_pollK l (cycleAct i)).symm))
  rw [← key]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The certificate of the cycle. -/
noncomputable def cycleCert (l : Bool) :
    TagCert cycleEntry_typed (cycleBlocks_typed l) (cycleRouter l) 0 where
  free := cycleFree l
  free_typed := cycleFree_typed l
  toStates := ofRegion toStates3.property
  entry := rfl
  rows := fun j => match j with
    | ⟨0, _⟩ => (Paper.TypeCategory.ofRegion_eq_iff _ _).mpr (cyc_row_lift l 0).symm
    | ⟨1, _⟩ => (Paper.TypeCategory.ofRegion_eq_iff _ _).mpr (cyc_row_lift l 1).symm
    | ⟨2, _⟩ => (Paper.TypeCategory.ofRegion_eq_iff _ _).mpr (cyc_row_lift l 2).symm
    | ⟨n + 3, h⟩ => absurd h (by simp)
  tags := cyc_tags
  step := cyc_step l

/-! ## The cycle at its source entry -/

/-- The cycle is its router table entered at row `0`, in the
table-packing quotient. -/
theorem cyc3_source_entered (l : Bool) :
    Paper.WithAdministrativeReturns.WithGuardedTablePacking.Eqv false [Bit] (cycleSource l)
      (seqRegion (.br 0 (.inl (.var 0))) ((cycleRouter l).entered 0)) [Bit] := by
  rw [cycleSource_eq]
  exact cert_source (cycleCert l)

theorem cyc3_bitPointed (l : Bool) :
    BitPointed (cycleSource l) (fun _ => some l) cycleAct (fun _ => (0 : Fin 3)) := by
  rw [cycleSource_eq]
  exact cert_bitPointed (label := fun _ => some l) (act := cycleAct) (cycleCert l)

open Paper.WithAdministrativeReturns.WithGuardedTablePacking (Valid) in
/-- Two cycles are equal at the source entry exactly when they are valid
in every supported model. -/
theorem cyc3_complete (l l' : Bool) :
    Eqv false [Bit] (cycleSource l) (cycleSource l') [Bit] ↔
      Valid (cycleSource_typed l).hasType (cycleSource_typed l').hasType :=
  bit_source_complete (tidy_of_labelled fun _ => Option.some_ne_none _)
    (tidy_of_labelled fun _ => Option.some_ne_none _) (cycleSource_typed l) (cycleSource_typed l')
    (cyc3_bitPointed l) (cyc3_bitPointed l')

open Paper.WithAdministrativeReturns.WithGuardedTablePacking (Valid) in
/-- A cycle of three blocks and a table of the two-block fragment are
equal at the source entry exactly when they are valid in every supported
model. -/
theorem cyc3_poll_complete (l : Bool) (d : PollTable) :
    Eqv false [Bit] (cycleSource l) d.source [Bit] ↔
      Valid (cycleSource_typed l).hasType d.source_typed.hasType :=
  bit_source_complete (tidy_of_labelled fun _ => Option.some_ne_none _)
    (tidy_of_labelled fun _ => Option.some_ne_none _) (cycleSource_typed l) d.source_typed
    (cyc3_bitPointed l) (poll_bitPointed d)

/-- A cycle and a two-block table are equal exactly when their router
tables are equal at the start rows. -/
theorem cyc3_poll_entered (l : Bool) (d : PollTable) :
    Eqv false [Bit] (cycleSource l) d.source [Bit] ↔
      Eqv false [State] ((cycleRouter l).entered 0) (d.router.entered (pairIdx d.start)) [Bit] := by
  rw [cycleSource_eq]
  have hE := (cycleRouter l).entered_typed 0
  have hE' := d.router.entered_typed (pairIdx d.start)
  have hs := cert_typed cycleEntry_typed (cycleBlocks_typed l)
  constructor
  · intro h
    apply (Paper.Extension.Singleton.ofRegion_eq_iff N hE hE').1
    apply q_state_ext hE hE'
    exact (q_comp bitState_typed hE).trans ((q_cert_source (cycleCert l)).symm.trans
      (((Paper.Extension.Singleton.ofRegion_eq_iff N hs d.source_typed).2 h).trans
        ((q_poll_source d).trans (q_comp bitState_typed hE').symm)))
  · intro h
    apply (Paper.Extension.Singleton.ofRegion_eq_iff N hs d.source_typed).1
    exact (q_cert_source (cycleCert l)).trans ((congrArg (QLit bitState_typed ≫ ·)
      ((Paper.Extension.Singleton.ofRegion_eq_iff N hE hE').2 h)).trans (q_poll_source d).symm)

/-- The cycle of three blocks has the source of the two-block table whose
blocks repeat themselves: every row returns on the left reply and
continues on the right. -/
theorem cyc3_self (l : Bool) : Eqv false [Bit] (cycleSource l) (selfTable l).source [Bit] :=
  (cyc3_poll_entered l (selfTable l)).2
    ((Router.labels_eqv_iff (fun _ => l) cycleAct (fun i => (selfTable l).label (pairBit i)) (selfTable l).act
      0 (pairIdx (selfTable l).start)).2
      ⟨fun _ _ => True, fun _ _ _ => rfl, fun _ _ _ tag _ => by
        cases tag
        · exact rfl
        · exact ⟨rfl, trivial⟩, trivial⟩)

/-- The cycle is not a table that never leaves. -/
theorem cyc3_never (l l' : Bool) : ¬ Eqv false [Bit] (cycleSource l) (neverTable l').source [Bit] :=
  fun e => by
    obtain ⟨R, -, ha, r⟩ := (Router.labels_eqv_iff (fun _ => l) cycleAct
      (fun i => (neverTable l').label (pairBit i)) (neverTable l').act 0 (pairIdx (neverTable l').start)).1
      ((cyc3_poll_entered l (neverTable l')).1 e)
    exact ha _ _ r false false

/-- Two cycles are equal exactly when their labels agree. -/
theorem cyc3_label (l l' : Bool) : Eqv false [Bit] (cycleSource l) (cycleSource l') [Bit] ↔ l = l' := by
  constructor
  · intro e
    rw [cycleSource_eq, cycleSource_eq] at e
    obtain ⟨R, hl, -, r⟩ := (Router.labels_eqv_iff (fun _ => l) cycleAct (fun _ => l') cycleAct 0 0).1
      ((cert_eqv_iff_entered (cycleCert l) (cycleCert l')).1 e)
    exact hl _ _ r
  · rintro rfl
    exact Paper.Extension.Eqv.refl (cycleSource_typed l).hasType

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables

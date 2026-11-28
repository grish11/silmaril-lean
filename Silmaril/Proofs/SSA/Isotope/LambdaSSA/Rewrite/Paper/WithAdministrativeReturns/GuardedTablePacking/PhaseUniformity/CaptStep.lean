module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.CapturedSource

/-! # The step equation for the loop that keeps the captured input -/

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

/-! ## A Bit is one of its two constructors -/

theorem inlU_typed : ValueBranches [U] (.br 0 (.inl (.var 0)) : Region signature.Instr) [Bit] :=
  .br rfl (.inl (.var rfl))

theorem inrU_typed : ValueBranches [U] (.br 0 (.inr (.var 0)) : Region signature.Instr) [Bit] :=
  .br rfl (.inr (.var rfl))

/-- A region on a Bit is the case of its two restrictions. Default Paper. -/
theorem bit_eta {D : Ty Empty} {k : Region signature.Instr} (h : ValueBranches [Bit] k [D]) :
    ofRegion h = ofRegion (caseValueBranches (seqValueBranches inlU_typed h) (seqValueBranches inrU_typed h)) := by
  have a : ofRegion inlU_typed = coprod.inl ≫ (sumIso (Φ := signature.Instr) U U).inv :=
    (br_inl (.var rfl)).trans ((congrArg (· ≫ _) (ofRegion_id U)).trans (Category.id_comp _))
  have b : ofRegion inrU_typed = coprod.inr ≫ (sumIso (Φ := signature.Instr) U U).inv :=
    (br_inr (.var rfl)).trans ((congrArg (· ≫ _) (ofRegion_id U)).trans (Category.id_comp _))
  have key : coprod.desc ((coprod.inl ≫ (sumIso (Φ := signature.Instr) U U).inv) ≫ ofRegion h)
      ((coprod.inr ≫ (sumIso (Φ := signature.Instr) U U).inv) ≫ ofRegion h) =
      (sumIso (Φ := signature.Instr) U U).inv ≫ ofRegion h := by
    apply coprod.hom_ext <;> simp
  rw [← coprod_desc_ofRegion (seqValueBranches inlU_typed h) (seqValueBranches inrU_typed h),
    ← ofRegion_comp inlU_typed h (seqValueBranches inlU_typed h),
    ← ofRegion_comp inrU_typed h (seqValueBranches inrU_typed h), a, b, key, ← Category.assoc,
    Iso.hom_inv_id, Category.id_comp]

/-! ## The step equation -/

/-- The body with the first Bit of its pair a constant. -/
theorem captBodyLit_typed (l c : Bool) :
    ValueBranches [Bit]
      (.case (.op (.ask l) (.var 0)) (.br 0 (.inl (litBit c))) (.br 0 (.inr (.pair (litBit c) (.var 0)))) :
        Region signature.Instr) [Silmaril.coprod Bit Pair] :=
  .case (A := Bit) (B := Bit) (.op (.var (i := 0) rfl)) (.br rfl (.inl (litBit_any c)))
    (.br rfl (.inr (.pair (litBit_any c) (.var rfl))))

/-- Product β on the body entered with a pair whose first Bit is a constant. -/
theorem capt_body_lit (l c : Bool) :
    ofRegion (seqValueBranches (pairLit_typed c) (captBody_typed l)) = ofRegion (captBodyLit_typed l c) := by
  have hbody : Region.HasType [Bit, Bit, Bit]
      (.case (.op (.ask l) (.var 0)) (.br 0 (.inl (.var 2))) (.br 0 (.inr (.pair (.var 2) (.var 0)))) :
        Region signature.Instr) [Silmaril.coprod Bit Pair] :=
    (ValueBranches.case (A := Bit) (B := Bit) (.op (.var (i := 0) rfl)) (.br rfl (.inl (.var (i := 2) rfl)))
      (.br rfl (.inr (.pair (.var (i := 2) rfl) (.var (i := 0) rfl))))).hasType
  have beta := Paper.Eqv.productBeta
    (ProductBeta.Step.let₂Beta (Γ := [Bit]) (a := litBit c) (b := (.var 0 : Tm signature.Instr))
      (litBit_typed c) (.var rfl) hbody)
  cases c <;> exact (Paper.TypeCategory.ofRegion_eq_iff _ _).mpr beta

theorem inrCap_typed (c : Bool) :
    ValueBranches [Bit] (.br 0 (.inr (.pair (litBit c) (.var 0))) : Region signature.Instr)
      [Silmaril.coprod Bit Pair] :=
  .br rfl (.inr (.pair (litBit_any c) (.var rfl)))

/-- The left reply: the conjugated body returns the constant, and so does
the router row. Unit η discards the reply. -/
theorem capt_step_left (c : Bool) :
    QLit (seqValueBranches (inlLit_typed c) (postRegion_typed (B := Bit) pairEnc_typed)) =
      QLit (seqValueBranches brInl_typed (routerRoute_typed 1 (captAct (pairIdx c)))) := by
  have l₁ : ofRegion (seqValueBranches (inlLit_typed c) (postRegion_typed (B := Bit) pairEnc_typed)) =
      ofRegion (retLit_typed c) :=
    (ofRegion_comp (inlLit_typed c) (postRegion_typed (B := Bit) pairEnc_typed) _).symm.trans
      (postR_inl pairEnc_typed (litBit_any c))
  have l₂ : QLit (retLit_typed c) =
      QLit (caseValueBranches (act_typed 1 (.ret c)) (act_typed 1 (.ret c))) :=
    (q_region_congr (by cases c <;> rfl) (retLit_typed c)
      (seqValueBranches bitDiscard (act_typed 1 (.ret c)))).trans (q_discard (act_typed 1 (.ret c)))
  have l₃ : ofRegion (seqValueBranches brInl_typed (routerRoute_typed 1 (captAct (pairIdx c)))) =
      ofRegion (caseValueBranches (act_typed 1 (.ret c)) (act_typed 1 (.ret c))) := by
    cases c <;>
      exact (case_inl_arrow (X := Bit) (B := State) (t := (.var 0 : Tm signature.Instr)) (.var (i := 0) rfl)
        (bitSplit_typed 1 _ _) (stateSplit_typed 1 _ _)).trans
        ((ofRegion_comp idBit (bitSplit_typed 1 _ _) (seqValueBranches idBit (bitSplit_typed 1 _ _))).symm.trans
          (by rw [ofRegion_id, Category.id_comp]))
  exact (congrArg (π).map l₁).trans (l₂.trans (congrArg (π).map l₃).symm)

/-- The right reply: the conjugated body encodes the pair of the constant
and the reply, which is the row of the constant carrying the reply; the
router row stays in its row with the reply. Default Paper: the encoding
at a constant first Bit, and the case of a Bit on its constructors. -/
theorem capt_step_right (c : Bool) :
    ofRegion (seqValueBranches (inrCap_typed c) (postRegion_typed (B := Bit) pairEnc_typed)) =
      ofRegion (seqValueBranches brInrInl_typed (routerRoute_typed 1 (captAct (pairIdx c)))) := by
  have inr_arrow : ofRegion inrSt_typed = coprod.inr ≫ (sumIso (Φ := signature.Instr) Bit (States 1)).inv :=
    (br_inr (.var rfl)).trans ((congrArg (· ≫ _) (ofRegion_id (States 1))).trans (Category.id_comp _))
  have r₁ : ofRegion (seqValueBranches (inrCap_typed c) (postRegion_typed (B := Bit) pairEnc_typed)) =
      ofRegion (seqValueBranches (injBit_typed c) inrSt_typed) := by
    refine (ofRegion_comp (inrCap_typed c) (postRegion_typed (B := Bit) pairEnc_typed) _).symm.trans ?_
    refine (postR_inr pairEnc_typed (.pair (litBit_any c) (.var (i := 0) rfl))).trans ?_
    rw [← inr_arrow, ofRegion_comp (pairLit_typed c) pairEnc_typed (seqValueBranches (pairLit_typed c) pairEnc_typed),
      enc_lit]
    exact ofRegion_comp (injBit_typed c) inrSt_typed _
  have r₂ : ofRegion (seqValueBranches (injBit_typed c) inrSt_typed) =
      ofRegion (caseValueBranches (act_typed 1 (.go (pairIdx c) false)) (act_typed 1 (.go (pairIdx c) true))) := by
    refine (bit_eta (seqValueBranches (injBit_typed c) inrSt_typed)).trans ?_
    cases c <;> rfl
  have r₃ : ofRegion (seqValueBranches brInrInl_typed (routerRoute_typed 1 (captAct (pairIdx c)))) =
      ofRegion (caseValueBranches (act_typed 1 (.go (pairIdx c) false)) (act_typed 1 (.go (pairIdx c) true))) := by
    cases c <;>
      exact (case_inr_arrow (X := Bit) (A := Bit) (t := (.inl (.var 0) : Tm signature.Instr))
        (.inl (.var (i := 0) rfl)) (bitSplit_typed 1 _ _) (stateSplit_typed 1 _ _)).trans
        ((case_inl_arrow (X := Bit) (B := Silmaril.empty) (t := (.var 0 : Tm signature.Instr)) (.var (i := 0) rfl)
          (bitSplit_typed 1 _ _) (dead_typed 1)).trans
          ((ofRegion_comp idBit (bitSplit_typed 1 _ _) (seqValueBranches idBit (bitSplit_typed 1 _ _))).symm.trans
            (by rw [ofRegion_id, Category.id_comp])))
  exact r₁.trans (r₂.trans r₃.symm)

/-- One row on a Bit: congruence under the request. -/
theorem capt_step_bit (l c : Bool) :
    QLit (seqValueBranches (captBodyLit_typed l c) (postRegion_typed (B := Bit) pairEnc_typed)) =
      QLit (seqValueBranches (labelPoll l).program.typed.packExits (routerRoute_typed 1 (captAct (pairIdx c)))) := by
  have left := Paper.Extension.Eqv.substVars (Δ := [Bit, Bit]) (θ := fun i => (.var i : Tm signature.Instr))
    ((Paper.Extension.Singleton.ofRegion_eq_iff N _ _).1 (capt_step_left c)) (fun _ _ h => weaken h)
  have right := Paper.Extension.Eqv.substVars (Δ := [Bit, Bit]) (θ := fun i => (.var i : Tm signature.Instr))
    ((Paper.Extension.Singleton.ofRegion_eq_iff N _ _).1 (congrArg (π).map (capt_step_right c)))
    (fun _ _ h => weaken h)
  have hop : Tm.HasType [Bit] (.op (.ask l) (.var 0) : Tm signature.Instr) (Silmaril.coprod Bit Bit) :=
    .op (.var (i := 0) rfl)
  cases c <;>
    exact (Paper.Extension.Singleton.ofRegion_eq_iff N _ _).2 (Paper.Extension.Eqv.case hop left right)

/-- One row: the conjugated body at the row of the constant `c` is the
router row. -/
theorem capt_step_row (l c : Bool) :
    QLit (seqValueBranches (pairDecRow_typed c)
        (seqRegion_typed (captBody_typed l) (postRegion_typed (B := Bit) pairEnc_typed))) =
      QLit (routerRow_typed 1 (labelPoll l).program (captAct (pairIdx c))) := by
  apply q_state_ext
  have dL : ofRegion (seqValueBranches bitState_typed (seqValueBranches (pairDecRow_typed c)
        (seqRegion_typed (captBody_typed l) (postRegion_typed (B := Bit) pairEnc_typed)))) =
      ofRegion (seqValueBranches (captBodyLit_typed l c) (postRegion_typed (B := Bit) pairEnc_typed)) := by
    have hX := seqRegion_typed (captBody_typed l) (postRegion_typed (B := Bit) pairEnc_typed)
    have e₁ := (ofRegion_comp bitState_typed (seqValueBranches (pairDecRow_typed c) hX)
      (seqValueBranches bitState_typed (seqValueBranches (pairDecRow_typed c) hX))).symm
    have e₂ := (ofRegion_comp (pairDecRow_typed c) hX (seqValueBranches (pairDecRow_typed c) hX)).symm
    have e₃ := (ofRegion_comp (captBody_typed l) (postRegion_typed (B := Bit) pairEnc_typed) hX).symm
    have e₄ := ofRegion_comp (pairLit_typed c) (captBody_typed l)
      (seqValueBranches (pairLit_typed c) (captBody_typed l))
    rw [e₁, e₂, e₃, ← Category.assoc, bit_decRow, ← Category.assoc, e₄, capt_body_lit]
    exact ofRegion_comp (captBodyLit_typed l c) (postRegion_typed (B := Bit) pairEnc_typed) _
  have dR : ofRegion (seqValueBranches bitState_typed
        (routerRow_typed 1 (labelPoll l).program (captAct (pairIdx c)))) =
      ofRegion (seqValueBranches (labelPoll l).program.typed.packExits
        (routerRoute_typed 1 (captAct (pairIdx c)))) := by
    rw [← ofRegion_comp bitState_typed (routerRow_typed 1 (labelPoll l).program (captAct (pairIdx c)))
        (seqValueBranches bitState_typed (routerRow_typed 1 (labelPoll l).program (captAct (pairIdx c)))),
      ← ofRegion_comp (step_typed (labelPoll l).program) (routerRoute_typed 1 (captAct (pairIdx c)))
        (routerRow_typed 1 (labelPoll l).program (captAct (pairIdx c))),
      ← ofRegion_comp unpack_typed (labelPoll l).program.typed.packExits (step_typed (labelPoll l).program),
      ← Category.assoc, ← Category.assoc, pack_unpack, Category.id_comp]
    exact ofRegion_comp (labelPoll l).program.typed.packExits (routerRoute_typed 1 (captAct (pairIdx c))) _
  exact (congrArg (π).map dL).trans ((capt_step_bit l c).trans (congrArg (π).map dR).symm)

/-- The step that keeps the captured input, conjugated by the encoding of
pairs, is the dispatcher step of its router table. -/
theorem capt_step (l : Bool) : Task.captStep l := by
  apply (Paper.Extension.Singleton.ofRegion_eq_iff N
    (seqRegion_typed pairDec_typed
      (seqRegion_typed (captBody_typed l) (postRegion_typed (B := Bit) pairEnc_typed)))
    (dispatch_typed 1 (captRouter l).rows_typed)).1
  refine (congrArg (π).map (seq_dispatch (fun i => pairDecRow_typed (pairBit i))
    (seqRegion_typed (captBody_typed l) (postRegion_typed (B := Bit) pairEnc_typed)))).trans ?_
  exact q_dispatch_congr 1
    (fun i => seqValueBranches (pairDecRow_typed (pairBit i))
      (seqRegion_typed (captBody_typed l) (postRegion_typed (B := Bit) pairEnc_typed)))
    (captRouter l).rows_typed (fun i => by
      match i with
      | 0 => exact capt_step_row l false
      | 1 => exact capt_step_row l true)

/-! ## The loop on the pair: factoring and completeness -/

theorem capt_factors (l : Bool) : Factors pairDec (loopRegion Pair (captBody l)) (captRouter l) :=
  capt_factors_of l (capt_step l)

open Paper.WithAdministrativeReturns.WithGuardedTablePacking (Valid) in
theorem capt_complete (l l' : Bool) :
    Eqv false [Pair] (loopRegion Pair (captBody l)) (loopRegion Pair (captBody l')) [Bit] ↔
      Valid (loopRegion_typed (captBody_typed l)).hasType (loopRegion_typed (captBody_typed l')).hasType :=
  capt_complete_of l l' (capt_step l) (capt_step l')

/-! ## The source entry: a constant input reaches the router at its diagonal state -/

/-- The source run on the Bit of a state. -/
theorem stateSource_typed (l : Bool) :
    ValueBranches [State] (seqRegion (unpackExits [Bit]) (captSource l)) [Bit] :=
  seqRegion_typed unpack_typed (captSource_typed l)

theorem pairVar2_typed (q : Bool) :
    ValueBranches [U] (.br 0 (.pair (bitTm q) (bitTm q)) : Region signature.Instr) [Pair] :=
  .br rfl (.pair (bitTm_typed q) (bitTm_typed q))

theorem pairLitVar_typed (q : Bool) :
    ValueBranches [U] (.br 0 (.pair (litBit q) (bitTm q)) : Region signature.Instr) [Pair] :=
  .br rfl (.pair (litBit_any q) (bitTm_typed q))

/-- A constant state, its Bit, duplicated: the pair of the constant with
itself, built on the unit input. Default Paper. -/
theorem const_dup (q : Bool) :
    ofRegion (const_typed q) ≫ ofRegion unpack_typed ≫ ofRegion dupEntry_typed = ofRegion (pairVar2_typed q) := by
  rw [const_arrow, Category.assoc, ← Category.assoc (ofRegion bitState_typed), pack_unpack, Category.id_comp]
  cases q
  · exact ofRegion_comp (ValueBranches.br (ℓ := 0) (L := [Bit]) rfl (bitTm_typed false)) dupEntry_typed
      (pairVar2_typed false)
  · exact ofRegion_comp (ValueBranches.br (ℓ := 0) (L := [Bit]) rfl (bitTm_typed true)) dupEntry_typed
      (pairVar2_typed true)

/-- A constant state, sent to the row of its Bit and decoded: the pair of
the literal constant and the constant. Default Paper. -/
theorem const_row_dec (q : Bool) :
    ofRegion (const_typed q) ≫ injArr 1 (pairIdx q) ≫ ofRegion pairDec_typed = ofRegion (pairLitVar_typed q) := by
  rw [const_arrow, Category.assoc, ← Category.assoc (ofRegion bitState_typed), ← injBit_arrow,
    ofRegion_comp (injBit_typed q) pairDec_typed (seqValueBranches (injBit_typed q) pairDec_typed), inj_dec]
  cases q
  · exact ofRegion_comp (ValueBranches.br (ℓ := 0) (L := [Bit]) rfl (bitTm_typed false)) (pairLit_typed false)
      (pairLitVar_typed false)
  · exact ofRegion_comp (ValueBranches.br (ℓ := 0) (L := [Bit]) rfl (bitTm_typed true)) (pairLit_typed true)
      (pairLitVar_typed true)

/-- The two pairs agree in the quotient: unit η. -/
theorem pair_lit_var (q : Bool) : QLit (pairLitVar_typed q) = QLit (pairVar2_typed q) := by
  apply (Paper.Extension.Singleton.ofRegion_eq_iff N (pairLitVar_typed q) (pairVar2_typed q)).2
  cases q
  · exact unit_fill (Γ := [U]) (i := 0) rfl (.pair (.inl (.var 0)) (.inl (.var 1)))
      (.pair (.inl (.var rfl)) (.inl (.var rfl)))
  · exact unit_fill (Γ := [U]) (i := 0) rfl (.pair (.inr (.var 0)) (.inr (.var 1)))
      (.pair (.inr (.var rfl)) (.inr (.var rfl)))

theorem capt_spin (l : Bool) : Router.ofSpin (fun _ => some l) captAct = captRouter l := rfl

/-- At each constant input the source is the router table entered at the
row of that constant, carrying that constant. -/
theorem capt_pointed (l : Bool) :
    SpinPointed (seqRegion (unpackExits [Bit]) (captSource l)) (fun _ => some l) captAct pairIdx := by
  intro q
  rw [capt_spin]
  have hloop := loopRegion_typed (captBody_typed l)
  have src : QLit (captSource_typed l) = QLit dupEntry_typed ≫ QLit hloop :=
    ((Paper.Extension.Singleton.ofRegion_eq_iff N (captSource_typed l) (captLoop_typed l)).2
      (Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.ofTablePacking false
        (capt_source_loop l))).trans (q_comp dupEntry_typed hloop)
  have dupq : QLit (pairVar2_typed q) =
      QLit (const_typed q) ≫ QLit unpack_typed ≫ QLit dupEntry_typed :=
    (congrArg (π).map (const_dup q).symm).trans
      (((π).map_comp _ _).trans (congrArg (QLit (const_typed q) ≫ ·) ((π).map_comp _ _)))
  have left : QLit (constEntry_typed q (stateSource_typed l)) = QLit (pairVar2_typed q) ≫ QLit hloop := by
    rw [dupq]
    refine (q_comp (const_typed q) (stateSource_typed l)).trans ?_
    refine (congrArg (QLit (const_typed q) ≫ ·)
      ((q_comp unpack_typed (captSource_typed l)).trans (congrArg (QLit unpack_typed ≫ ·) src))).trans ?_
    simp only [Category.assoc]
  have fac : QLit (captRouter l).loop_typed = QLit pairDec_typed ≫ QLit hloop :=
    ((Paper.Extension.Singleton.ofRegion_eq_iff N (seqRegion_typed pairDec_typed hloop)
      (captRouter l).loop_typed).2 (capt_factors l)).symm.trans (q_comp pairDec_typed hloop)
  have rowq : QLit (pairLitVar_typed q) =
      QLit (const_typed q) ≫ (π).map (injArr 1 (pairIdx q)) ≫ QLit pairDec_typed :=
    (congrArg (π).map (const_row_dec q).symm).trans
      (((π).map_comp _ _).trans (congrArg (QLit (const_typed q) ≫ ·) ((π).map_comp _ _)))
  have ent : QLit ((captRouter l).entered_typed (pairIdx q)) =
      (π).map (injArr 1 (pairIdx q)) ≫ QLit (captRouter l).loop_typed :=
    (congrArg (π).map (dispatchEntered_arrow (captRouter l).rows_typed (pairIdx q))).trans ((π).map_comp _ _)
  have right : QLit (constEntry_typed q ((captRouter l).entered_typed (pairIdx q))) =
      QLit (pairLitVar_typed q) ≫ QLit hloop := by
    rw [rowq]
    refine (q_comp (const_typed q) ((captRouter l).entered_typed (pairIdx q))).trans ?_
    refine (congrArg (QLit (const_typed q) ≫ ·)
      (ent.trans (congrArg ((π).map (injArr 1 (pairIdx q)) ≫ ·) fac))).trans ?_
    simp only [Category.assoc]
  exact (Paper.Extension.Singleton.ofRegion_eq_iff N (constEntry_typed q (stateSource_typed l))
    (constEntry_typed q ((captRouter l).entered_typed (pairIdx q)))).1
    (left.trans ((congrArg (· ≫ QLit hloop) (pair_lit_var q).symm).trans right.symm))

open Paper.WithAdministrativeReturns.WithGuardedTablePacking (Valid) in
/-- Validity at the source entry determines the request label: the
query-aware model shows the first request of the router table at the
diagonal state of a constant input. -/
theorem capt_label_of_valid (l l' : Bool)
    (v : Valid (captSource_typed l).hasType (captSource_typed l').hasType) : l = l' := by
  have vS : Valid (stateSource_typed l).hasType (stateSource_typed l').hasType :=
    Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.Valid.seq
      unpack_typed (captSource_typed l) (captSource_typed l') v
  have obs := TableModel.query_pointed_obs (stateSource_typed l) (stateSource_typed l') (capt_pointed l)
    (capt_pointed l') vS false
  exact (TableModel.query_label_query (fun _ => some l) captAct (fun _ => some l') captAct
    (pairIdx false) (pairIdx false) rfl rfl false false obs).1

open Paper.WithAdministrativeReturns.WithGuardedTablePacking (Valid) in
/-- Two sources are equal at the source entry exactly when they are
valid in every supported model. -/
theorem capt_source_complete (l l' : Bool) :
    Eqv false [Bit] (captSource l) (captSource l') [Bit] ↔
      Valid (captSource_typed l).hasType (captSource_typed l').hasType :=
  ⟨fun e => Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.valid_of_eqv false e _ _,
    fun v => capt_label_of_valid l l' v ▸ Paper.Extension.Eqv.refl (captSource_typed l).hasType⟩

/-- Two sources are equal exactly when their requests have the same label. -/
theorem capt_source_eqv_iff (l l' : Bool) :
    Eqv false [Bit] (captSource l) (captSource l') [Bit] ↔ l = l' :=
  ⟨fun e => capt_label_of_valid l l' ((capt_source_complete l l').1 e),
    fun h => h ▸ Paper.Extension.Eqv.refl (captSource_typed l).hasType⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables

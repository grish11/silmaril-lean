module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Packed.Product.Flat.Latch.Captured.Controlled.Defs
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.CaptStep

/-! # A two-block source whose captured input chooses the request -/

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

/-! ## A case on a constructor, with its payload substituted -/

section CaseLit

variable {Γ : VCtx (Ty Empty)} {A B : Ty Empty} {K : LCtx (Ty Empty)} {a : Tm signature.Instr}
  {L R : Region signature.Instr}

theorem case_lit_inl (ha : Tm.BranchValue Γ a A) (hl : Region.HasType (A :: Γ) L K)
    (hr : Region.HasType (B :: Γ) R K) :
    Paper.Eqv Γ (.case (.inl a) L R) (L.substVars (Tm.singleSubst a)) K :=
  (Paper.Eqv.cfgEta (.native (.base (.caseInl ha.hasType hl hr)))).trans (.cfgEta (.native (.letValue ha hl)))

theorem case_lit_inr (ha : Tm.BranchValue Γ a B) (hl : Region.HasType (A :: Γ) L K)
    (hr : Region.HasType (B :: Γ) R K) :
    Paper.Eqv Γ (.case (.inr a) L R) (R.substVars (Tm.singleSubst a)) K :=
  (Paper.Eqv.cfgEta (.native (.base (.caseInr ha.hasType hl hr)))).trans (.cfgEta (.native (.letValue ha hr)))

end CaseLit

/-! ## The flat graph -/

theorem ctrl_flat_typed (l₀ l₁ : Bool) :
    LambdaSSA.FiniteCFG.HasType (.snoc .nil Bit) (fun _ : Fin 2 => Bit) (fun _ : Fin 1 => Bit)
      (ctrlFlat l₀ l₁) where
  entry := .br (i := 0) .bv
  block := fun i => match i with
    | 0 => .case (A := U) (B := U) .bv
        (.case (A := Bit) (B := Bit) (.op .bv) (.br (i := 2) .bv) (.br (i := 1) .bv))
        (.case (A := Bit) (B := Bit) (.op .bv) (.br (i := 2) .bv) (.br (i := 1) .bv))
    | 1 => .br (i := 0) .bv

/-! ## At a constant input the captured input chooses one request, in default Paper -/

theorem bitU_typed (q : Bool) : ValueBranches [U] (.br 0 (bitTm q) : Region signature.Instr) [Bit] :=
  .br rfl (bitTm_typed q)

/-- At a constant input the source is the source of #5323 with the label
chosen by that input: inside the table, the case of the header on the
captured input is a case on a constructor. Default Paper. -/
theorem ctrl_const (l₀ l₁ q : Bool) :
    Paper.Eqv [U] (seqRegion (.br 0 (bitTm q)) (ctrlSource l₀ l₁))
      (seqRegion (.br 0 (bitTm q)) (captSource (pickLabel l₀ l₁ q))) [Bit] := by
  have latch : Region.HasType [Bit, U] (.br 0 (.var 0) : Region signature.Instr)
      (List.ofFn (fun _ : Fin 2 => Bit) ++ [Bit]) :=
    (ValueBranches.br (ℓ := 0) (A := Bit) rfl (.var (i := 0) rfl)).hasType
  cases q
  · refine Paper.Eqv.cfg (fun _ : Fin 2 => Bit)
      (Paper.Eqv.refl (ValueBranches.br (ℓ := 0) (A := Bit) (L := [Bit, Bit, Bit]) rfl
        (.inl (.var (i := 0) rfl))).hasType) (fun i => ?_)
    match i with
    | 0 =>
      exact case_lit_inl (A := U) (B := U) (.var (i := 1) rfl)
        (ValueBranches.case (A := Bit) (B := Bit) (.op (.var (i := 1) rfl))
          (.br (ℓ := 2) (A := Bit) rfl (.inl (.var (i := 3) rfl)))
          (.br (ℓ := 1) (A := Bit) rfl (.var (i := 0) rfl))).hasType
        (ValueBranches.case (A := Bit) (B := Bit) (.op (.var (i := 1) rfl))
          (.br (ℓ := 2) (A := Bit) rfl (.inl (.var (i := 3) rfl)))
          (.br (ℓ := 1) (A := Bit) rfl (.var (i := 0) rfl))).hasType
    | 1 => exact Paper.Eqv.refl latch
  · refine Paper.Eqv.cfg (fun _ : Fin 2 => Bit)
      (Paper.Eqv.refl (ValueBranches.br (ℓ := 0) (A := Bit) (L := [Bit, Bit, Bit]) rfl
        (.inr (.var (i := 0) rfl))).hasType) (fun i => ?_)
    match i with
    | 0 =>
      exact case_lit_inr (A := U) (B := U) (.var (i := 1) rfl)
        (ValueBranches.case (A := Bit) (B := Bit) (.op (.var (i := 1) rfl))
          (.br (ℓ := 2) (A := Bit) rfl (.inr (.var (i := 3) rfl)))
          (.br (ℓ := 1) (A := Bit) rfl (.var (i := 0) rfl))).hasType
        (ValueBranches.case (A := Bit) (B := Bit) (.op (.var (i := 1) rfl))
          (.br (ℓ := 2) (A := Bit) rfl (.inr (.var (i := 3) rfl)))
          (.br (ℓ := 1) (A := Bit) rfl (.var (i := 0) rfl))).hasType
    | 1 => exact Paper.Eqv.refl latch

/-! ## The router table at each constant input -/

theorem const_unpack (q : Bool) :
    ofRegion (const_typed q) ≫ ofRegion unpack_typed = ofRegion (bitU_typed q) := by
  rw [const_arrow, Category.assoc, pack_unpack, Category.comp_id]

/-- A source run on the Bit of a constant state is the source run on the
constant. -/
theorem const_state {s : Region signature.Instr} (hs : ValueBranches [Bit] s [Bit]) (q : Bool) :
    QLit (constEntry_typed q (seqRegion_typed unpack_typed hs)) = QLit (seqValueBranches (bitU_typed q) hs) :=
  (q_comp (const_typed q) (seqRegion_typed unpack_typed hs)).trans
    ((congrArg (QLit (const_typed q) ≫ ·) (q_comp unpack_typed hs)).trans
      (((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ QLit hs) (((π).map_comp _ _).symm.trans (congrArg (π).map (const_unpack q))))).trans
        (q_comp (bitU_typed q) hs).symm))

theorem ctrl_spin (l₀ l₁ : Bool) :
    Router.ofSpin (fun i => some (pickLabel l₀ l₁ (pairBit i))) captAct = ctrlRouter l₀ l₁ := rfl

/-- Entered at the row of `q`, the two-label table is the one-label table
of the chosen label: the table never leaves its row. -/
theorem ctrl_row_eqv (l₀ l₁ q : Bool) :
    Eqv false [State] ((captRouter (pickLabel l₀ l₁ q)).entered (pairIdx q))
      ((ctrlRouter l₀ l₁).entered (pairIdx q)) [Bit] :=
  (Router.labels_eqv_iff (fun _ => pickLabel l₀ l₁ q) captAct (fun i => pickLabel l₀ l₁ (pairBit i)) captAct
    (pairIdx q) (pairIdx q)).2
    ⟨fun x y => x = pairIdx q ∧ y = pairIdx q,
      by
        rintro x y ⟨rfl, rfl⟩
        cases q <;> rfl,
      by
        rintro x y ⟨rfl, rfl⟩ tag pl
        cases tag
        · exact rfl
        · exact ⟨rfl, rfl, rfl⟩,
      ⟨rfl, rfl⟩⟩

theorem stateCtrl_typed (l₀ l₁ : Bool) :
    ValueBranches [State] (seqRegion (unpackExits [Bit]) (ctrlSource l₀ l₁)) [Bit] :=
  seqRegion_typed unpack_typed (ctrlSource_typed l₀ l₁)

/-- At each constant input the source is the two-label router table
entered at the row of that constant, carrying that constant. -/
theorem ctrl_pointed (l₀ l₁ : Bool) :
    SpinPointed (seqRegion (unpackExits [Bit]) (ctrlSource l₀ l₁))
      (fun i => some (pickLabel l₀ l₁ (pairBit i))) captAct pairIdx := by
  intro q
  rw [ctrl_spin]
  have native : QLit (seqValueBranches (bitU_typed q) (ctrlSource_typed l₀ l₁)) =
      QLit (seqValueBranches (bitU_typed q) (captSource_typed (pickLabel l₀ l₁ q))) :=
    congrArg (π).map ((Paper.TypeCategory.ofRegion_eq_iff _ _).mpr (ctrl_const l₀ l₁ q))
  have one : QLit (constEntry_typed q (stateSource_typed (pickLabel l₀ l₁ q))) =
      QLit (constEntry_typed q ((captRouter (pickLabel l₀ l₁ q)).entered_typed (pairIdx q))) :=
    (Paper.Extension.Singleton.ofRegion_eq_iff N _ _).2 (capt_pointed (pickLabel l₀ l₁ q) q)
  have row : QLit ((captRouter (pickLabel l₀ l₁ q)).entered_typed (pairIdx q)) =
      QLit ((ctrlRouter l₀ l₁).entered_typed (pairIdx q)) :=
    (Paper.Extension.Singleton.ofRegion_eq_iff N _ _).2 (ctrl_row_eqv l₀ l₁ q)
  exact (Paper.Extension.Singleton.ofRegion_eq_iff N (constEntry_typed q (stateCtrl_typed l₀ l₁))
    (constEntry_typed q ((ctrlRouter l₀ l₁).entered_typed (pairIdx q)))).1
    ((const_state (ctrlSource_typed l₀ l₁) q).trans (native.trans
      ((const_state (captSource_typed (pickLabel l₀ l₁ q)) q).symm.trans (one.trans
        ((q_comp (const_typed q) ((captRouter (pickLabel l₀ l₁ q)).entered_typed (pairIdx q))).trans
          ((congrArg (QLit (const_typed q) ≫ ·) row).trans
            (q_comp (const_typed q) ((ctrlRouter l₀ l₁).entered_typed (pairIdx q))).symm))))))

/-! ## Completeness at the source entry -/

open Paper.WithAdministrativeReturns.WithGuardedTablePacking (Valid) in
/-- Validity at the source entry determines both request labels: the
query-aware model shows the first request at each of the two constant
inputs. -/
theorem ctrl_labels_of_valid (l₀ l₁ l₀' l₁' : Bool)
    (v : Valid (ctrlSource_typed l₀ l₁).hasType (ctrlSource_typed l₀' l₁').hasType) :
    l₀ = l₀' ∧ l₁ = l₁' := by
  have vS : Valid (stateCtrl_typed l₀ l₁).hasType (stateCtrl_typed l₀' l₁').hasType :=
    Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.Valid.seq
      unpack_typed (ctrlSource_typed l₀ l₁) (ctrlSource_typed l₀' l₁') v
  have obs := fun q => TableModel.query_pointed_obs (stateCtrl_typed l₀ l₁) (stateCtrl_typed l₀' l₁')
    (ctrl_pointed l₀ l₁) (ctrl_pointed l₀' l₁') vS q
  exact ⟨(TableModel.query_label_query (fun i => some (pickLabel l₀ l₁ (pairBit i))) captAct
      (fun i => some (pickLabel l₀' l₁' (pairBit i))) captAct (pairIdx false) (pairIdx false) rfl rfl
      false false (obs false)).1,
    (TableModel.query_label_query (fun i => some (pickLabel l₀ l₁ (pairBit i))) captAct
      (fun i => some (pickLabel l₀' l₁' (pairBit i))) captAct (pairIdx true) (pairIdx true) rfl rfl
      true true (obs true)).1⟩

open Paper.WithAdministrativeReturns.WithGuardedTablePacking (Valid) in
/-- Two sources are equal at the source entry exactly when they are
valid in every supported model. -/
theorem ctrl_source_complete (l₀ l₁ l₀' l₁' : Bool) :
    Eqv false [Bit] (ctrlSource l₀ l₁) (ctrlSource l₀' l₁') [Bit] ↔
      Valid (ctrlSource_typed l₀ l₁).hasType (ctrlSource_typed l₀' l₁').hasType :=
  ⟨fun e => Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.valid_of_eqv false e _ _,
    fun v => by
      obtain ⟨rfl, rfl⟩ := ctrl_labels_of_valid l₀ l₁ l₀' l₁' v
      exact Paper.Extension.Eqv.refl (ctrlSource_typed l₀ l₁).hasType⟩

/-- Two sources are equal exactly when both request labels agree. -/
theorem ctrl_source_eqv_iff (l₀ l₁ l₀' l₁' : Bool) :
    Eqv false [Bit] (ctrlSource l₀ l₁) (ctrlSource l₀' l₁') [Bit] ↔ l₀ = l₀' ∧ l₁ = l₁' :=
  ⟨fun e => ctrl_labels_of_valid l₀ l₁ l₀' l₁' ((ctrl_source_complete l₀ l₁ l₀' l₁').1 e),
    fun ⟨h₀, h₁⟩ => h₀ ▸ h₁ ▸ Paper.Extension.Eqv.refl (ctrlSource_typed l₀ l₁).hasType⟩

/-! ## The step on the pair: the captured input chooses the row's label -/

/-- Product β and the case on a constant: entered with a pair whose first
Bit is a constant, the step is the step of #5323 with the chosen label. -/
theorem ctrl_body_lit (l₀ l₁ c : Bool) :
    ofRegion (seqValueBranches (pairLit_typed c) (ctrlBody_typed l₀ l₁)) =
      ofRegion (captBodyLit_typed (pickLabel l₀ l₁ c) c) := by
  have harm : ∀ l, Region.HasType [U, Bit, Bit, Bit] (ctrlBodyArm l) [Silmaril.coprod Bit Pair] := fun l =>
    (ValueBranches.case (A := Bit) (B := Bit) (.op (.var (i := 1) rfl)) (.br rfl (.inl (.var (i := 3) rfl)))
      (.br rfl (.inr (.pair (.var (i := 3) rfl) (.var (i := 0) rfl))))).hasType
  have hbody : Region.HasType [Bit, Bit, Bit]
      (.case (.var 1) (ctrlBodyArm l₀) (ctrlBodyArm l₁) : Region signature.Instr) [Silmaril.coprod Bit Pair] :=
    .case (A := U) (B := U) (.var (i := 1) rfl) (harm l₀) (harm l₁)
  have beta := Paper.Eqv.productBeta
    (ProductBeta.Step.let₂Beta (Γ := [Bit]) (a := litBit c) (b := (.var 0 : Tm signature.Instr))
      (litBit_typed c) (.var rfl) hbody)
  have hlit : ∀ l, Region.HasType [U, Bit]
      (.case (.op (.ask l) (.var 1)) (.br 0 (.inl (litBit c))) (.br 0 (.inr (.pair (litBit c) (.var 0)))) :
        Region signature.Instr) [Silmaril.coprod Bit Pair] := fun l =>
    (ValueBranches.case (A := Bit) (B := Bit) (.op (.var (i := 1) rfl)) (.br rfl (.inl (litBit_any c)))
      (.br rfl (.inr (.pair (litBit_any c) (.var (i := 0) rfl))))).hasType
  cases c
  · exact (Paper.TypeCategory.ofRegion_eq_iff _ _).mpr
      (beta.trans (case_lit_inl (A := U) (B := U) .unit (hlit l₀) (hlit l₁)))
  · exact (Paper.TypeCategory.ofRegion_eq_iff _ _).mpr
      (beta.trans (case_lit_inr (A := U) (B := U) .unit (hlit l₀) (hlit l₁)))

/-- One row, for any step that at a constant first Bit is the request of
a label with the keeping continuations. -/
theorem row_of_lit {body : Region signature.Instr} (hb : ValueBranches [Pair] body [Silmaril.coprod Bit Pair])
    (l c : Bool) (e : ofRegion (seqValueBranches (pairLit_typed c) hb) = ofRegion (captBodyLit_typed l c)) :
    QLit (seqValueBranches (pairDecRow_typed c)
        (seqRegion_typed hb (postRegion_typed (B := Bit) pairEnc_typed))) =
      QLit (routerRow_typed 1 (labelPoll l).program (captAct (pairIdx c))) := by
  apply q_state_ext
  have dL : ofRegion (seqValueBranches bitState_typed (seqValueBranches (pairDecRow_typed c)
        (seqRegion_typed hb (postRegion_typed (B := Bit) pairEnc_typed)))) =
      ofRegion (seqValueBranches (captBodyLit_typed l c) (postRegion_typed (B := Bit) pairEnc_typed)) := by
    have hX := seqRegion_typed hb (postRegion_typed (B := Bit) pairEnc_typed)
    have e₁ := (ofRegion_comp bitState_typed (seqValueBranches (pairDecRow_typed c) hX)
      (seqValueBranches bitState_typed (seqValueBranches (pairDecRow_typed c) hX))).symm
    have e₂ := (ofRegion_comp (pairDecRow_typed c) hX (seqValueBranches (pairDecRow_typed c) hX)).symm
    have e₃ := (ofRegion_comp hb (postRegion_typed (B := Bit) pairEnc_typed) hX).symm
    have e₄ := ofRegion_comp (pairLit_typed c) hb
      (seqValueBranches (pairLit_typed c) hb)
    rw [e₁, e₂, e₃, ← Category.assoc, bit_decRow, ← Category.assoc, e₄, e]
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


/-- The step on the pair, conjugated by the encoding of pairs, is the
dispatcher step of the two-label router table. -/
theorem ctrl_step (l₀ l₁ : Bool) :
    Eqv false [States 1] (seqRegion pairDec (seqRegion (ctrlBody l₀ l₁) (postRegion pairEnc)))
      (dispatch 1 (ctrlRouter l₀ l₁).rows) [Silmaril.coprod Bit (States 1)] := by
  apply (Paper.Extension.Singleton.ofRegion_eq_iff N
    (seqRegion_typed pairDec_typed
      (seqRegion_typed (ctrlBody_typed l₀ l₁) (postRegion_typed (B := Bit) pairEnc_typed)))
    (dispatch_typed 1 (ctrlRouter l₀ l₁).rows_typed)).1
  refine (congrArg (π).map (seq_dispatch (fun i => pairDecRow_typed (pairBit i))
    (seqRegion_typed (ctrlBody_typed l₀ l₁) (postRegion_typed (B := Bit) pairEnc_typed)))).trans ?_
  exact q_dispatch_congr 1
    (fun i => seqValueBranches (pairDecRow_typed (pairBit i))
      (seqRegion_typed (ctrlBody_typed l₀ l₁) (postRegion_typed (B := Bit) pairEnc_typed)))
    (ctrlRouter l₀ l₁).rows_typed (fun i => by
      match i with
      | 0 => exact row_of_lit (ctrlBody_typed l₀ l₁) l₀ false (ctrl_body_lit l₀ l₁ false)
      | 1 => exact row_of_lit (ctrlBody_typed l₀ l₁) l₁ true (ctrl_body_lit l₀ l₁ true))

theorem ctrl_factors (l₀ l₁ : Bool) :
    Factors pairDec (loopRegion Pair (ctrlBody l₀ l₁)) (ctrlRouter l₀ l₁) :=
  conjugate_factors pairEnc_typed pairDec_typed (ctrlBody_typed l₀ l₁) enc_dec (ctrlRouter l₀ l₁)
    (ctrl_step l₀ l₁)

open Paper.WithAdministrativeReturns.WithGuardedTablePacking (Valid) in
theorem ctrl_complete (l₀ l₁ l₀' l₁' : Bool) :
    Eqv false [Pair] (loopRegion Pair (ctrlBody l₀ l₁)) (loopRegion Pair (ctrlBody l₀' l₁')) [Bit] ↔
      Valid (loopRegion_typed (ctrlBody_typed l₀ l₁)).hasType
        (loopRegion_typed (ctrlBody_typed l₀' l₁')).hasType :=
  factored_complete pairEnc_typed pairDec_typed (loopRegion_typed (ctrlBody_typed l₀ l₁))
    (loopRegion_typed (ctrlBody_typed l₀' l₁')) enc_dec (ctrlRouter l₀ l₁) (ctrlRouter l₀' l₁')
    (ctrl_factors l₀ l₁) (ctrl_factors l₀' l₁')

/-! ## The source and the loop on the pair at the source entry -/

/-- A region that duplicates its input and runs a loop on the pair that
factors through a router table is, at each constant input, that table
entered at the row of the constant, carrying the constant. -/
theorem dup_loop_pointed {S body : Region signature.Instr} (hS : ValueBranches [Bit] S [Bit])
    (hb : ValueBranches [Pair] body [Silmaril.coprod Bit Pair]) (t : Router 1)
    (src : QLit hS = QLit dupEntry_typed ≫ QLit (loopRegion_typed hb))
    (fac : Factors pairDec (loopRegion Pair body) t) (q : Bool) :
    Eqv false [U] (constEntry q (seqRegion (unpackExits [Bit]) S)) (constEntry q (t.entered (pairIdx q))) [Bit] := by
  have hloop := loopRegion_typed hb
  have dupq : QLit (pairVar2_typed q) =
      QLit (const_typed q) ≫ QLit unpack_typed ≫ QLit dupEntry_typed :=
    (congrArg (π).map (const_dup q).symm).trans
      (((π).map_comp _ _).trans (congrArg (QLit (const_typed q) ≫ ·) ((π).map_comp _ _)))
  have left : QLit (constEntry_typed q (seqRegion_typed unpack_typed hS)) = QLit (pairVar2_typed q) ≫ QLit hloop := by
    rw [dupq]
    refine (q_comp (const_typed q) (seqRegion_typed unpack_typed hS)).trans ?_
    refine (congrArg (QLit (const_typed q) ≫ ·)
      ((q_comp unpack_typed hS).trans (congrArg (QLit unpack_typed ≫ ·) src))).trans ?_
    simp only [Category.assoc]
  have fac : QLit t.loop_typed = QLit pairDec_typed ≫ QLit hloop :=
    ((Paper.Extension.Singleton.ofRegion_eq_iff N (seqRegion_typed pairDec_typed hloop)
      t.loop_typed).2 fac).symm.trans (q_comp pairDec_typed hloop)
  have rowq : QLit (pairLitVar_typed q) =
      QLit (const_typed q) ≫ (π).map (injArr 1 (pairIdx q)) ≫ QLit pairDec_typed :=
    (congrArg (π).map (const_row_dec q).symm).trans
      (((π).map_comp _ _).trans (congrArg (QLit (const_typed q) ≫ ·) ((π).map_comp _ _)))
  have ent : QLit (t.entered_typed (pairIdx q)) =
      (π).map (injArr 1 (pairIdx q)) ≫ QLit t.loop_typed :=
    (congrArg (π).map (dispatchEntered_arrow t.rows_typed (pairIdx q))).trans ((π).map_comp _ _)
  have right : QLit (constEntry_typed q (t.entered_typed (pairIdx q))) =
      QLit (pairLitVar_typed q) ≫ QLit hloop := by
    rw [rowq]
    refine (q_comp (const_typed q) (t.entered_typed (pairIdx q))).trans ?_
    refine (congrArg (QLit (const_typed q) ≫ ·)
      (ent.trans (congrArg ((π).map (injArr 1 (pairIdx q)) ≫ ·) fac))).trans ?_
    simp only [Category.assoc]
  exact (Paper.Extension.Singleton.ofRegion_eq_iff N (constEntry_typed q (seqRegion_typed unpack_typed hS))
    (constEntry_typed q (t.entered_typed (pairIdx q)))).1
    (left.trans ((congrArg (· ≫ QLit hloop) (pair_lit_var q).symm).trans right.symm))


theorem ctrl_loop_pointed (l₀ l₁ : Bool) :
    SpinPointed (seqRegion (unpackExits [Bit]) (ctrlLoop l₀ l₁))
      (fun i => some (pickLabel l₀ l₁ (pairBit i))) captAct pairIdx := by
  intro q
  rw [ctrl_spin]
  exact dup_loop_pointed (ctrlLoop_typed l₀ l₁) (ctrlBody_typed l₀ l₁) (ctrlRouter l₀ l₁)
    (q_comp dupEntry_typed (loopRegion_typed (ctrlBody_typed l₀ l₁))) (ctrl_factors l₀ l₁) q

/-- A region on a Bit is its run on the Bit of a state, after packing. -/
theorem state_unwrap {s : Region signature.Instr} (hs : ValueBranches [Bit] s [Bit]) :
    QLit hs = QLit bitState_typed ≫ QLit (seqRegion_typed unpack_typed hs) :=
  ((congrArg (QLit bitState_typed ≫ ·) (q_comp unpack_typed hs)).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ QLit hs)
        (((π).map_comp _ _).symm.trans ((congrArg (π).map pack_unpack).trans ((π).map_id _)))).trans
        (Category.id_comp _)))).symm

/-- The source is the loop on the pair of captured input and header
parameter at the source entry, in the opt-in quotient: the two agree at
each constant input, and unit η recombines the two inputs. -/
theorem ctrl_source_loop (l₀ l₁ : Bool) :
    Eqv false [Bit] (ctrlSource l₀ l₁) (ctrlLoop l₀ l₁) [Bit] := by
  have st : Eqv false [State] (seqRegion (unpackExits [Bit]) (ctrlSource l₀ l₁))
      (seqRegion (unpackExits [Bit]) (ctrlLoop l₀ l₁)) [Bit] :=
    spin_pointed_eqv (stateCtrl_typed l₀ l₁) (seqRegion_typed unpack_typed (ctrlLoop_typed l₀ l₁))
      (ctrl_pointed l₀ l₁) (ctrl_loop_pointed l₀ l₁)
      (fun q => Paper.Extension.Eqv.refl
        ((Router.ofSpin (fun i => some (pickLabel l₀ l₁ (pairBit i))) captAct).entered_typed (pairIdx q)).hasType)
  apply (Paper.Extension.Singleton.ofRegion_eq_iff N (ctrlSource_typed l₀ l₁) (ctrlLoop_typed l₀ l₁)).1
  exact (state_unwrap (ctrlSource_typed l₀ l₁)).trans
    ((congrArg (QLit bitState_typed ≫ ·)
      ((Paper.Extension.Singleton.ofRegion_eq_iff N (stateCtrl_typed l₀ l₁)
        (seqRegion_typed unpack_typed (ctrlLoop_typed l₀ l₁))).2 st)).trans
      (state_unwrap (ctrlLoop_typed l₀ l₁)).symm)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables

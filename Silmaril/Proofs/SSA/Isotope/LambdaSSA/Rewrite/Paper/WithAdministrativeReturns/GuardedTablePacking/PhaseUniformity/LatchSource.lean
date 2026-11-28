module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.CaptureDrop

/-! # A two-block cyclic flat source and the loop on pairs -/

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

/-! ## The named table, the flat graph and their typing -/

/-- The named two-block table elaborates to the flat graph. -/
theorem named_latch (l : Bool) :
    Bridge.NamedFlat.elaborate (latchNamed l) [.exit] (fun _ : Fin 1 => LatchReg.p) = some (latchFlat l) := by
  have h : Bridge.NamedFlat.elaborate (latchNamed l) [.exit] (fun _ : Fin 1 => LatchReg.p) =
      some ⟨(latchFlat l).entry, Fin.cases ((latchFlat l).block 0)
        (Fin.cases ((latchFlat l).block 1) Fin.elim0)⟩ := rfl
  refine h.trans (congrArg some (congrArg (LambdaSSA.FiniteCFG.mk _) (funext fun i => ?_)))
  match i with
  | 0 => rfl
  | 1 => rfl

/-- The flat graph is typed in the flat judgment: both blocks receive a
pair, the exit a Bit, and the captured input is a pair. -/
theorem latch_flat_typed (l : Bool) :
    LambdaSSA.FiniteCFG.HasType (.snoc .nil Pair) (fun _ : Fin 2 => Pair) (fun _ : Fin 1 => Bit)
      (latchFlat l) where
  entry := .br (i := 0) .bv
  block := fun i => match i with
    | 0 => .let₂ (A := Bit) (B := Bit) .bv
        (.case (A := Bit) (B := Bit) (.op .bv) (.br (i := 2) .bv) (.br (i := 1) (.pair .bv .bv)))
    | 1 => .br (i := 0) .bv

/-! ## The rows of the readback thread the captured input without using it -/

theorem head_row (l : Bool) :
    ofRegion (headRow_typed l) =
      ofRegion (seqValueBranches (whiskerLeftRegion_typed Pair (headStep_typed l))
        (dropCase_typed (X := Pair) (B := Bit) (A := LatchTags))) :=
  (Paper.TypeCategory.ofRegion_eq_iff _ _).mpr
    (.symm (.let₂ (A := Pair) (B := Pair) (.var rfl) (.let₂ (A := Bit) (B := Bit) (.var rfl)
      (.case (A := Bit) (B := Bit) (.op (.var (i := 0) rfl))
        (drop_inl (X := Pair) (A := LatchTags) (i := 4) rfl (.var (i := 2) rfl))
        (drop_inr (X := Pair) (B := Bit) (i := 4) rfl
          (.inr (.inl (.pair (.var (i := 0) rfl) (.var (i := 2) rfl)))))))))

theorem latch_row :
    ofRegion latchRow_typed =
      ofRegion (seqValueBranches (whiskerLeftRegion_typed Pair latchStep_typed)
        (dropCase_typed (X := Pair) (B := Bit) (A := LatchTags))) :=
  (Paper.TypeCategory.ofRegion_eq_iff _ _).mpr
    (.symm (.let₂ (A := Pair) (B := Pair) (.var rfl)
      (drop_inr (X := Pair) (B := Bit) (i := 1) rfl (.inl (.var (i := 0) rfl)))))

/-! ## The readback as a capture-free loop on the tags -/

/-- The dead row of the empty tail of the tags. -/
@[expose] noncomputable def deadRow :
    {r : Region signature.Instr // ValueBranches [Silmaril.empty] r [Silmaril.coprod Bit LatchState]} :=
  emptyDispatchRep (Silmaril.coprod Bit LatchState)

/-- The dispatcher of the readback is the two-row dispatcher of the rows. -/
theorem disp_typed (l : Bool) :
    ValueBranches [LatchState] (twoRows (headRow l) latchRow deadRow.val) [Silmaril.coprod Bit LatchState] :=
  (dispatcherRep Pair (List.ofFn fun _ : Fin 2 => Pair) (orderedRow (fun _ : Fin 2 => Pair)
    (latchBlocks_typed l))).property

/-- The packed readback enters the capture-free loop on the tags at the
tag of the header. Default Paper. -/
theorem readback_arrow (l : Bool) :
    ofRegion (latchReadback l).property =
      ofRegion tagHead_typed ≫ iterate (freeStep (headStep_typed l) latchStep_typed) := by
  have hloop := loopRegion_typed (disp_typed l)
  have ha : Tm.BranchValue [Pair] (.pair (.var 0) (.inl (.var 0)) : Tm signature.Instr) LatchState :=
    .pair (.var rfl) (.inl (.var rfl))
  have hbr : ValueBranches [Pair] (.br 0 (.pair (.var 0) (.inl (.var 0))) : Region signature.Instr)
      [LatchState] := .br rfl ha
  have hid : ValueBranches [Bit] (.br 0 (.var 0) : Region signature.Instr) [Bit] := .br rfl (.var rfl)
  have shape : ofRegion (latchReadback l).property =
      ofRegion (seqValueBranches (ValueBranches.br (ℓ := 0) (L := [Silmaril.coprod Bit LatchState]) rfl (.inr ha))
        (caseValueBranches hid hloop)) := rfl
  have s₁ := case_inr_arrow ha hid hloop
  have s₂ := ofRegion_comp hbr hloop (seqValueBranches hbr hloop)
  have s₃ := iterate_exact (disp_typed l)
  have s₄ := two_row_drop (headRow_typed l) latchRow_typed deadRow.property (headStep_typed l) latchStep_typed
    (head_row l) latch_row (disp_typed l)
  have hbody : Region.HasType [LatchTags, Pair, Pair] (.br 0 (.var 0) : Region signature.Instr) [LatchTags] :=
    (ValueBranches.br (ℓ := 0) rfl (.var rfl)).hasType
  have s₅ : ofRegion hbr ≫ productSnd (ofType (Φ := signature.Instr) Pair) (ofType LatchTags) =
      ofRegion tagHead_typed :=
    (ofRegion_comp hbr (productSndBranches Pair LatchTags)
      (seqValueBranches hbr (productSndBranches Pair LatchTags))).trans
      ((Paper.TypeCategory.ofRegion_eq_iff _ _).mpr
        (.productBeta (.let₂Beta (A := Pair) (B := LatchTags) (.var rfl) (.inl (.var rfl)) hbody)))
  exact shape.trans (s₁.trans (s₂.symm.trans ((congrArg (ofRegion hbr ≫ ·) (s₃.symm.trans s₄)).trans
    ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ iterate (freeStep (headStep_typed l) latchStep_typed)) s₅)))))

/-! ## Eliminating the back-edge block: native Bekič -/

local notation "P'" => Silmaril.coprod Pair Silmaril.empty

theorem retInl_typed :
    ValueBranches [Bit] (.br 0 (.inl (.var 0)) : Region signature.Instr) [Silmaril.coprod Bit LatchTags] :=
  .br rfl (.inl (.var rfl))

theorem tagLatch_typed :
    ValueBranches [Pair] (.br 0 (.inr (.inr (.inl (.var 0)))) : Region signature.Instr)
      [Silmaril.coprod Bit LatchTags] :=
  .br rfl (.inr (.inr (.inl (.var rfl))))

/-- The header step is the step written on pairs, with its repeat sent
to the tag of the back-edge block. Native case on a constructor. -/
theorem head_step (l : Bool) :
    ofRegion (headStep_typed l) =
      ofRegion (pairBody_typed l) ≫ ofRegion (caseValueBranches retInl_typed tagLatch_typed) := by
  refine ((Paper.TypeCategory.ofRegion_eq_iff _ _).mpr ?_).trans
    (ofRegion_comp (pairBody_typed l) (caseValueBranches retInl_typed tagLatch_typed)
      (seqValueBranches (pairBody_typed l) (caseValueBranches retInl_typed tagLatch_typed))).symm
  have hl : Region.HasType [Bit, Bit, Bit, Bit, Pair] (.br 0 (.inl (.var 0)) : Region signature.Instr)
      [Silmaril.coprod Bit LatchTags] := (ValueBranches.br (ℓ := 0) rfl (.inl (.var rfl))).hasType
  have hr : Region.HasType [Pair, Bit, Bit, Bit, Pair]
      (.br 0 (.inr (.inr (.inl (.var 0)))) : Region signature.Instr) [Silmaril.coprod Bit LatchTags] :=
    (ValueBranches.br (ℓ := 0) rfl (.inr (.inr (.inl (.var rfl))))).hasType
  have left : Paper.Eqv [Bit, Bit, Bit, Pair]
      (.case (.inl (.var 2)) (.br 0 (.inl (.var 0))) (.br 0 (.inr (.inr (.inl (.var 0))))))
      (.br 0 (.inl (.var 2)) : Region signature.Instr) [Silmaril.coprod Bit LatchTags] :=
    (Paper.Eqv.cfgEta (.native (.base (.caseInl (A := Bit) (B := Pair) (.var rfl) hl hr)))).trans
      (.cfgEta (.native (.base (.letBr (ℓ := 0) (A := Bit) (.var rfl) (.inl (.var rfl)) rfl))))
  have right : Paper.Eqv [Bit, Bit, Bit, Pair]
      (.case (.inr (.pair (.var 0) (.var 2))) (.br 0 (.inl (.var 0))) (.br 0 (.inr (.inr (.inl (.var 0))))))
      (.br 0 (.inr (.inr (.inl (.pair (.var 0) (.var 2))))) : Region signature.Instr)
      [Silmaril.coprod Bit LatchTags] :=
    (Paper.Eqv.cfgEta (.native (.base (.caseInr (A := Bit) (B := Pair) (.pair (.var rfl) (.var rfl)) hl hr)))).trans
      (.cfgEta (.native (.base (.letBr (ℓ := 0) (A := Pair) (.pair (.var rfl) (.var rfl))
        (.inr (.inr (.inl (.var rfl)))) rfl))))
  exact .symm (.let₂ (A := Bit) (B := Bit) (.var rfl)
    (.case (A := Bit) (B := Bit) (.op (.var (i := 0) rfl)) left right))

/-- The step written on pairs, as an arrow to the chosen coproduct. -/
noncomputable def pairArr (l : Bool) : ofType (Φ := signature.Instr) Pair ⟶ ofType Bit ⨿ ofType Pair :=
  ofRegion (pairBody_typed l) ≫ (sumIso (Φ := signature.Instr) Bit Pair).hom

/-- The header row of the two blocks: exit, or enter the back-edge block. -/
noncomputable def headBlockRow (l : Bool) :
    ofType (Φ := signature.Instr) Pair ⟶ (ofType Bit ⨿ ofType Pair) ⨿ ofType P' :=
  pairArr l ≫ coprod.desc (coprod.inl ≫ coprod.inl) (sumInl Pair Silmaril.empty ≫ coprod.inr)

/-- The back-edge row: go to the header. -/
noncomputable def latchBlockRow :
    ofType (Φ := signature.Instr) P' ⟶ (ofType Bit ⨿ ofType Pair) ⨿ ofType P' :=
  (sumIso (Φ := signature.Instr) Pair Silmaril.empty).hom ≫
    coprod.desc (coprod.inr ≫ coprod.inl) ((Paper.TypeCategory.emptyIsInitial (Φ := signature.Instr)).to _)

theorem tagHead_arrow : ofRegion tagHead_typed = sumInl (Φ := signature.Instr) Pair P' :=
  (br_inl (.var rfl)).trans ((congrArg (· ≫ _) (ofRegion_id Pair)).trans (Category.id_comp _))

theorem latchStep_arrow :
    ofRegion latchStep_typed ≫ (sumIso (Φ := signature.Instr) Bit LatchTags).hom =
      sumInl (Φ := signature.Instr) Pair P' ≫ coprod.inr := by
  have e : ofRegion latchStep_typed = ofRegion tagHead_typed ≫
      (coprod.inr ≫ (sumIso (Φ := signature.Instr) Bit LatchTags).inv) := br_inr (.inl (.var rfl))
  rw [e, tagHead_arrow]
  simp
  rfl

theorem tagLatch_arrow :
    ofRegion tagLatch_typed = (sumInl (Φ := signature.Instr) Pair Silmaril.empty ≫ sumInr Pair P') ≫
      (coprod.inr ≫ (sumIso (Φ := signature.Instr) Bit LatchTags).inv) := by
  have e₁ : ofRegion tagLatch_typed =
      ofRegion (r := .br 0 (.inr (.inl (.var 0)))) (.br (L := [LatchTags]) rfl (.inr (.inl (.var rfl)))) ≫
        (coprod.inr ≫ (sumIso (Φ := signature.Instr) Bit LatchTags).inv) := br_inr (.inr (.inl (.var rfl)))
  have e₂ : ofRegion (r := (.br 0 (.inr (.inl (.var 0))) : Region signature.Instr))
      (.br (L := [LatchTags]) (Γ := [Pair]) rfl (.inr (.inl (.var rfl)))) =
      ofRegion (r := .br 0 (.inl (.var 0))) (.br (L := [P']) rfl (.inl (.var rfl))) ≫
        (coprod.inr ≫ (sumIso (Φ := signature.Instr) Pair P').inv) := br_inr (.inl (.var rfl))
  have e₃ : ofRegion (r := (.br 0 (.inl (.var 0)) : Region signature.Instr))
      (.br (L := [P']) (Γ := [Pair]) rfl (.inl (.var rfl))) = sumInl (Φ := signature.Instr) Pair Silmaril.empty :=
    (br_inl (.var rfl)).trans ((congrArg (· ≫ _) (ofRegion_id Pair)).trans (Category.id_comp _))
  rw [e₁, e₂, e₃]
  rfl

/-- The capture-free step on the tags is the joined step of the two rows. -/
theorem free_blockStep (l : Bool) :
    freeStep (headStep_typed l) latchStep_typed = blockStep Pair P' (headBlockRow l) latchBlockRow := by
  have ea : ofRegion (headStep_typed l) ≫ (sumIso (Φ := signature.Instr) Bit LatchTags).hom =
      headBlockRow l ≫ blockRoute Pair P' Bit := by
    have retInl_arrow : ofRegion retInl_typed = coprod.inl ≫ (sumIso (Φ := signature.Instr) Bit LatchTags).inv :=
      (br_inl (.var rfl)).trans ((congrArg (· ≫ _) (ofRegion_id Bit)).trans (Category.id_comp _))
    rw [head_step, ← coprod_desc_ofRegion retInl_typed tagLatch_typed, retInl_arrow, tagLatch_arrow]
    unfold headBlockRow pairArr blockRoute
    simp only [Category.assoc]
    congr 2
    apply coprod.hom_ext
    · simp
      rfl
    · simp
  have eb : (sumIso (Φ := signature.Instr) Pair Silmaril.empty).hom ≫
      coprod.desc (ofRegion latchStep_typed ≫ (sumIso (Φ := signature.Instr) Bit LatchTags).hom)
        ((Paper.TypeCategory.emptyIsInitial (Φ := signature.Instr)).to _) =
      latchBlockRow ≫ blockRoute Pair P' Bit := by
    unfold latchBlockRow
    rw [Category.assoc, latchStep_arrow]
    congr 1
    apply coprod.hom_ext
    · unfold blockRoute
      simp
    · exact (Paper.TypeCategory.emptyIsInitial (Φ := signature.Instr)).hom_ext _ _
  exact congrArg ((sumIso (Φ := signature.Instr) Pair P').hom ≫ ·) (congrArg₂ coprod.desc ea eb)

/-- Iterating the back-edge row goes to the header. -/
theorem latch_iterate :
    iterate latchBlockRow = (sumIso (Φ := signature.Instr) Pair Silmaril.empty).hom ≫
      coprod.desc coprod.inr ((Paper.TypeCategory.emptyIsInitial (Φ := signature.Instr)).to _) := by
  refine (iterate_fixpoint latchBlockRow).trans ?_
  unfold latchBlockRow
  rw [Category.assoc]
  congr 1
  apply coprod.hom_ext
  · simp
  · exact (Paper.TypeCategory.emptyIsInitial (Φ := signature.Instr)).hom_ext _ _

/-- With the back-edge block solved, the header row is the step on pairs. -/
theorem head_solved (l : Bool) :
    headBlockRow l ≫ coprod.desc (𝟙 _) (iterate latchBlockRow) = pairArr l := by
  rw [latch_iterate]
  unfold headBlockRow sumInl
  rw [Category.assoc]
  refine (congrArg (pairArr l ≫ ·) ?_).trans (Category.comp_id _)
  apply coprod.hom_ext <;> simp

/-- The capture-free loop on the tags, entered at the header, is the
loop on pairs. Default Paper: Bekič for two blocks at an exact sum. -/
theorem latch_bekic (l : Bool) :
    ofRegion tagHead_typed ≫ iterate (freeStep (headStep_typed l) latchStep_typed) =
      ofRegion (loopRegion_typed (pairBody_typed l)) := by
  rw [tagHead_arrow, free_blockStep, (iterate_blockStep Pair P' (headBlockRow l) latchBlockRow).1, head_solved]
  exact iterate_exact (pairBody_typed l)

/-- The packed readback of the two-block source is the loop on pairs, in
default Paper. -/
theorem latch_readback_loop (l : Bool) :
    Paper.Eqv [Pair] (latchReadback l).val (loopRegion Pair (pairBody l)) [Bit] :=
  (Paper.TypeCategory.ofRegion_eq_iff _ _).mp ((readback_arrow l).trans (latch_bekic l))

/-! ## The source: the table-packing seed, then the native reduction -/

/-- The table-packing seed at the two-block source. -/
theorem latch_source_readback (l : Bool) :
    Paper.WithAdministrativeReturns.WithGuardedTablePacking.Eqv false [Pair] (latchSource l)
      (latchReadback l).val [Bit] := by
  rw [latchSource_eq]
  exact Paper.WithAdministrativeReturns.WithGuardedTablePacking.pack false (fun _ : Fin 2 => Pair)
    latchEntry_typed (latchBlocks_typed l)

/-- The two-block source is the loop on pairs at the source entry: the
seed, then default Paper. -/
theorem latch_source_loop (l : Bool) :
    Paper.WithAdministrativeReturns.WithGuardedTablePacking.Eqv false [Pair] (latchSource l)
      (loopRegion Pair (pairBody l)) [Bit] :=
  (latch_source_readback l).trans (.paper (latch_readback_loop l))

theorem q_latch_loop (l : Bool) : Eqv false [Pair] (latchSource l) (loopRegion Pair (pairBody l)) [Bit] :=
  Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.ofTablePacking false
    (latch_source_loop l)

/-- A guarded source equal to the loop on pairs factors through the
packed loop of the router table. -/
theorem factors_of_loop {src : Region signature.Instr} (hs : ValueBranches [Pair] src [Bit]) (l : Bool)
    (e : Eqv false [Pair] src (loopRegion Pair (pairBody l)) [Bit]) : Factors pairDec src (pairRouter l) := by
  have packed : Eqv false [States 1] (seqRegion pairDec src)
      (seqRegion pairDec (loopRegion Pair (pairBody l))) [Bit] :=
    (Paper.Extension.Singleton.ofRegion_eq_iff N (seqRegion_typed pairDec_typed hs)
      (seqRegion_typed pairDec_typed (loopRegion_typed (pairBody_typed l)))).1
      ((q_comp pairDec_typed hs).trans
        ((congrArg (QLit pairDec_typed ≫ ·)
          ((Paper.Extension.Singleton.ofRegion_eq_iff N hs (loopRegion_typed (pairBody_typed l))).2 e)).trans
          (q_comp pairDec_typed (loopRegion_typed (pairBody_typed l))).symm))
  exact packed.trans (pair_factors l)

theorem latch_factors (l : Bool) : Factors pairDec (latchSource l) (pairRouter l) :=
  factors_of_loop (latchSource_typed l) l (q_latch_loop l)

open Paper.WithAdministrativeReturns.WithGuardedTablePacking (Valid) in
/-- Two two-block sources are equal at the source entry exactly when
they are valid in every supported model. -/
theorem latch_complete (l l' : Bool) :
    Eqv false [Pair] (latchSource l) (latchSource l') [Bit] ↔
      Valid (latchSource_typed l).hasType (latchSource_typed l').hasType :=
  factored_complete pairEnc_typed pairDec_typed (latchSource_typed l) (latchSource_typed l') enc_dec
    (pairRouter l) (pairRouter l') (latch_factors l) (latch_factors l')

theorem latch_eqv_iff (l l' : Bool) : Eqv false [Pair] (latchSource l) (latchSource l') [Bit] ↔ l = l' :=
  ⟨fun e => (pair_eqv_iff l l').1 ((q_latch_loop l).symm.trans (e.trans (q_latch_loop l'))),
    fun h => h ▸ Paper.Extension.Eqv.refl (latchSource_typed l).hasType⟩

theorem latch_loop_iff (l l' : Bool) :
    Eqv false [Pair] (latchSource l) (loopRegion Pair (pairBody l')) [Bit] ↔ l = l' :=
  ⟨fun e => (pair_eqv_iff l l').1 ((q_latch_loop l).symm.trans e), fun h => h ▸ q_latch_loop l⟩

/-- The two-block source and the one-header source are equal exactly
when their requests have the same label. -/
theorem latch_header_iff (l l' : Bool) :
    Eqv false [Pair] (latchSource l) (pairSource l') [Bit] ↔ l = l' :=
  ⟨fun e => (latch_loop_iff l l').1 (e.trans (q_source_loop l')),
    fun h => h ▸ (q_latch_loop l).trans (q_source_loop l).symm⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables

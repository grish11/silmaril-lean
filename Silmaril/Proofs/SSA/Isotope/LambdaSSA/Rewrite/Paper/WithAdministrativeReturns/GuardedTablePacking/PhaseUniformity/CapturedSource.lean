module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Packed.Product.Flat.Latch.Captured.Defs
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.CaptureKeep

/-! # A two-block source whose header returns the captured input -/

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

/-! ## The tail that keeps and returns the captured input -/

section Keep

variable {X E A : Ty Empty}

local notation "Z" => ofType (Φ := signature.Instr) X

theorem fstInl_typed :
    ValueBranches [Silmaril.product X E] (.let₂ (.var 0) (.br 0 (.inl (.var 1))) : Region signature.Instr)
      [Silmaril.coprod X (Silmaril.product X A)] :=
  .let₂ (A := X) (B := E) (.var rfl) (.br rfl (.inl (.var rfl)))

theorem inrState_typed :
    ValueBranches [Silmaril.product X A] (.br 0 (.inr (.var 0)) : Region signature.Instr)
      [Silmaril.coprod X (Silmaril.product X A)] :=
  .br rfl (.inr (.var rfl))

/-- `keepCase` is the distributor followed by the first projection on the
return side. Product β and the native case on a constructor. -/
theorem keepCase_eqv :
    Paper.Eqv [Silmaril.product X (Silmaril.coprod E A)] keepCase
      (seqRegion distributorRegion (.case (.var 0) (.let₂ (.var 0) (.br 0 (.inl (.var 1))))
        (.br 0 (.inr (.var 0)))))
      [Silmaril.coprod X (Silmaril.product X A)] := by
  have hfstL : Region.HasType [Silmaril.product X E, E, Silmaril.coprod E A, X,
      Silmaril.product X (Silmaril.coprod E A)]
      (.let₂ (.var 0) (.br 0 (.inl (.var 1))) : Region signature.Instr)
      [Silmaril.coprod X (Silmaril.product X A)] :=
    (ValueBranches.let₂ (A := X) (B := E) (.var rfl) (.br rfl (.inl (.var rfl)))).hasType
  have hkeepL : Region.HasType [Silmaril.product X A, E, Silmaril.coprod E A, X,
      Silmaril.product X (Silmaril.coprod E A)]
      (.br 0 (.inr (.var 0)) : Region signature.Instr) [Silmaril.coprod X (Silmaril.product X A)] :=
    (ValueBranches.br (ℓ := 0) rfl (.inr (.var rfl))).hasType
  have hfstR : Region.HasType [Silmaril.product X E, A, Silmaril.coprod E A, X,
      Silmaril.product X (Silmaril.coprod E A)]
      (.let₂ (.var 0) (.br 0 (.inl (.var 1))) : Region signature.Instr)
      [Silmaril.coprod X (Silmaril.product X A)] :=
    (ValueBranches.let₂ (A := X) (B := E) (.var rfl) (.br rfl (.inl (.var rfl)))).hasType
  have hkeepR : Region.HasType [Silmaril.product X A, A, Silmaril.coprod E A, X,
      Silmaril.product X (Silmaril.coprod E A)]
      (.br 0 (.inr (.var 0)) : Region signature.Instr) [Silmaril.coprod X (Silmaril.product X A)] :=
    (ValueBranches.br (ℓ := 0) rfl (.inr (.var rfl))).hasType
  have hbody : Region.HasType [E, X, E, Silmaril.coprod E A, X, Silmaril.product X (Silmaril.coprod E A)]
      (.br 0 (.inl (.var 1)) : Region signature.Instr) [Silmaril.coprod X (Silmaril.product X A)] :=
    (ValueBranches.br (ℓ := 0) rfl (.inl (.var (i := 1) rfl))).hasType
  have left : Paper.Eqv [E, Silmaril.coprod E A, X, Silmaril.product X (Silmaril.coprod E A)]
      (.case (.inl (.pair (.var 2) (.var 0))) (.let₂ (.var 0) (.br 0 (.inl (.var 1))))
        (.br 0 (.inr (.var 0))))
      (.br 0 (.inl (.var 2)) : Region signature.Instr) [Silmaril.coprod X (Silmaril.product X A)] :=
    (Paper.Eqv.cfgEta (.native (.base (.caseInl (A := Silmaril.product X E) (B := Silmaril.product X A)
      (.pair (.var rfl) (.var rfl)) hfstL hkeepL)))).trans
      ((Paper.Eqv.cfgEta (.native (.letValue (.pair (.var rfl) (.var rfl)) hfstL))).trans
        (.productBeta (.let₂Beta (A := X) (B := E) (.var rfl) (.var rfl) hbody)))
  have right : Paper.Eqv [A, Silmaril.coprod E A, X, Silmaril.product X (Silmaril.coprod E A)]
      (.case (.inr (.pair (.var 2) (.var 0))) (.let₂ (.var 0) (.br 0 (.inl (.var 1))))
        (.br 0 (.inr (.var 0))))
      (.br 0 (.inr (.pair (.var 2) (.var 0))) : Region signature.Instr)
      [Silmaril.coprod X (Silmaril.product X A)] :=
    (Paper.Eqv.cfgEta (.native (.base (.caseInr (A := Silmaril.product X E) (B := Silmaril.product X A)
      (.pair (.var rfl) (.var rfl)) hfstR hkeepR)))).trans
      (.cfgEta (.native (.base (.letBr (ℓ := 0) (.pair (.var rfl) (.var rfl)) (.inr (.var rfl)) rfl))))
  exact .symm (.let₂ (A := X) (B := Silmaril.coprod E A) (.var rfl)
    (.case (A := E) (B := A) (.var rfl) left right))

/-- The arrow of `keepCase`: the inverse comparison of the fixed left
factor followed by the first projection on the return side. -/
theorem keepCase_arrow :
    ofRegion (keepCase_typed (X := X) (E := E) (A := A)) ≫
        (sumIso (Φ := signature.Instr) X (Silmaril.product X A)).hom =
      whiskerLeft Z (sumIso (Φ := signature.Instr) E A).hom ≫
        ((leftCoproductComparisonIso Z (ofType E) (ofType A)).inv ≫
          coprod.map (ofRegion (τ := Ty Empty) (fstRegion_typed (X := X) (E := E)))
            (𝟙 (tensorObj Z (ofType A)))) := by
  have hl := fstInl_typed (X := X) (E := E) (A := A)
  have hr := inrState_typed (X := X) (A := A)
  have inlB : ValueBranches [X] (.br 0 (.inl (.var 0)) : Region signature.Instr)
      [Silmaril.coprod X (Silmaril.product X A)] := .br rfl (.inl (.var rfl))
  have e : ofRegion (keepCase_typed (X := X) (E := E) (A := A)) =
      ofRegion (seqValueBranches (distributorRegion_typed X E A) (caseValueBranches hl hr)) :=
    (Paper.TypeCategory.ofRegion_eq_iff _ _).mpr keepCase_eqv
  have c := ofRegion_comp (distributorRegion_typed X E A) (caseValueBranches hl hr)
    (seqValueBranches (distributorRegion_typed X E A) (caseValueBranches hl hr))
  have d := coprod_desc_ofRegion hl hr
  have l₀ : ofRegion inlB = coprod.inl ≫ (sumIso (Φ := signature.Instr) X (Silmaril.product X A)).inv :=
    (br_inl (.var rfl)).trans ((congrArg (· ≫ _) (ofRegion_id X)).trans (Category.id_comp _))
  have l : ofRegion hl = ofRegion (τ := Ty Empty) (fstRegion_typed (X := X) (E := E)) ≫ coprod.inl ≫
      (sumIso (Φ := signature.Instr) X (Silmaril.product X A)).inv :=
    (ofRegion_comp (fstRegion_typed (X := X) (E := E)) inlB hl).symm.trans
      (congrArg (ofRegion (τ := Ty Empty) (fstRegion_typed (X := X) (E := E)) ≫ ·) l₀)
  have r : ofRegion hr = coprod.inr ≫ (sumIso (Φ := signature.Instr) X (Silmaril.product X A)).inv :=
    (br_inr (.var rfl)).trans ((congrArg (· ≫ _) (ofRegion_id (Silmaril.product X A))).trans (Category.id_comp _))
  have w : whiskerLeft Z (sumIso (Φ := signature.Instr) E A).hom ≫
      whiskerLeft Z (sumIso (Φ := signature.Instr) E A).inv = 𝟙 _ := by
    rw [← whiskerLeft_comp, Iso.hom_inv_id, whiskerLeft_id]
  have rhs : whiskerLeft Z (sumIso (Φ := signature.Instr) E A).hom ≫
      ((leftCoproductComparisonIso Z (ofType E) (ofType A)).inv ≫
        coprod.map (ofRegion (τ := Ty Empty) (fstRegion_typed (X := X) (E := E))) (𝟙 (tensorObj Z (ofType A)))) =
      ofRegion (distributorRegion_typed X E A) ≫
        (sumIso (Φ := signature.Instr) (Silmaril.product X E) (Silmaril.product X A)).hom ≫
          coprod.map (ofRegion (τ := Ty Empty) (fstRegion_typed (X := X) (E := E)))
            (𝟙 (tensorObj Z (ofType A))) := by
    rw [leftCoproductComparisonIso_inv]
    change whiskerLeft Z (sumIso (Φ := signature.Instr) E A).hom ≫
      ((whiskerLeft Z (sumIso (Φ := signature.Instr) E A).inv ≫
        ofRegion (τ := Ty Empty) (distributorRegion_typed X E A) ≫
        (sumIso (Φ := signature.Instr) (Silmaril.product X E) (Silmaril.product X A)).hom) ≫ _) = _
    rw [Category.assoc, ← Category.assoc (whiskerLeft Z (sumIso (Φ := signature.Instr) E A).hom), w,
      Category.id_comp, Category.assoc]
  rw [rhs, e, ← c, ← d, l, r]
  simp only [Category.assoc]
  congr 2
  apply coprod.hom_ext <;> simp <;> first | rfl | exact (Category.id_comp _).symm

variable {Γ : VCtx (Ty Empty)} {i : Nat} {d t : Tm signature.Instr}

/-- On a returned value the tail returns the captured input. -/
theorem keep_inl (hi : At Γ i X) (hd : Tm.BranchValue Γ d E) :
    Paper.Eqv Γ
      (.let₂ (.pair (.var i) (.inl d))
        (.case (.var 0) (.br 0 (.inl (.var 2))) (.br 0 (.inr (.pair (.var 2) (.var 0))))))
      (.br 0 (.inl (.var i)) : Region signature.Instr) [Silmaril.coprod X (Silmaril.product X A)] := by
  have hl : Region.HasType (E :: Γ) (.br 0 (.inl (.var (i + 1))) : Region signature.Instr)
      [Silmaril.coprod X (Silmaril.product X A)] :=
    (ValueBranches.br (Γ := E :: Γ) (ℓ := 0) rfl
      (.inl (.var (i := i + 1) (show At (E :: Γ) (i + 1) X from hi)))).hasType
  have hr : Region.HasType (A :: Γ) (.br 0 (.inr (.pair (.var (i + 1)) (.var 0))) : Region signature.Instr)
      [Silmaril.coprod X (Silmaril.product X A)] :=
    (ValueBranches.br (Γ := A :: Γ) (ℓ := 0) rfl
      (.inr (.pair (.var (i := i + 1) (show At (A :: Γ) (i + 1) X from hi)) (.var (i := 0) rfl)))).hasType
  have hbody : Region.HasType (Silmaril.coprod E A :: X :: Γ)
      (.case (.var 0) (.br 0 (.inl (.var 2))) (.br 0 (.inr (.pair (.var 2) (.var 0)))) : Region signature.Instr)
      [Silmaril.coprod X (Silmaril.product X A)] :=
    (ValueBranches.case (A := E) (B := A) (.var rfl) (.br rfl (.inl (.var (i := 2) rfl)))
      (.br rfl (.inr (.pair (.var rfl) (.var rfl))))).hasType
  exact (Paper.Eqv.productBeta (.let₂Beta (A := X) (B := Silmaril.coprod E A) (.var hi) (.inl hd) hbody)).trans
    ((Paper.Eqv.cfgEta (.native (.base (.caseInl (A := E) (B := A) hd.hasType hl hr)))).trans
      (.cfgEta (.native (.base (.letBr (ℓ := 0) hd
        (.inl (.var (i := i + 1) (show At (E :: Γ) (i + 1) X from hi))) rfl)))))

/-- On a repeated state the tail keeps the captured input. -/
theorem keep_inr {E' : Ty Empty} (hi : At Γ i X) (ht : Tm.BranchValue Γ t A) :
    Paper.Eqv Γ
      (.let₂ (.pair (.var i) (.inr t))
        (.case (.var 0) (.br 0 (.inl (.var 2))) (.br 0 (.inr (.pair (.var 2) (.var 0))))))
      (.br 0 (.inr (.pair (.var i) t)) : Region signature.Instr) [Silmaril.coprod X (Silmaril.product X A)] := by
  have hl : Region.HasType (E' :: Γ) (.br 0 (.inl (.var (i + 1))) : Region signature.Instr)
      [Silmaril.coprod X (Silmaril.product X A)] :=
    (ValueBranches.br (Γ := E' :: Γ) (ℓ := 0) rfl
      (.inl (.var (i := i + 1) (show At (E' :: Γ) (i + 1) X from hi)))).hasType
  have hr : Region.HasType (A :: Γ) (.br 0 (.inr (.pair (.var (i + 1)) (.var 0))) : Region signature.Instr)
      [Silmaril.coprod X (Silmaril.product X A)] :=
    (ValueBranches.br (Γ := A :: Γ) (ℓ := 0) rfl
      (.inr (.pair (.var (i := i + 1) (show At (A :: Γ) (i + 1) X from hi)) (.var (i := 0) rfl)))).hasType
  have hbody : Region.HasType (Silmaril.coprod E' A :: X :: Γ)
      (.case (.var 0) (.br 0 (.inl (.var 2))) (.br 0 (.inr (.pair (.var 2) (.var 0)))) : Region signature.Instr)
      [Silmaril.coprod X (Silmaril.product X A)] :=
    (ValueBranches.case (A := E') (B := A) (.var rfl) (.br rfl (.inl (.var (i := 2) rfl)))
      (.br rfl (.inr (.pair (.var rfl) (.var rfl))))).hasType
  exact (Paper.Eqv.productBeta (.let₂Beta (A := X) (B := Silmaril.coprod E' A) (.var hi) (.inr ht) hbody)).trans
    ((Paper.Eqv.cfgEta (.native (.base (.caseInr (A := E') (B := A) ht.hasType hl hr)))).trans
      (.cfgEta (.native (.base (.letBr (ℓ := 0) ht
        (.inr (.pair (.var (i := i + 1) (show At (A :: Γ) (i + 1) X from hi)) (.var (i := 0) rfl))) rfl)))))

end Keep

/-! ## The source: typing and rows -/

/-- The flat graph is typed in the flat judgment: both blocks receive a
Bit, the exit a Bit, and the captured input is a Bit. -/
theorem capt_flat_typed (l : Bool) :
    LambdaSSA.FiniteCFG.HasType (.snoc .nil Bit) (fun _ : Fin 2 => Bit) (fun _ : Fin 1 => Bit)
      (captFlat l) where
  entry := .br (i := 0) .bv
  block := fun i => match i with
    | 0 => .case (A := Bit) (B := Bit) (.op .bv) (.br (i := 2) .bv) (.br (i := 1) .bv)
    | 1 => .br (i := 0) .bv

/-- The header row is the capture-free step whiskered by the captured
input, followed by the tail that returns the captured input. -/
theorem capt_head_row (l : Bool) :
    ofRegion (captHeadRow_typed l) =
      ofRegion (seqValueBranches (whiskerLeftRegion_typed Bit (pollHead_typed l))
        (keepCase_typed (X := Bit) (E := Bit) (A := CaptTags))) :=
  (Paper.TypeCategory.ofRegion_eq_iff _ _).mpr
    (.symm (.let₂ (A := Bit) (B := Bit) (.var rfl)
      (.case (A := Bit) (B := Bit) (.op (.var (i := 0) rfl))
        (keep_inl (X := Bit) (A := CaptTags) (i := 2) rfl (.var (i := 0) rfl))
        (keep_inr (X := Bit) (E' := Bit) (i := 2) rfl (.inr (.inl (.var (i := 0) rfl)))))))

theorem capt_latch_row :
    ofRegion captLatchRow_typed =
      ofRegion (seqValueBranches (whiskerLeftRegion_typed Bit (latchStepG_typed (A := Bit) (E := Bit)))
        (keepCase_typed (X := Bit) (E := Bit) (A := CaptTags))) :=
  (Paper.TypeCategory.ofRegion_eq_iff _ _).mpr
    (.symm (.let₂ (A := Bit) (B := Bit) (.var rfl)
      (keep_inr (X := Bit) (E' := Bit) (i := 1) rfl (.inl (.var (i := 0) rfl)))))

/-- The capture-free header step is the poll step with its repeat sent
to the tag of the back-edge block. -/
theorem poll_head_step (l : Bool) :
    ofRegion (pollHead_typed l) =
      ofRegion (pollBody_typed l) ≫
        ofRegion (caseValueBranches (retInlG_typed (A := Bit) (E := Bit)) tagLatchG_typed) := by
  refine ((Paper.TypeCategory.ofRegion_eq_iff _ _).mpr ?_).trans
    (ofRegion_comp (pollBody_typed l) (caseValueBranches (retInlG_typed (A := Bit) (E := Bit)) tagLatchG_typed)
      (seqValueBranches (pollBody_typed l)
        (caseValueBranches (retInlG_typed (A := Bit) (E := Bit)) tagLatchG_typed))).symm
  have hl : Region.HasType [Bit, Bit, Bit] (.br 0 (.inl (.var 0)) : Region signature.Instr)
      [Silmaril.coprod Bit CaptTags] := (ValueBranches.br (ℓ := 0) rfl (.inl (.var rfl))).hasType
  have hr : Region.HasType [Bit, Bit, Bit] (.br 0 (.inr (.inr (.inl (.var 0)))) : Region signature.Instr)
      [Silmaril.coprod Bit CaptTags] := (ValueBranches.br (ℓ := 0) rfl (.inr (.inr (.inl (.var rfl))))).hasType
  have left : Paper.Eqv [Bit, Bit]
      (.case (.inl (.var 0)) (.br 0 (.inl (.var 0))) (.br 0 (.inr (.inr (.inl (.var 0))))))
      (.br 0 (.inl (.var 0)) : Region signature.Instr) [Silmaril.coprod Bit CaptTags] :=
    (Paper.Eqv.cfgEta (.native (.base (.caseInl (A := Bit) (B := Bit) (.var rfl) hl hr)))).trans
      (.cfgEta (.native (.base (.letBr (ℓ := 0) (A := Bit) (.var rfl) (.inl (.var rfl)) rfl))))
  have right : Paper.Eqv [Bit, Bit]
      (.case (.inr (.var 0)) (.br 0 (.inl (.var 0))) (.br 0 (.inr (.inr (.inl (.var 0))))))
      (.br 0 (.inr (.inr (.inl (.var 0)))) : Region signature.Instr) [Silmaril.coprod Bit CaptTags] :=
    (Paper.Eqv.cfgEta (.native (.base (.caseInr (A := Bit) (B := Bit) (.var rfl) hl hr)))).trans
      (.cfgEta (.native (.base (.letBr (ℓ := 0) (A := Bit) (.var rfl) (.inr (.inr (.inl (.var rfl)))) rfl))))
  exact .symm (.case (A := Bit) (B := Bit) (.op (.var (i := 0) rfl)) left right)

/-! ## The readback keeps the captured input as a factor of the loop state -/

local notation "ZB" => ofType (Φ := signature.Instr) Bit

/-- The dead row of the empty tail of the tags. -/
@[expose] noncomputable def captDead :
    {r : Region signature.Instr // ValueBranches [Silmaril.empty] r [Silmaril.coprod Bit CaptState]} :=
  emptyDispatchRep (Silmaril.coprod Bit CaptState)

theorem capt_disp_typed (l : Bool) :
    ValueBranches [CaptState] (twoRows (captHeadRow l) latchRow captDead.val) [Silmaril.coprod Bit CaptState] :=
  (dispatcherRep Bit (List.ofFn fun _ : Fin 2 => Bit) (orderedRow (fun _ : Fin 2 => Bit)
    (captBlocks_typed l))).property

/-- The poll step as an arrow to the chosen coproduct. -/
@[expose] noncomputable def pollArr (l : Bool) : ofType (Φ := signature.Instr) Bit ⟶ ofType Bit ⨿ ofType Bit :=
  ofRegion (pollBody_typed l) ≫ (sumIso (Φ := signature.Instr) Bit Bit).hom

/-- The packed readback duplicates the input, runs the capture-free poll
loop on one copy while keeping the other, and returns the kept copy.
Default Paper: lifted rows, iteration strength and naturality, Bekič. -/
theorem capt_readback_arrow (l : Bool) :
    ofRegion (captReadback l).property =
      ofRegion dupEntry_typed ≫ (whiskerLeft ZB (iterate (pollArr l)) ≫
        ofRegion (τ := Ty Empty) (fstRegion_typed (X := Bit) (E := Bit))) := by
  have hloop := loopRegion_typed (capt_disp_typed l)
  have ha : Tm.BranchValue [Bit] (.pair (.var 0) (.inl (.var 0)) : Tm signature.Instr) CaptState :=
    .pair (.var rfl) (.inl (.var rfl))
  have hbr : ValueBranches [Bit] (.br 0 (.pair (.var 0) (.inl (.var 0))) : Region signature.Instr)
      [CaptState] := .br rfl ha
  have hid : ValueBranches [Bit] (.br 0 (.var 0) : Region signature.Instr) [Bit] := .br rfl (.var rfl)
  have shape : ofRegion (captReadback l).property =
      ofRegion (seqValueBranches (ValueBranches.br (ℓ := 0) (L := [Silmaril.coprod Bit CaptState]) rfl (.inr ha))
        (caseValueBranches hid hloop)) := rfl
  have s₁ := case_inr_arrow ha hid hloop
  have s₂ := ofRegion_comp hbr hloop (seqValueBranches hbr hloop)
  have s₃ := iterate_exact (capt_disp_typed l)
  have s₄ := two_row_keep (keepCase_typed (X := Bit) (E := Bit) (A := CaptTags))
    (ofRegion (τ := Ty Empty) (fstRegion_typed (X := Bit) (E := Bit))) keepCase_arrow
    (captHeadRow_typed l) captLatchRow_typed captDead.property (pollHead_typed l)
    (latchStepG_typed (A := Bit) (E := Bit)) (capt_head_row l) capt_latch_row (capt_disp_typed l)
  have s₅ := bekic_two (pollBody_typed l) (pollHead_typed l) (poll_head_step l)
  have hwl := whiskerLeftRegion_typed Bit (tagHeadG_typed (A := Bit))
  have hbody : Region.HasType [Bit, Bit, Bit] (.br 0 (.pair (.var 1) (.inl (.var 0))) : Region signature.Instr)
      [CaptState] := (ValueBranches.br (ℓ := 0) rfl (.pair (.var (i := 1) rfl) (.inl (.var (i := 0) rfl)))).hasType
  have s₆ : ofRegion hbr = ofRegion dupEntry_typed ≫ whiskerLeft ZB (ofRegion (tagHeadG_typed (A := Bit))) :=
    ((Paper.TypeCategory.ofRegion_eq_iff _ _).mpr
      (.symm (.productBeta (.let₂Beta (A := Bit) (B := Bit) (.var rfl) (.var rfl) hbody)))).trans
      ((ofRegion_comp dupEntry_typed hwl (seqValueBranches dupEntry_typed hwl)).symm.trans
        (congrArg (ofRegion dupEntry_typed ≫ ·) (whiskerLeft_ofRegion Bit (tagHeadG_typed (A := Bit))).symm))
  have t₁ : whiskerLeft ZB (ofRegion (tagHeadG_typed (A := Bit))) ≫
      whiskerLeft ZB (iterate (freeStep (pollHead_typed l) (latchStepG_typed (A := Bit) (E := Bit)))) =
      whiskerLeft ZB (iterate (pollArr l)) :=
    (whiskerLeft_comp ZB _ _).symm.trans (congrArg (whiskerLeft ZB) s₅)
  exact shape.trans (s₁.trans (s₂.symm.trans ((congrArg (ofRegion hbr ≫ ·) (s₃.symm.trans s₄)).trans
    ((congrArg (· ≫ (whiskerLeft ZB (iterate (freeStep (pollHead_typed l)
        (latchStepG_typed (A := Bit) (E := Bit)))) ≫
        ofRegion (τ := Ty Empty) (fstRegion_typed (X := Bit) (E := Bit)))) s₆).trans
      ((Category.assoc _ _ _).trans (congrArg (ofRegion dupEntry_typed ≫ ·)
        ((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ ofRegion (τ := Ty Empty) (fstRegion_typed (X := Bit) (E := Bit))) t₁))))))))

/-- The step on the pair of captured input and parameter is the poll
step whiskered by the captured input, followed by the keeping tail. -/
theorem capt_body_arrow (l : Bool) :
    ofRegion (captBody_typed l) ≫ (sumIso (Φ := signature.Instr) Bit Pair).hom =
      (whiskerLeft ZB (pollArr l) ≫ (leftCoproductComparisonIso ZB (ofType Bit) (ofType Bit)).inv) ≫
        coprod.map (ofRegion (τ := Ty Empty) (fstRegion_typed (X := Bit) (E := Bit)))
          (𝟙 (tensorObj ZB (ofType Bit))) := by
  have hseq := seqValueBranches (whiskerLeftRegion_typed Bit (pollBody_typed l))
    (keepCase_typed (X := Bit) (E := Bit) (A := Bit))
  have e : ofRegion (captBody_typed l) = ofRegion hseq :=
    (Paper.TypeCategory.ofRegion_eq_iff _ _).mpr
      (.symm (.let₂ (A := Bit) (B := Bit) (.var rfl)
        (.case (A := Bit) (B := Bit) (.op (.var (i := 0) rfl))
          (keep_inl (X := Bit) (A := Bit) (i := 2) rfl (.var (i := 0) rfl))
          (keep_inr (X := Bit) (E' := Bit) (i := 2) rfl (.var (i := 0) rfl)))))
  have c := ofRegion_comp (whiskerLeftRegion_typed Bit (pollBody_typed l))
    (keepCase_typed (X := Bit) (E := Bit) (A := Bit)) hseq
  have k := keepCase_arrow (X := Bit) (E := Bit) (A := Bit)
  unfold pollArr
  rw [e, ← c, whiskerLeft_comp, whiskerLeft_ofRegion]
  simp only [Category.assoc]
  rw [k]

/-- The loop on the pair is the whiskered poll loop followed by the
first projection. Iteration strength and naturality. -/
theorem capt_loop_arrow (l : Bool) :
    ofRegion (loopRegion_typed (captBody_typed l)) =
      whiskerLeft ZB (iterate (pollArr l)) ≫ ofRegion (τ := Ty Empty) (fstRegion_typed (X := Bit) (E := Bit)) :=
  (iterate_exact (captBody_typed l)).symm.trans
    ((congrArg Paper.TypeCategory.iterate (capt_body_arrow l)).trans
      ((iterate_naturality (whiskerLeft ZB (pollArr l) ≫
          (leftCoproductComparisonIso ZB (ofType Bit) (ofType Bit)).inv)
        (ofRegion (τ := Ty Empty) (fstRegion_typed (X := Bit) (E := Bit)))).symm.trans
        (congrArg (· ≫ ofRegion (τ := Ty Empty) (fstRegion_typed (X := Bit) (E := Bit)))
          (whiskerLeft_iterate ZB (pollArr l)))))

/-- The packed readback is the loop on the pair of captured input and
header parameter, entered with the input in both places. Default Paper. -/
theorem capt_readback_loop (l : Bool) : Paper.Eqv [Bit] (captReadback l).val (captLoop l) [Bit] :=
  (Paper.TypeCategory.ofRegion_eq_iff _ _).mp
    ((capt_readback_arrow l).trans
      ((congrArg (ofRegion dupEntry_typed ≫ ·) (capt_loop_arrow l).symm).trans
        (ofRegion_comp dupEntry_typed (loopRegion_typed (captBody_typed l)) (captLoop_typed l))))

/-! ## The source: the table-packing seed, then the native reduction -/

theorem capt_source_readback (l : Bool) :
    Paper.WithAdministrativeReturns.WithGuardedTablePacking.Eqv false [Bit] (captSource l)
      (captReadback l).val [Bit] := by
  rw [captSource_eq]
  exact Paper.WithAdministrativeReturns.WithGuardedTablePacking.pack false (fun _ : Fin 2 => Bit)
    captEntry_typed (captBlocks_typed l)

/-- The source is the loop on the pair of captured input and parameter,
at the source entry: the seed, then default Paper. -/
theorem capt_source_loop (l : Bool) :
    Paper.WithAdministrativeReturns.WithGuardedTablePacking.Eqv false [Bit] (captSource l) (captLoop l) [Bit] :=
  (capt_source_readback l).trans (.paper (capt_readback_loop l))

/-! ## The router table: conditional on the open step equation -/

/-- If the conjugated step is the dispatcher step, the loop on the pair
factors through the packed loop of the router table. -/
theorem capt_factors_of (l : Bool) (h : Task.captStep l) :
    Factors pairDec (loopRegion Pair (captBody l)) (captRouter l) :=
  conjugate_factors pairEnc_typed pairDec_typed (captBody_typed l) enc_dec (captRouter l) h

open Paper.WithAdministrativeReturns.WithGuardedTablePacking (Valid) in
/-- If the conjugated steps are the dispatcher steps, two loops on the
pair are equal at the product-state entry exactly when they are valid in
every supported model. -/
theorem capt_complete_of (l l' : Bool) (h : Task.captStep l) (h' : Task.captStep l') :
    Eqv false [Pair] (loopRegion Pair (captBody l)) (loopRegion Pair (captBody l')) [Bit] ↔
      Valid (loopRegion_typed (captBody_typed l)).hasType (loopRegion_typed (captBody_typed l')).hasType :=
  factored_complete pairEnc_typed pairDec_typed (loopRegion_typed (captBody_typed l))
    (loopRegion_typed (captBody_typed l')) enc_dec (captRouter l) (captRouter l')
    (capt_factors_of l h) (capt_factors_of l' h')

/-- Two sources are equal at the source entry when their loops on the
pair are equal at the product-state entry. -/
theorem capt_source_of_loops (l l' : Bool)
    (e : Eqv false [Pair] (loopRegion Pair (captBody l)) (loopRegion Pair (captBody l')) [Bit]) :
    Eqv false [Bit] (captSource l) (captSource l') [Bit] := by
  have q : ∀ k, Eqv false [Bit] (captSource k) (captLoop k) [Bit] := fun k =>
    Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.ofTablePacking false
      (capt_source_loop k)
  have loops : Eqv false [Bit] (captLoop l) (captLoop l') [Bit] :=
    (Paper.Extension.Singleton.ofRegion_eq_iff N (captLoop_typed l) (captLoop_typed l')).1
      ((q_comp dupEntry_typed (loopRegion_typed (captBody_typed l))).trans
        ((congrArg (QLit dupEntry_typed ≫ ·)
          ((Paper.Extension.Singleton.ofRegion_eq_iff N (loopRegion_typed (captBody_typed l))
            (loopRegion_typed (captBody_typed l'))).2 e)).trans
          (q_comp dupEntry_typed (loopRegion_typed (captBody_typed l'))).symm))
  exact (q l).trans (loops.trans (q l').symm)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables

module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Capture.Defs
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.CompositeTables

/-! # A kept Bit: the factoring, and the kept Bit as a constant under its request -/

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

/-! ## The factoring, in default Paper -/

/-- The packed program that keeps its first reply is the packed
one-request program followed by the chain into the second step. -/
theorem cap_packed (l₁ l₂ : Bool) :
    ofRegion (seqValueBranches (labelPoll l₁).program.typed.packExits (chain_typed (capSecond l₂))) =
      ofRegion (capProgram l₁ l₂).typed.packExits := by
  have left := Paper.Eqv.substVars (Δ := [Bit, Bit]) (θ := fun i => (.var i : Tm signature.Instr))
    ((Paper.TypeCategory.ofRegion_eq_iff _ _).mp (chain_inl (capSecond l₂))) (fun _ _ h => weaken h)
  have right := Paper.Eqv.substVars (Δ := [Bit, Bit]) (θ := fun i => (.var i : Tm signature.Instr))
    ((Paper.TypeCategory.ofRegion_eq_iff _ _).mp (chain_inr (capSecond l₂))) (fun _ _ h => weaken h)
  have hop : Tm.HasType [Bit] (.op (.ask l₁) (.var 0) : Tm signature.Instr) (Silmaril.coprod Bit Bit) :=
    .op (.var (i := 0) rfl)
  exact (Paper.TypeCategory.ofRegion_eq_iff _ _).mpr (Paper.Eqv.case hop left right)

/-- A step factors when its packed program does. -/
theorem packed_step {p p₁ p₂ : Program}
    (h : ofRegion (seqValueBranches p₁.typed.packExits (chain_typed p₂)) = ofRegion p.typed.packExits) :
    ofRegion (step_typed p) = ofRegion (chainedStep_typed p₁ p₂) := by
  have a := (ofRegion_comp unpack_typed p.typed.packExits (step_typed p)).symm
  have b := (ofRegion_comp (step_typed p₁) (chain_typed p₂) (chainedStep_typed p₁ p₂)).symm
  have c := (ofRegion_comp unpack_typed p₁.typed.packExits (step_typed p₁)).symm
  have d := (ofRegion_comp p₁.typed.packExits (chain_typed p₂)
    (seqValueBranches p₁.typed.packExits (chain_typed p₂))).symm
  rw [a, b, c, Category.assoc, ← d, h]

/-- The row of a factored step is the row of trees that send the second
step, in default Paper. -/
theorem factored_row (K : Nat) {p p₁ p₂ : Program}
    (h : ofRegion (step_typed p) = ofRegion (chainedStep_typed p₁ p₂)) (a : Bool → Bool → Act K) :
    ofRegion (routerRow_typed K p a) =
      ofRegion (genRow_typed p₁ fun x y => treeRegion_typed K (duoKids K p₂ a x y)) := by
  have l := (ofRegion_comp (step_typed p) (routerRoute_typed K a) (routerRow_typed K p a)).symm
  have m := (ofRegion_comp (step_typed p₁) (chain_typed p₂) (chainedStep_typed p₁ p₂)).symm
  have r := (ofRegion_comp (step_typed p₁)
    (genRoute_typed fun x y => treeRegion_typed K (duoKids K p₂ a x y))
    (genRow_typed p₁ fun x y => treeRegion_typed K (duoKids K p₂ a x y))).symm
  rw [l, h, m, Category.assoc, chain_route, ← r]

theorem cap_step_arrow (l₁ l₂ : Bool) :
    ofRegion (step_typed (capProgram l₁ l₂)) =
      ofRegion (chainedStep_typed (labelPoll l₁).program (capSecond l₂)) :=
  packed_step (cap_packed l₁ l₂)

theorem cap_stepFactors (l₁ l₂ : Bool) :
    StepFactors (capProgram l₁ l₂) (labelPoll l₁).program (capSecond l₂) :=
  (Paper.Extension.Singleton.ofRegion_eq_iff N (step_typed (capProgram l₁ l₂))
    (chainedStep_typed (labelPoll l₁).program (capSecond l₂))).1
    (congrArg (π).map (cap_step_arrow l₁ l₂))

/-- The table of programs that keep their first reply and the table whose
second step is still written have the same entered loops, in default
Paper. -/
theorem cap_carried_arrow {K : Nat} (l₁ l₂ : Fin (K + 1) → Bool) (act : Fin (K + 1) → Bool → Bool → Act K)
    (j : Fin (K + 1)) :
    ofRegion ((capRouter l₁ l₂ act).entered_typed j) = ofRegion ((capCarried l₁ l₂ act).entered_typed j) :=
  dispatch_rows_arrow (capRouter l₁ l₂ act).rows_typed (capCarried l₁ l₂ act).rows_typed
    (fun i => factored_row K (cap_step_arrow (l₁ i) (l₂ i)) (act i)) j

/-! ## Unit η of the opt-in quotient -/

theorem unitRet : ValueBranches [U] (.br 0 .unit : Region signature.Instr) [U] := .br rfl .unit

theorem unitId : ValueBranches [U] (.br 0 (.var 0) : Region signature.Instr) [U] := .br rfl (.var rfl)

/-- The unit-η seed that the quotient already contains. -/
theorem unit_eta : Eqv false [U] (.br 0 .unit : Region signature.Instr) (.br 0 (.var 0)) [U] :=
  .extra unitRet.hasType unitId.hasType
    (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr .unit)))))))))

theorem q_unit : QLit unitRet = 𝟙 ((π).obj (ofType (Φ := signature.Instr) U)) :=
  ((Paper.Extension.Singleton.ofRegion_eq_iff N unitRet unitId).2 unit_eta).trans
    ((congrArg (π).map (ofRegion_id U)).trans ((π).map_id _))

/-! ## Cases, in default Paper and in the quotient -/

section Cases

variable {A B D E : Ty Empty} {l r l' r' g : Region signature.Instr}

/-- A case followed by a region is the case of the two composites. -/
theorem case_seq_arrow (hl : ValueBranches [A] l [D]) (hr : ValueBranches [B] r [D])
    (hg : ValueBranches [D] g [E]) :
    ofRegion (caseValueBranches hl hr) ≫ ofRegion hg =
      ofRegion (caseValueBranches (seqValueBranches hl hg) (seqValueBranches hr hg)) := by
  rw [← coprod_desc_ofRegion hl hr, ← coprod_desc_ofRegion (seqValueBranches hl hg) (seqValueBranches hr hg),
    ← ofRegion_comp hl hg (seqValueBranches hl hg), ← ofRegion_comp hr hg (seqValueBranches hr hg)]
  simp

/-- Cases with equal arms in the quotient are equal in the quotient. -/
theorem q_case_congr (hl : ValueBranches [A] l [D]) (hr : ValueBranches [B] r [D])
    (hl' : ValueBranches [A] l' [D]) (hr' : ValueBranches [B] r' [D])
    (e₁ : QLit hl = QLit hl') (e₂ : QLit hr = QLit hr') :
    QLit (caseValueBranches hl hr) = QLit (caseValueBranches hl' hr') := by
  rw [← exactCopair_ofRegion N hl hr, ← exactCopair_ofRegion N hl' hr', e₁, e₂]

end Cases

theorem q_comp {X Y Z : Ty Empty} {r s : Region signature.Instr} (h₁ : ValueBranches [X] r [Y])
    (h₂ : ValueBranches [Y] s [Z]) : QLit (seqValueBranches h₁ h₂) = QLit h₁ ≫ QLit h₂ :=
  (congrArg (π).map (ofRegion_comp h₁ h₂ (seqValueBranches h₁ h₂)).symm).trans ((π).map_comp _ _)

/-! ## A discarded Bit -/

theorem bitDiscard : ValueBranches [Bit] (.br 0 .unit : Region signature.Instr) [U] := .br rfl .unit

/-- Discarding a Bit is the case that discards either unit payload, in
default Paper. This is the native case on a variable. -/
theorem discard_case : ofRegion (caseValueBranches unitRet unitRet) = ofRegion bitDiscard :=
  (Paper.TypeCategory.ofRegion_eq_iff _ _).mpr
    (.cfgEta (.native (.caseValue (A := U) (B := U) (a := .var 0) (.var rfl)
      (ValueBranches.br (ℓ := 0) (Γ := [Bit, Bit]) (L := [U]) rfl .unit).hasType)))

/-- A discarded Bit followed by a region on unit is the case with that
region in both arms, in the quotient. This uses unit η. -/
theorem q_discard {D : Ty Empty} {k : Region signature.Instr} (hk : ValueBranches [U] k [D]) :
    QLit (seqValueBranches bitDiscard hk) = QLit (caseValueBranches hk hk) := by
  have d : ofRegion (seqValueBranches bitDiscard hk) =
      ofRegion (caseValueBranches (seqValueBranches unitRet hk) (seqValueBranches unitRet hk)) := by
    rw [← ofRegion_comp bitDiscard hk (seqValueBranches bitDiscard hk), ← discard_case]
    exact case_seq_arrow unitRet unitRet hk
  have u : QLit (seqValueBranches unitRet hk) = QLit hk := by
    rw [q_comp unitRet hk, q_unit, Category.id_comp]
  exact (congrArg (π).map d).trans (q_case_congr _ _ hk hk u u)

/-! ## The kept Bit replaced by a constant -/

theorem idState : ValueBranches [State] (.br 0 (.var 0) : Region signature.Instr) [State] := .br rfl (.var rfl)

theorem bit_typed (c : Bool) : ValueBranches [U] (.br 0 (bitTm c) : Region signature.Instr) [Bit] :=
  .br rfl (bitTm_typed c)

theorem lit_typed (c : Bool) : ValueBranches [Bit] (.br 0 (litBit c) : Region signature.Instr) [Bit] :=
  .br rfl (litBit_typed c)

/-- The constant followed by a case on its unit payload discards the Bit
and takes the arm of the constant, in default Paper. -/
theorem lit_case {D : Ty Empty} (y : Bool) {r : Bool → Region signature.Instr}
    (h : ∀ b, ValueBranches [U] (r b) [D]) :
    ofRegion (seqValueBranches (lit_typed y) (caseValueBranches (h false) (h true))) =
      ofRegion (seqValueBranches bitDiscard (h y)) := by
  cases y
  · exact case_inl_arrow (X := Bit) (t := (.unit : Tm signature.Instr)) .unit (h false) (h true)
  · exact case_inr_arrow (X := Bit) (t := (.unit : Tm signature.Instr)) .unit (h false) (h true)

section Route

variable {K : Nat} {r : Bool → Bool → Region signature.Instr}
  (h : ∀ x y, ValueBranches [U] (r x y) [Silmaril.coprod Bit (States K)])

/-- Fixing the returned payload to `y` and then routing is the routing
whose return arms are both the arm of `y`, in the quotient. -/
theorem fix_route (y : Bool) :
    QLit (fix_typed y) ≫ QLit (genRoute_typed h) = QLit (genRoute_typed (kept_typed h y)) := by
  have split : QLit (fix_typed y) ≫ QLit (genRoute_typed h) =
      QLit (caseValueBranches (seqValueBranches (litLeft_typed y) (genRoute_typed h))
        (seqValueBranches keep_typed (genRoute_typed h))) :=
    ((π).map_comp _ _).symm.trans
      (congrArg (π).map (case_seq_arrow (litLeft_typed y) keep_typed (genRoute_typed h)))
  have right : ofRegion (seqValueBranches keep_typed (genRoute_typed h)) =
      ofRegion (caseValueBranches (caseValueBranches (h true false) (h true true)) (dead_typed K)) := by
    have red := case_inr_arrow (X := State) (A := Bit) (t := (.var 0 : Tm signature.Instr)) (.var (i := 0) rfl)
      (caseValueBranches (h false false) (h false true))
      (caseValueBranches (caseValueBranches (h true false) (h true true)) (dead_typed K))
    refine red.trans ?_
    have e := (ofRegion_comp idState
      (caseValueBranches (caseValueBranches (h true false) (h true true)) (dead_typed K))
      (seqValueBranches idState
        (caseValueBranches (caseValueBranches (h true false) (h true true)) (dead_typed K)))).symm
    refine e.trans ?_
    rw [ofRegion_id, Category.id_comp]
  have left : ofRegion (seqValueBranches (litLeft_typed y) (genRoute_typed h)) =
      ofRegion (seqValueBranches bitDiscard (h false y)) :=
    (case_inl_arrow (X := Bit) (B := State) (t := litBit y) (litBit_typed y)
      (caseValueBranches (h false false) (h false true))
      (caseValueBranches (caseValueBranches (h true false) (h true true)) (dead_typed K))).trans
      (lit_case y (h false))
  exact split.trans (q_case_congr _ _ (caseValueBranches (h false y) (h false y))
    (caseValueBranches (caseValueBranches (h true false) (h true true)) (dead_typed K))
    ((congrArg (π).map left).trans (q_discard (h false y))) (congrArg (π).map right))

end Route

/-! ## The second step entered with a constant -/

theorem fix_inl (y : Bool) :
    ofRegion (litLeft_typed y) =
      ofRegion (seqValueBranches (ValueBranches.br (ℓ := 0) (L := [Silmaril.coprod Bit State]) rfl
        (.inl (.var (i := 0) rfl)) : ValueBranches [Bit] (.br 0 (.inl (.var 0)) : Region signature.Instr) _)
        (fix_typed y)) := by
  have red := case_inl_arrow (X := Bit) (B := State) (t := (.var 0 : Tm signature.Instr)) (.var (i := 0) rfl)
    (litLeft_typed y) keep_typed
  refine (red.trans ?_).symm
  have e := (ofRegion_comp idBit (litLeft_typed y) (seqValueBranches idBit (litLeft_typed y))).symm
  refine e.trans ?_
  rw [ofRegion_id, Category.id_comp]

theorem fix_inr (y : Bool) :
    ofRegion (ValueBranches.br (ℓ := 0) (L := [Silmaril.coprod Bit State]) rfl
        (.inr (.inl (.var (i := 0) rfl))) :
          ValueBranches [Bit] (.br 0 (.inr (.inl (.var 0))) : Region signature.Instr) _) =
      ofRegion (seqValueBranches (ValueBranches.br (ℓ := 0) (L := [Silmaril.coprod Bit State]) rfl
        (.inr (.inl (.var (i := 0) rfl))) :
          ValueBranches [Bit] (.br 0 (.inr (.inl (.var 0))) : Region signature.Instr) _) (fix_typed y)) := by
  have red := case_inr_arrow (X := Bit) (A := Bit) (B := State) (t := (.inl (.var 0) : Tm signature.Instr))
    (.inl (.var (i := 0) rfl)) (litLeft_typed y) keep_typed
  refine (red.trans ?_).symm
  have e := (ofRegion_comp bitState_typed keep_typed (seqValueBranches bitState_typed keep_typed)).symm
  refine e.trans ?_
  rw [keep_arrow]
  exact (br_inr (.inl (.var rfl))).symm

theorem weakenU {i : Nat} {A : Ty Empty} (h : At [Bit] i A) :
    Tm.BranchValue (Φ := signature.Instr) [Bit, U] (.var i) A := by
  cases i with
  | zero => exact .var h
  | succ i => cases h

theorem shiftU {i : Nat} {A : Ty Empty} (h : At [U] i A) :
    Tm.BranchValue (Φ := signature.Instr) [Bit, U] (.var (i + 1)) A := by
  cases i with
  | zero => exact .var h
  | succ i => cases h

/-- Unit η under the reply binder: a returned constant built on the outer
unit variable is the constant built on literal unit. -/
theorem lit_outer (t : Tm signature.Instr)
    (ht : Tm.BranchValue [U, Bit, U] t (Silmaril.coprod Bit State)) :
    Eqv false [Bit, U] ((Region.br 0 t).substVars (Tm.singleSubst .unit))
      ((Region.br 0 t).substVars (Tm.singleSubst (.var 1))) [Silmaril.coprod Bit State] := by
  have e := Paper.Extension.Eqv.substVars (Δ := [Bit, U]) (θ := fun i => (.var (i + 1) : Tm signature.Instr))
    unit_eta (fun _ _ h => shiftU h)
  exact Paper.Extension.Eqv.lsubstPost (σ := fun _ => .br 0 t) e (.br rfl .unit) (.br rfl (.var rfl))
    (fun ℓ A hA => by
      cases ℓ with
      | zero =>
        cases hA
        exact (ValueBranches.br (ℓ := 0) rfl ht).hasType
      | succ ℓ => cases hA)

/-- The second step entered with the constant `y` is the labelled request
entered with `y`, with its returned payload fixed to `y`. In the quotient. -/
theorem cap_fix (l₂ y : Bool) :
    QLit (seqValueBranches (bit_typed y) (capSecond l₂).typed.packExits) =
      QLit (seqValueBranches (seqValueBranches (bit_typed y) (labelPoll l₂).program.typed.packExits)
        (fix_typed y)) := by
  apply (Paper.Extension.Singleton.ofRegion_eq_iff N _ _).2
  have left := Paper.Eqv.substVars (Δ := [Bit, U]) (θ := fun i => (.var i : Tm signature.Instr))
    ((Paper.TypeCategory.ofRegion_eq_iff _ _).mp (fix_inl y)) (fun _ _ h => weakenU h)
  have right := Paper.Eqv.substVars (Δ := [Bit, U]) (θ := fun i => (.var i : Tm signature.Instr))
    ((Paper.TypeCategory.ofRegion_eq_iff _ _).mp (fix_inr y)) (fun _ _ h => weakenU h)
  have keep : Region.HasType [Bit, U] (.br 0 (.inr (.inl (.var 0))) : Region signature.Instr)
      [Silmaril.coprod Bit State] :=
    (ValueBranches.br (ℓ := 0) rfl (.inr (.inl (.var (i := 0) rfl)))).hasType
  cases y
  · have hop : Tm.HasType [U] (.op (.ask l₂) (.inl (.var 0)) : Tm signature.Instr) (Silmaril.coprod Bit Bit) :=
      .op (.inl (.var (i := 0) rfl))
    have eta := lit_outer (.inl (.inl (.var 0))) (.inl (.inl (.var rfl)))
    exact (Paper.Extension.Eqv.case hop eta.symm (Paper.Extension.Eqv.refl keep)).trans
      (.paper (Paper.Eqv.case hop left right))
  · have hop : Tm.HasType [U] (.op (.ask l₂) (.inr (.var 0)) : Tm signature.Instr) (Silmaril.coprod Bit Bit) :=
      .op (.inr (.var (i := 0) rfl))
    have eta := lit_outer (.inl (.inr (.var 0))) (.inl (.inr (.var rfl)))
    exact (Paper.Extension.Eqv.case hop eta.symm (Paper.Extension.Eqv.refl keep)).trans
      (.paper (Paper.Eqv.case hop left right))

/-! ## The entry state kept across both requests, at a constant entry -/

theorem weakenUU {i : Nat} {A : Ty Empty} (h : At [Bit] i A) :
    Tm.BranchValue (Φ := signature.Instr) [Bit, Bit, U] (.var i) A := by
  cases i with
  | zero => exact .var h
  | succ i => cases h

theorem shiftUU {i : Nat} {A : Ty Empty} (h : At [U] i A) :
    Tm.BranchValue (Φ := signature.Instr) [Bit, Bit, U] (.var (i + 2)) A := by
  cases i with
  | zero => exact .var h
  | succ i => cases h

/-- Unit η under two reply binders. -/
theorem lit_outer₂ (t : Tm signature.Instr)
    (ht : Tm.BranchValue [U, Bit, Bit, U] t (Silmaril.coprod Bit State)) :
    Eqv false [Bit, Bit, U] ((Region.br 0 t).substVars (Tm.singleSubst .unit))
      ((Region.br 0 t).substVars (Tm.singleSubst (.var 2))) [Silmaril.coprod Bit State] := by
  have e := Paper.Extension.Eqv.substVars (Δ := [Bit, Bit, U])
    (θ := fun i => (.var (i + 2) : Tm signature.Instr)) unit_eta (fun _ _ h => shiftUU h)
  exact Paper.Extension.Eqv.lsubstPost (σ := fun _ => .br 0 t) e (.br rfl .unit) (.br rfl (.var rfl))
    (fun ℓ A hA => by
      cases ℓ with
      | zero =>
        cases hA
        exact (ValueBranches.br (ℓ := 0) rfl ht).hasType
      | succ ℓ => cases hA)

/-- The program that keeps its entry state, entered with the constant
`g`, is the two-request program entered with `g` with its returned
payload fixed to `g`. In the quotient. -/
theorem entry_fix (l₁ l₂ g : Bool) :
    QLit (seqValueBranches (bit_typed g) (entryProgram l₁ l₂).typed.packExits) =
      QLit (seqValueBranches (seqValueBranches (bit_typed g) (duoProgram l₁ l₂).typed.packExits)
        (fix_typed g)) := by
  apply (Paper.Extension.Singleton.ofRegion_eq_iff N _ _).2
  have left₂ := Paper.Eqv.substVars (Δ := [Bit, Bit, U]) (θ := fun i => (.var i : Tm signature.Instr))
    ((Paper.TypeCategory.ofRegion_eq_iff _ _).mp (fix_inl g)) (fun _ _ h => weakenUU h)
  have right₂ := Paper.Eqv.substVars (Δ := [Bit, Bit, U]) (θ := fun i => (.var i : Tm signature.Instr))
    ((Paper.TypeCategory.ofRegion_eq_iff _ _).mp (fix_inr g)) (fun _ _ h => weakenUU h)
  have right₁ := Paper.Eqv.substVars (Δ := [Bit, U]) (θ := fun i => (.var i : Tm signature.Instr))
    ((Paper.TypeCategory.ofRegion_eq_iff _ _).mp (fix_inr g)) (fun _ _ h => weakenU h)
  have keep : Region.HasType [Bit, Bit, U] (.br 0 (.inr (.inl (.var 0))) : Region signature.Instr)
      [Silmaril.coprod Bit State] :=
    (ValueBranches.br (ℓ := 0) rfl (.inr (.inl (.var (i := 0) rfl)))).hasType
  have hop₂ : Tm.HasType [Bit, U] (.op (.ask l₂) (.var 0) : Tm signature.Instr) (Silmaril.coprod Bit Bit) :=
    .op (.var (i := 0) rfl)
  cases g
  · have hop₁ : Tm.HasType [U] (.op (.ask l₁) (.inl (.var 0)) : Tm signature.Instr) (Silmaril.coprod Bit Bit) :=
      .op (.inl (.var (i := 0) rfl))
    have eta := lit_outer₂ (.inl (.inl (.var 0))) (.inl (.inl (.var rfl)))
    exact Paper.Extension.Eqv.case hop₁
      ((Paper.Extension.Eqv.case hop₂ eta.symm (Paper.Extension.Eqv.refl keep)).trans
        (.paper (Paper.Eqv.case hop₂ left₂ right₂))) (.paper right₁)
  · have hop₁ : Tm.HasType [U] (.op (.ask l₁) (.inr (.var 0)) : Tm signature.Instr) (Silmaril.coprod Bit Bit) :=
      .op (.inr (.var (i := 0) rfl))
    have eta := lit_outer₂ (.inl (.inr (.var 0))) (.inl (.inr (.var rfl)))
    exact Paper.Extension.Eqv.case hop₁
      ((Paper.Extension.Eqv.case hop₂ eta.symm (Paper.Extension.Eqv.refl keep)).trans
        (.paper (Paper.Eqv.case hop₂ left₂ right₂))) (.paper right₁)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables

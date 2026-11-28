module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Defs
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.CompileTables
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Roundtrip.Thms

/-! # From a factored step to the literal request tree, at loop entries -/

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

/-! ## Dispatchers with equal rows in the quotient -/

theorem q_dispatch_congr {D : Ty Empty} : ∀ (K : Nat) {rows rows' : Fin (K + 1) → Region signature.Instr}
    (h : ∀ i, ValueBranches [State] (rows i) [D]) (h' : ∀ i, ValueBranches [State] (rows' i) [D]),
    (∀ i, QLit (h i) = QLit (h' i)) → QLit (dispatch_typed K h) = QLit (dispatch_typed K h')
  | 0, _, _, _, _, e => e 0
  | K + 1, _, _, h, h', e => by
    have a : QLit (dispatch_typed (K + 1) h) =
        exactCopair N (QLit (h 0)) (QLit (dispatch_typed K fun i => h i.succ)) :=
      (exactCopair_ofRegion N (h 0) (dispatch_typed K fun i => h i.succ)).symm
    have b : QLit (dispatch_typed (K + 1) h') =
        exactCopair N (QLit (h' 0)) (QLit (dispatch_typed K fun i => h' i.succ)) :=
      (exactCopair_ofRegion N (h' 0) (dispatch_typed K fun i => h' i.succ)).symm
    rw [a, b, e 0, q_dispatch_congr K (fun i => h i.succ) (fun i => h' i.succ) (fun i => e i.succ)]

section Rows

variable {K : Nat} {rows rows' : Fin (K + 1) → Region signature.Instr}
  (h : ∀ i, ValueBranches [State] (rows i) [Silmaril.coprod Bit (States K)])
  (h' : ∀ i, ValueBranches [State] (rows' i) [Silmaril.coprod Bit (States K)])

theorem q_loop : QLit (dispatchLoop_typed h) = iterateSum N (QLit (dispatch_typed K h)) :=
  ((iterateSum_map N (ofRegion (dispatch_typed K h))).trans
    (congrArg (π).map (Paper.TypeCategory.iterateSum_ofRegion (dispatch_typed K h)))).symm

theorem q_entered (i : Fin (K + 1)) :
    QLit (dispatchEntered_typed h i) = QLit (entry_typed K i) ≫ QLit (dispatchLoop_typed h) :=
  (congrArg (π).map
    (ofRegion_comp (entry_typed K i) (dispatchLoop_typed h) (dispatchEntered_typed h i)).symm).trans
    ((π).map_comp _ _)

/-- Dispatchers whose rows are equal in the quotient have equal entered
loops. -/
theorem dispatch_rows_eqv (row : ∀ i, QLit (h i) = QLit (h' i)) (i : Fin (K + 1)) :
    Eqv false [State] (dispatchEntered K rows i) (dispatchEntered K rows' i) [Bit] := by
  apply (Paper.Extension.Singleton.ofRegion_eq_iff N (dispatchEntered_typed h i)
    (dispatchEntered_typed h' i)).1
  rw [q_entered h i, q_entered h' i, q_loop h, q_loop h', q_dispatch_congr K h h' row]

end Rows

theorem qlit_congr {D : Ty Empty} {r r' : Region signature.Instr} (e : r = r')
    (h : ValueBranches [State] r [D]) (h' : ValueBranches [State] r' [D]) : QLit h = QLit h' := by
  subst e
  rfl

/-! ## A case on an injected payload, at a one-variable boundary -/

section Reduce

variable {X A B D : Ty Empty} {t : Tm signature.Instr} {l r : Region signature.Instr}

/-- A branch with a left-injected payload followed by a case is the
branch followed by the left arm. An equation of default Paper. -/
theorem case_inl_arrow (ht : Tm.BranchValue [X] t A) (hl : ValueBranches [A] l [D])
    (hr : ValueBranches [B] r [D]) :
    ofRegion (seqValueBranches (ValueBranches.br (ℓ := 0) (L := [Silmaril.coprod A B]) rfl (.inl ht))
        (caseValueBranches hl hr)) =
      ofRegion (seqValueBranches (ValueBranches.br (ℓ := 0) (L := [A]) rfl ht) hl) := by
  have e₁ := (ofRegion_comp (ValueBranches.br (ℓ := 0) (L := [Silmaril.coprod A B]) rfl (.inl ht))
    (caseValueBranches hl hr)
    (seqValueBranches (ValueBranches.br (ℓ := 0) (L := [Silmaril.coprod A B]) rfl (.inl ht))
      (caseValueBranches hl hr))).symm
  have e₂ := (ofRegion_comp (ValueBranches.br (ℓ := 0) (L := [A]) rfl ht) hl
    (seqValueBranches (ValueBranches.br (ℓ := 0) (L := [A]) rfl ht) hl)).symm
  rw [e₁, e₂, br_inl ht, ← coprod_desc_ofRegion hl hr]
  simp

/-- The same for a right-injected payload. -/
theorem case_inr_arrow (ht : Tm.BranchValue [X] t B) (hl : ValueBranches [A] l [D])
    (hr : ValueBranches [B] r [D]) :
    ofRegion (seqValueBranches (ValueBranches.br (ℓ := 0) (L := [Silmaril.coprod A B]) rfl (.inr ht))
        (caseValueBranches hl hr)) =
      ofRegion (seqValueBranches (ValueBranches.br (ℓ := 0) (L := [B]) rfl ht) hr) := by
  have e₁ := (ofRegion_comp (ValueBranches.br (ℓ := 0) (L := [Silmaril.coprod A B]) rfl (.inr ht))
    (caseValueBranches hl hr)
    (seqValueBranches (ValueBranches.br (ℓ := 0) (L := [Silmaril.coprod A B]) rfl (.inr ht))
      (caseValueBranches hl hr))).symm
  have e₂ := (ofRegion_comp (ValueBranches.br (ℓ := 0) (L := [B]) rfl ht) hr
    (seqValueBranches (ValueBranches.br (ℓ := 0) (L := [B]) rfl ht) hr)).symm
  rw [e₁, e₂, br_inr ht, ← coprod_desc_ofRegion hl hr]
  simp

end Reduce

/-! ## The chain followed by the routing, in default Paper -/

theorem bitState_arrow : ofRegion bitState_typed =
    coprod.inl ≫ (sumIso (Φ := signature.Instr) Bit (packedExitType ([] : LCtx (Ty Empty)))).inv :=
  (br_inl (.var rfl)).trans ((congrArg (· ≫ _) (ofRegion_id Bit)).trans (Category.id_comp _))

theorem const_arrow (b : Bool) : ofRegion (const_typed b) =
    ofRegion (r := .br 0 (bitTm b)) (.br rfl (bitTm_typed b)) ≫ ofRegion bitState_typed :=
  (br_inl (bitTm_typed b)).trans
    (congrArg (ofRegion (r := .br 0 (bitTm b)) (.br rfl (bitTm_typed b)) ≫ ·) bitState_arrow.symm)

theorem bitTm_false_arrow : ofRegion (r := .br 0 (bitTm false)) (.br rfl (bitTm_typed false)) =
    coprod.inl ≫ (sumIso (Φ := signature.Instr) Ty.unit Ty.unit).inv :=
  (br_inl (.var rfl)).trans ((congrArg (· ≫ _) (ofRegion_id Ty.unit)).trans (Category.id_comp _))

theorem bitTm_true_arrow : ofRegion (r := .br 0 (bitTm true)) (.br rfl (bitTm_typed true)) =
    coprod.inr ≫ (sumIso (Φ := signature.Instr) Ty.unit Ty.unit).inv :=
  (br_inr (.var rfl)).trans ((congrArg (· ≫ _) (ofRegion_id Ty.unit)).trans (Category.id_comp _))

theorem keep_arrow : ofRegion keep_typed =
    coprod.inr ≫ (sumIso (Φ := signature.Instr) Bit State).inv :=
  (br_inr (.var rfl)).trans ((congrArg (· ≫ _) (ofRegion_id State)).trans (Category.id_comp _))

/-- The chain into `p₂` followed by the routing `a` is the routing whose
return leaves send the request of `p₂`. An equation of default Paper. -/
theorem chain_route (K : Nat) (p₂ : Program) (a : Bool → Bool → Act K) :
    ofRegion (chain_typed p₂) ≫ ofRegion (routerRoute_typed K a) =
      ofRegion (genRoute_typed fun x y => treeRegion_typed K (duoKids K p₂ a x y)) := by
  have row₂ : ofRegion (seqValueBranches bitState_typed (step_typed p₂)) ≫ ofRegion (routerRoute_typed K a) =
      ofRegion bitState_typed ≫ ofRegion (routerRow_typed K p₂ a) := by
    rw [← ofRegion_comp bitState_typed (step_typed p₂) (seqValueBranches bitState_typed (step_typed p₂)),
      Category.assoc, ofRegion_comp (step_typed p₂) (routerRoute_typed K a) (routerRow_typed K p₂ a)]
  have leaf : ∀ b, ofRegion (treeRegion_typed K (duoKids K p₂ a false b)) =
      ofRegion (r := .br 0 (bitTm b)) (.br rfl (bitTm_typed b)) ≫
        ofRegion bitState_typed ≫ ofRegion (routerRow_typed K p₂ a) := fun b =>
    (ask_arrow K b p₂ fun x' y' => .leaf (a x' y')).trans
      ((congrArg (· ≫ ofRegion (routerRow_typed K p₂ a)) (const_arrow b)).trans (Category.assoc _ _ _))
  have left : ofRegion (caseValueBranches (treeRegion_typed K (duoKids K p₂ a false false))
      (treeRegion_typed K (duoKids K p₂ a false true))) =
      ofRegion bitState_typed ≫ ofRegion (routerRow_typed K p₂ a) := by
    rw [← coprod_desc_ofRegion (treeRegion_typed K (duoKids K p₂ a false false))
      (treeRegion_typed K (duoKids K p₂ a false true)), leaf false, leaf true, bitTm_false_arrow,
      bitTm_true_arrow]
    have e : coprod.desc
        ((coprod.inl ≫ (sumIso (Φ := signature.Instr) Ty.unit Ty.unit).inv) ≫
          ofRegion bitState_typed ≫ ofRegion (routerRow_typed K p₂ a))
        ((coprod.inr ≫ (sumIso (Φ := signature.Instr) Ty.unit Ty.unit).inv) ≫
          ofRegion bitState_typed ≫ ofRegion (routerRow_typed K p₂ a)) =
        (sumIso (Φ := signature.Instr) Ty.unit Ty.unit).inv ≫
          ofRegion bitState_typed ≫ ofRegion (routerRow_typed K p₂ a) := by
      apply coprod.hom_ext <;> simp
    rw [e, Iso.hom_inv_id_assoc]
  have keep : ofRegion keep_typed ≫ ofRegion (routerRoute_typed K a) =
      ofRegion (stateSplit_typed K (a true false) (a true true)) := by
    rw [keep_arrow, ← coprod_desc_ofRegion (bitSplit_typed K (a false false) (a false true))
      (stateSplit_typed K (a true false) (a true true))]
    simp
  have rhs : ofRegion (genRoute_typed fun x y => treeRegion_typed K (duoKids K p₂ a x y)) =
      (sumIso (Φ := signature.Instr) Bit State).hom ≫
        coprod.desc
          (ofRegion (caseValueBranches (treeRegion_typed K (duoKids K p₂ a false false))
            (treeRegion_typed K (duoKids K p₂ a false true))))
          (ofRegion (stateSplit_typed K (a true false) (a true true))) :=
    (coprod_desc_ofRegion
      (caseValueBranches (treeRegion_typed K (duoKids K p₂ a false false))
        (treeRegion_typed K (duoKids K p₂ a false true)))
      (stateSplit_typed K (a true false) (a true true))).symm
  rw [← coprod_desc_ofRegion (seqValueBranches bitState_typed (step_typed p₂)) keep_typed, rhs, Category.assoc]
  congr 1
  apply coprod.hom_ext
  · rw [coprod.inl_desc_assoc, coprod.inl_desc, row₂, left]
  · rw [coprod.inr_desc_assoc, coprod.inr_desc, keep]

/-! ## The lift -/

/-- If the written step of `p` factors as the step of `p₁` chained into
`p₂`, the row of `p` equals the row of literal request trees, in the
quotient. -/
theorem duo_row (K : Nat) (p p₁ p₂ : Program) (a : Bool → Bool → Act K) (fac : StepFactors p p₁ p₂) :
    QLit (routerRow_typed K p a) =
      QLit (genRow_typed p₁ fun x y => treeRegion_typed K (duoKids K p₂ a x y)) := by
  have step : (π).map (ofRegion (step_typed p)) = (π).map (ofRegion (chainedStep_typed p₁ p₂)) :=
    (Paper.Extension.Singleton.ofRegion_eq_iff N (step_typed p) (chainedStep_typed p₁ p₂)).2 fac
  have l : ofRegion (routerRow_typed K p a) = ofRegion (step_typed p) ≫ ofRegion (routerRoute_typed K a) :=
    (ofRegion_comp (step_typed p) (routerRoute_typed K a) (routerRow_typed K p a)).symm
  have m : ofRegion (chainedStep_typed p₁ p₂) = ofRegion (step_typed p₁) ≫ ofRegion (chain_typed p₂) :=
    (ofRegion_comp (step_typed p₁) (chain_typed p₂) (chainedStep_typed p₁ p₂)).symm
  have r : ofRegion (genRow_typed p₁ fun x y => treeRegion_typed K (duoKids K p₂ a x y)) =
      ofRegion (step_typed p₁) ≫
        ofRegion (genRoute_typed fun x y => treeRegion_typed K (duoKids K p₂ a x y)) :=
    (ofRegion_comp (step_typed p₁) (genRoute_typed fun x y => treeRegion_typed K (duoKids K p₂ a x y))
      (genRow_typed p₁ fun x y => treeRegion_typed K (duoKids K p₂ a x y))).symm
  calc
    QLit (routerRow_typed K p a) =
        (π).map (ofRegion (step_typed p)) ≫ (π).map (ofRegion (routerRoute_typed K a)) :=
      (congrArg (π).map l).trans ((π).map_comp _ _)
    _ = (π).map (ofRegion (chainedStep_typed p₁ p₂)) ≫ (π).map (ofRegion (routerRoute_typed K a)) := by
      rw [step]
    _ = (π).map ((ofRegion (step_typed p₁) ≫ ofRegion (chain_typed p₂)) ≫
          ofRegion (routerRoute_typed K a)) := by
      rw [← Functor.map_comp, m]
    _ = QLit (genRow_typed p₁ fun x y => treeRegion_typed K (duoKids K p₂ a x y)) := by
      rw [Category.assoc, chain_route, ← r]

variable {K : Nat} (l₁ l₂ : Fin (K + 1) → Bool) (act : Fin (K + 1) → Bool → Bool → Act K)

theorem duoSource_rows (i : Fin (K + 1)) :
    (duoSource l₁ l₂ act).toTable.rows i = genRow (labelPoll (l₁ i)).program
      (fun x y => treeRegion K (duoKids K (labelPoll (l₂ i)).program (act i) x y)) :=
  congrArg (genRow (labelPoll (l₁ i)).program) (funext fun x => funext fun y => by cases x <;> rfl)

/-- If every written step factors, the table of two-request programs
equals the table of literal request trees at every entry. -/
theorem duo_table_eqv
    (fac : ∀ i, StepFactors (duoProgram (l₁ i) (l₂ i)) (labelPoll (l₁ i)).program (labelPoll (l₂ i)).program)
    (j : Fin (K + 1)) :
    Eqv false [State] ((duoRouter l₁ l₂ act).entered j) ((duoSource l₁ l₂ act).entered j) [Bit] :=
  dispatch_rows_eqv (duoRouter l₁ l₂ act).rows_typed (duoSource l₁ l₂ act).toTable.rows_typed
    (fun i => (duo_row K _ _ _ (act i) (fac i)).trans
      (qlit_congr (duoSource_rows l₁ l₂ act i).symm _ _)) j

/-! ## The factoring, in default Paper -/

theorem idBit : ValueBranches [Bit] (.br 0 (.var 0) : Region signature.Instr) [Bit] := .br rfl (.var rfl)

/-- Packing a Bit as a state and unpacking it is the identity, in default Paper. -/
theorem pack_unpack : ofRegion bitState_typed ≫ ofRegion unpack_typed = 𝟙 (ofType (Φ := signature.Instr) Bit) := by
  have native := ValueBranches.unpack_packExits (Φ := signature.Instr) idBit
  have e : ofRegion (seqValueBranches bitState_typed unpack_typed) = ofRegion idBit :=
    (Paper.TypeCategory.ofRegion_eq_iff _ _).mpr (.cfgEta (.native native))
  rw [ofRegion_comp bitState_typed unpack_typed (seqValueBranches bitState_typed unpack_typed), e]
  exact ofRegion_id Bit

theorem chain_inl (p₂ : Program) :
    ofRegion (seqValueBranches (ValueBranches.br (ℓ := 0) (L := [Silmaril.coprod Bit State]) rfl
      (.inl (.var (i := 0) rfl)) : ValueBranches [Bit] (.br 0 (.inl (.var 0)) : Region signature.Instr) _)
      (chain_typed p₂)) = ofRegion p₂.typed.packExits := by
  have red := case_inl_arrow (X := Bit) (B := State) (t := (.var 0 : Tm signature.Instr)) (.var (i := 0) rfl)
    (seqValueBranches bitState_typed (step_typed p₂)) keep_typed
  refine red.trans ?_
  have e₁ := (ofRegion_comp idBit (seqValueBranches bitState_typed (step_typed p₂))
    (seqValueBranches idBit (seqValueBranches bitState_typed (step_typed p₂)))).symm
  have e₂ := (ofRegion_comp bitState_typed (step_typed p₂)
    (seqValueBranches bitState_typed (step_typed p₂))).symm
  have e₃ := (ofRegion_comp unpack_typed p₂.typed.packExits (step_typed p₂)).symm
  refine e₁.trans ?_
  rw [e₂, e₃, ofRegion_id, Category.id_comp, ← Category.assoc, pack_unpack, Category.id_comp]

theorem chain_inr (p₂ : Program) :
    ofRegion (seqValueBranches (ValueBranches.br (ℓ := 0) (L := [Silmaril.coprod Bit State]) rfl
      (.inr (.inl (.var (i := 0) rfl))) :
        ValueBranches [Bit] (.br 0 (.inr (.inl (.var 0))) : Region signature.Instr) _) (chain_typed p₂)) =
      ofRegion (ValueBranches.br (ℓ := 0) (L := [Silmaril.coprod Bit State]) rfl
        (.inr (.inl (.var (i := 0) rfl))) :
          ValueBranches [Bit] (.br 0 (.inr (.inl (.var 0))) : Region signature.Instr) _) := by
  have red := case_inr_arrow (X := Bit) (A := Bit) (B := State) (t := (.inl (.var 0) : Tm signature.Instr))
    (.inl (.var (i := 0) rfl)) (seqValueBranches bitState_typed (step_typed p₂)) keep_typed
  refine red.trans ?_
  have e := (ofRegion_comp bitState_typed keep_typed (seqValueBranches bitState_typed keep_typed)).symm
  refine e.trans ?_
  rw [keep_arrow]
  exact (br_inr (.inl (.var rfl))).symm

theorem weaken {i : Nat} {A : Ty Empty} (h : At [Bit] i A) :
    Tm.BranchValue (Φ := signature.Instr) [Bit, Bit] (.var i) A := by
  cases i with
  | zero => exact .var h
  | succ i => cases h

/-- The packed two-request program is the packed one-request program
followed by the chain, in default Paper. -/
theorem duo_packed (l₁ l₂ : Bool) :
    ofRegion (seqValueBranches (labelPoll l₁).program.typed.packExits (chain_typed (labelPoll l₂).program)) =
      ofRegion (duoProgram l₁ l₂).typed.packExits := by
  have left := Paper.Eqv.substVars (Δ := [Bit, Bit]) (θ := fun i => (.var i : Tm signature.Instr))
    ((Paper.TypeCategory.ofRegion_eq_iff _ _).mp (chain_inl (labelPoll l₂).program)) (fun _ _ h => weaken h)
  have right := Paper.Eqv.substVars (Δ := [Bit, Bit]) (θ := fun i => (.var i : Tm signature.Instr))
    ((Paper.TypeCategory.ofRegion_eq_iff _ _).mp (chain_inr (labelPoll l₂).program)) (fun _ _ h => weaken h)
  have hop : Tm.HasType [Bit] (.op (.ask l₁) (.var 0) : Tm signature.Instr) (Silmaril.coprod Bit Bit) :=
    .op (.var (i := 0) rfl)
  exact (Paper.TypeCategory.ofRegion_eq_iff _ _).mpr (Paper.Eqv.case hop left right)

/-- The written step of the two-request program is the step of its first
request chained into its second, as arrows of default Paper. -/
theorem duo_step_arrow (l₁ l₂ : Bool) :
    ofRegion (step_typed (duoProgram l₁ l₂)) =
      ofRegion (chainedStep_typed (labelPoll l₁).program (labelPoll l₂).program) := by
  have a := (ofRegion_comp unpack_typed (duoProgram l₁ l₂).typed.packExits (step_typed (duoProgram l₁ l₂))).symm
  have b := (ofRegion_comp (step_typed (labelPoll l₁).program) (chain_typed (labelPoll l₂).program)
    (chainedStep_typed (labelPoll l₁).program (labelPoll l₂).program)).symm
  have c := (ofRegion_comp unpack_typed (labelPoll l₁).program.typed.packExits
    (step_typed (labelPoll l₁).program)).symm
  have d := (ofRegion_comp (labelPoll l₁).program.typed.packExits (chain_typed (labelPoll l₂).program)
    (seqValueBranches (labelPoll l₁).program.typed.packExits (chain_typed (labelPoll l₂).program))).symm
  rw [a, b, c, Category.assoc, ← d, duo_packed]

/-- So the factoring hypothesis holds for the two-request program. -/
theorem duo_stepFactors (l₁ l₂ : Bool) :
    StepFactors (duoProgram l₁ l₂) (labelPoll l₁).program (labelPoll l₂).program :=
  (Paper.Extension.Singleton.ofRegion_eq_iff N (step_typed (duoProgram l₁ l₂))
    (chainedStep_typed (labelPoll l₁).program (labelPoll l₂).program)).1
    (congrArg (π).map (duo_step_arrow l₁ l₂))

/-- The row of the two-request program equals the row of literal request
trees, as arrows of default Paper. -/
theorem duo_row_arrow (K : Nat) (l₁ l₂ : Bool) (a : Bool → Bool → Act K) :
    ofRegion (routerRow_typed K (duoProgram l₁ l₂) a) =
      ofRegion (genRow_typed (labelPoll l₁).program
        fun x y => treeRegion_typed K (duoKids K (labelPoll l₂).program a x y)) := by
  have l := (ofRegion_comp (step_typed (duoProgram l₁ l₂)) (routerRoute_typed K a)
    (routerRow_typed K (duoProgram l₁ l₂) a)).symm
  have m := (ofRegion_comp (step_typed (labelPoll l₁).program) (chain_typed (labelPoll l₂).program)
    (chainedStep_typed (labelPoll l₁).program (labelPoll l₂).program)).symm
  have r := (ofRegion_comp (step_typed (labelPoll l₁).program)
    (genRoute_typed fun x y => treeRegion_typed K (duoKids K (labelPoll l₂).program a x y))
    (genRow_typed (labelPoll l₁).program
      fun x y => treeRegion_typed K (duoKids K (labelPoll l₂).program a x y))).symm
  rw [l, duo_step_arrow, m, Category.assoc, chain_route, ← r]

theorem region_arrow_congr {X D : Ty Empty} {r r' : Region signature.Instr} (e : r = r')
    (h : ValueBranches [X] r [D]) (h' : ValueBranches [X] r' [D]) : ofRegion h = ofRegion h' := by
  subst e
  rfl

/-- Dispatchers whose rows are equal arrows have equal entered loops, in
default Paper. -/
theorem dispatch_rows_arrow {K : Nat} {rows rows' : Fin (K + 1) → Region signature.Instr}
    (h : ∀ i, ValueBranches [State] (rows i) [Silmaril.coprod Bit (States K)])
    (h' : ∀ i, ValueBranches [State] (rows' i) [Silmaril.coprod Bit (States K)])
    (row : ∀ i, ofRegion (h i) = ofRegion (h' i)) (i : Fin (K + 1)) :
    ofRegion (dispatchEntered_typed h i) = ofRegion (dispatchEntered_typed h' i) := by
  have d : ofRegion (dispatch_typed K h) = ofRegion (dispatch_typed K h') := by
    apply inj_ext K
    intro j
    rw [inj_dispatch K h j, inj_dispatch K h' j]
    exact row j
  rw [dispatchEntered_arrow h i, dispatchEntered_arrow h' i, dispatchLoop_arrow h, dispatchLoop_arrow h', d]

/-- The table of two-request programs and the table of literal request
trees have the same entered loops, as arrows of default Paper. -/
theorem duo_table_arrow (j : Fin (K + 1)) :
    ofRegion ((duoRouter l₁ l₂ act).entered_typed j) = ofRegion ((duoSource l₁ l₂ act).entered_typed j) :=
  dispatch_rows_arrow (duoRouter l₁ l₂ act).rows_typed (duoSource l₁ l₂ act).toTable.rows_typed
    (fun i => (duo_row_arrow K (l₁ i) (l₂ i) (act i)).trans
      (region_arrow_congr (duoSource_rows l₁ l₂ act i).symm _ _)) j

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables

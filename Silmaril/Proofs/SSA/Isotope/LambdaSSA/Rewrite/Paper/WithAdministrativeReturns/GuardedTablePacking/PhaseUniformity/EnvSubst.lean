module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.EntrySplit
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Environment.Defs

/-! # Written rows with an environment: substitution, the Bit split, and one request -/

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
open Silmaril.DeBruijn (lift)
open Paper.WithAdministrativeReturns.BitFragment.Recursive (Code Normal)

/-! ## Substitution in a schedule -/

theorem packedExitArg_subst (i : Nat) (a : Tm signature.Instr) (θ : Nat → Tm signature.Instr) :
    (packedExitArg i a).subst θ = packedExitArg i (a.subst θ) := by
  induction i with
  | zero => rfl
  | succ i ih => exact congrArg Tm.inr ih

theorem pushTm_subst {n : Nat} (ρ : Fin n → Tm signature.Instr) (θ : Nat → Tm signature.Instr) :
    (fun i => (pushTm ρ i).subst (Tm.liftSubst θ)) = pushTm fun i => (ρ i).subst θ := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · rfl
  · exact (Tm.subst_rename (ρ i) Nat.succ (Tm.liftSubst θ)).trans (Tm.rename_subst (ρ i) θ Nat.succ).symm

/-- Substituting variables in a schedule substitutes in its slot terms. -/
theorem envSem_subst : ∀ {n : Nat} (c : Normal 2 n) (ρ : Fin n → Tm signature.Instr)
    (θ : Nat → Tm signature.Instr), (envSem c ρ).substVars θ = envSem c fun i => (ρ i).subst θ
  | _, .ret e s, ρ, θ => congrArg (Region.br 0) (packedExitArg_subst e.val (ρ s) θ)
  | _, .ask l s left right, ρ, θ => by
    show Region.case (.op (.ask l) ((ρ s).subst θ)) ((envSem left (pushTm ρ)).substVars (Tm.liftSubst θ))
      ((envSem right (pushTm ρ)).substVars (Tm.liftSubst θ)) = _
    rw [envSem_subst left, envSem_subst right, pushTm_subst]
    rfl

theorem bitTm_subst (b : Bool) (θ : Nat → Tm signature.Instr) (h : θ 0 = .var 0) :
    (bitTm b).subst θ = bitTm b := by
  cases b
  · exact congrArg Tm.inl h
  · exact congrArg Tm.inr h

/-- A schedule on constants is fixed by a substitution that fixes variable zero. -/
theorem envSpec_subst {n : Nat} (c : Normal 2 n) (env : Fin n → Bool) (θ : Nat → Tm signature.Instr)
    (h : θ 0 = .var 0) : (envSpec c env).substVars θ = envSpec c env :=
  (envSem_subst c _ θ).trans (congrArg (envSem c) (funext fun i => bitTm_subst (env i) θ h))

theorem envSpec_rename {n : Nat} (c : Normal 2 n) (env : Fin n → Bool) (ρ : Nat → Nat) :
    (envSpec c env).renameVars (lift ρ) = envSpec c env :=
  (Region.renameVars_eq_substVars _ _).trans (envSpec_subst c env _ rfl)

/-! ## The written program is the schedule on its variables -/

theorem pack_lift : Region.liftLSubstVars (fun i => (.br 0 (packedExitArg i (.var 0)) : Region signature.Instr)) =
    fun i => .br 0 (packedExitArg i (.var 0)) := by
  funext i
  show Region.br 0 ((packedExitArg i (.var 0)).rename (lift Nat.succ)) = _
  rw [Tm.rename_eq_subst, packedExitArg_subst]
  rfl

theorem envCode_packed : ∀ {n m : Nat} (c : Normal 2 n) (ρ : Fin n → Fin m),
    ((envCode c).region ρ).packExits = envSem c fun i => .var (ρ i).val
  | _, _, .ret e s, ρ => by
    show Region.br 0 ((packedExitArg e.val (.var 0)).subst (Tm.singleSubst (.var (ρ s).val))) = _
    rw [packedExitArg_subst]
    rfl
  | _, _, .ask l s left right, ρ => by
    show Region.case (.op (.ask l) (.var (ρ s).val))
      (((envCode left).region (Paper.WithAdministrativeReturns.BitFragment.Recursive.push ρ)).lsubst
        (Region.liftLSubstVars fun i => .br 0 (packedExitArg i (.var 0))))
      (((envCode right).region (Paper.WithAdministrativeReturns.BitFragment.Recursive.push ρ)).lsubst
        (Region.liftLSubstVars fun i => .br 0 (packedExitArg i (.var 0)))) = _
    rw [pack_lift]
    have push_eq : (fun i => (.var (Paper.WithAdministrativeReturns.BitFragment.Recursive.push ρ i).val :
        Tm signature.Instr)) = pushTm fun i => .var (ρ i).val := by
      funext i
      refine Fin.cases ?_ (fun i => ?_) i <;> rfl
    have l := envCode_packed left (Paper.WithAdministrativeReturns.BitFragment.Recursive.push ρ)
    have r := envCode_packed right (Paper.WithAdministrativeReturns.BitFragment.Recursive.push ρ)
    rw [push_eq] at l r
    exact congrArg₂ (Region.case _) l r

/-- The packed written row entered with a constant is its schedule on that constant. -/
theorem envCode_const (c : Normal 2 1) (g : Bool) :
    ((Region.br 0 (bitTm g)).lsubst fun _ =>
      (Paper.WithAdministrativeReturns.BitFragment.Recursive.Program.written (envCode c)).packExits.renameVars
        (lift Nat.succ)) = envSpec c fun _ => g := by
  show ((((envCode c).region id).packExits).renameVars (lift Nat.succ)).substVars (Tm.singleSubst (bitTm g)) = _
  rw [envCode_packed, Region.renameVars_eq_substVars, envSem_subst, envSem_subst]
  refine congrArg (envSem c) (funext fun i => ?_)
  have i0 : i = 0 := Fin.eq_zero i
  subst i0
  rfl

/-! ## Typing -/

theorem branchValue_succ {Γ : VCtx (Ty Empty)} {t : Tm signature.Instr} {A B : Ty Empty}
    (h : Tm.BranchValue Γ t A) : Tm.BranchValue (B :: Γ) (t.rename Nat.succ) A := by
  have r := ValueBranches.renameVars (Δ := B :: Γ) (ρ := Nat.succ)
    (ValueBranches.br (ℓ := 0) (L := [A]) rfl h) (fun _ _ hi => hi)
  cases r with
  | br hl ha =>
    cases hl
    exact ha

theorem packed_typed {Γ : VCtx (Ty Empty)} {t : Tm signature.Instr} (e : Fin 2) (h : Tm.BranchValue Γ t Bit) :
    Tm.BranchValue Γ (packedExitArg e.val t) (Silmaril.coprod Bit State) := by
  match e with
  | 0 => exact .inl h
  | 1 => exact .inr (.inl h)

theorem envSem_typed : ∀ {n : Nat} (c : Normal 2 n) {Γ : VCtx (Ty Empty)} (ρ : Fin n → Tm signature.Instr),
    (∀ i, Tm.BranchValue Γ (ρ i) Bit) → ValueBranches Γ (envSem c ρ) [Silmaril.coprod Bit State]
  | _, .ret e s, _, ρ, h => .br rfl (packed_typed e (h s))
  | _, .ask l s left right, _, ρ, h => by
    have push : ∀ i, Tm.BranchValue (Bit :: _) (pushTm ρ i) Bit := fun i => by
      refine Fin.cases ?_ (fun i => ?_) i
      · exact .var rfl
      · exact branchValue_succ (h i)
    exact .case (A := Bit) (B := Bit) (.op (h s).hasType) (envSem_typed left _ push) (envSem_typed right _ push)

theorem envSpec_typed {n : Nat} (c : Normal 2 n) (env : Fin n → Bool) :
    ValueBranches [U] (envSpec c env) [Silmaril.coprod Bit State] :=
  envSem_typed c _ fun i => bitTm_typed (env i)

/-! ## A Bit variable is one of its two constants -/

theorem splitSubst_typed (b : Bool) ⦃i : Nat⦄ ⦃A : Ty Empty⦄ (h : At [Bit, U] i A) :
    Tm.BranchValue [U] (splitSubst b i) A := by
  match i, h with
  | 0, h =>
    cases h
    exact bitTm_typed b
  | 1, h =>
    cases h
    exact .var rfl

/-- Any two unit variables are equal, by unit η. -/
theorem unit_vars {Γ : VCtx (Ty Empty)} {i j : Nat} (hi : At Γ i U) (hj : At Γ j U) :
    Eqv false Γ (.br 0 (.var i) : Region signature.Instr) (.br 0 (.var j)) [U] := by
  have at_i := Paper.Extension.Eqv.substVars (Δ := Γ) (θ := fun _ => (.var i : Tm signature.Instr)) unit_eta
    (fun k A h => by
      cases k with
      | zero =>
        cases h
        exact .var hi
      | succ k => cases h)
  have at_j := Paper.Extension.Eqv.substVars (Δ := Γ) (θ := fun _ => (.var j : Tm signature.Instr)) unit_eta
    (fun k A h => by
      cases k with
      | zero =>
        cases h
        exact .var hj
      | succ k => cases h)
  exact at_i.symm.trans at_j

/-- The Bit as a fresh newest variable. -/
def freshSubst : Nat → Tm signature.Instr
  | 0 => .var 0
  | i + 1 => .var (i + 2)

theorem freshSubst_typed : Tm.Subst.HasType (Φ := signature.Instr) [Bit, U] [Bit, Bit, U] freshSubst :=
    fun i A hi => by
  match i, hi with
  | 0, hi => exact .var hi
  | 1, hi => exact .var hi

def tagTm (b : Bool) (t : Tm signature.Instr) : Tm signature.Instr :=
  match b with
  | false => .inl t
  | true => .inr t

/-- The Bit as a constructor on unit variable one; the old unit variable
as a fresh newest variable. -/
def swapSubst (b : Bool) : Nat → Tm signature.Instr
  | 0 => tagTm b (.var 1)
  | 1 => .var 0
  | i + 2 => .var (i + 4)

theorem swapSubst_typed (b : Bool) :
    Tm.Subst.HasType (Φ := signature.Instr) [Bit, U] [U, U, Bit, U] (swapSubst b) := fun i A hi => by
  match i, hi with
  | 0, hi =>
    cases hi
    cases b
    · exact .inl (.var rfl)
    · exact .inr (.var rfl)
  | 1, hi =>
    cases hi
    exact .var rfl

section BitSplit

variable {D : Ty Empty} {X : Region signature.Instr}

/-- Under the case on the Bit, the constructor arm of the region is the
region on the constant, built on the unit payload of the case. Unit η. -/
theorem split_arm (h : ValueBranches [Bit, U] X [D]) (b : Bool) :
    Eqv false [U, Bit, U] ((X.substVars freshSubst).substVars (Tm.replaceNewest (tagTm b (.var 0))))
      ((X.substVars (splitSubst b)).renameVars (lift Nat.succ)) [D] := by
  have swap := Paper.Extension.Eqv.lsubstPost (σ := fun _ => X.substVars (swapSubst b)) (K := [D])
    (unit_vars (Γ := [U, Bit, U]) (i := 2) (j := 0) rfl rfl) (.br rfl (.var rfl)) (.br rfl (.var rfl))
    (fun ℓ A hA => by
      cases ℓ with
      | zero =>
        cases hA
        exact h.hasType.substVars (swapSubst_typed b)
      | succ ℓ => cases hA)
  have l : (X.substVars (swapSubst b)).substVars (Tm.singleSubst (.var 2)) =
      (X.substVars freshSubst).substVars (Tm.replaceNewest (tagTm b (.var 0))) := by
    rw [Region.substVars_comp, Region.substVars_comp]
    refine congrArg X.substVars (funext fun i => ?_)
    match i with
    | 0 => cases b <;> rfl
    | 1 => rfl
    | i + 2 => rfl
  have r : (X.substVars (swapSubst b)).substVars (Tm.singleSubst (.var 0)) =
      (X.substVars (splitSubst b)).renameVars (lift Nat.succ) := by
    rw [Region.substVars_comp, Region.renameVars_substVars]
    refine congrArg X.substVars (funext fun i => ?_)
    match i with
    | 0 => cases b <;> rfl
    | 1 => rfl
    | i + 2 => rfl
  exact l ▸ r ▸ swap

/-- A region with a Bit variable and a unit variable is the case on the
Bit of the region on each constant. The native case on a variable, then
unit η in each arm. -/
theorem bit_split (h : ValueBranches [Bit, U] X [D]) :
    Eqv false [Bit, U] X (pairSplit (X.substVars (splitSubst false)) (X.substVars (splitSubst true))) [D] := by
  have back : (X.substVars freshSubst).substVars (Tm.singleSubst (.var 0)) = X := by
    rw [Region.substVars_comp]
    have e : (fun i => (freshSubst i).subst (Tm.singleSubst (.var 0))) = (Tm.var : Nat → Tm signature.Instr) := by
      funext i
      cases i <;> rfl
    rw [e, Region.substVars_var]
  have native := SubstitutionEquiv.caseValue (Γ := [Bit, U]) (A := U) (B := U) (L := [D])
    (a := (.var 0 : Tm signature.Instr)) (.var rfl) (h.hasType.substVars freshSubst_typed)
  rw [back] at native
  have cases_eqv := Paper.Extension.Eqv.case (Seed := N) (A := U) (B := U)
    (a := (.var 0 : Tm signature.Instr)) (Γ := [Bit, U]) (.var rfl) (split_arm h false) (split_arm h true)
  exact (Paper.Extension.Eqv.paper (.cfgEta (.native native))).symm.trans cases_eqv

end BitSplit

/-! ## One request -/

theorem deadAny_typed (X : Ty Empty) :
    ValueBranches [Silmaril.empty] (.br 0 (.inl (.inl .unit)) : Region signature.Instr) [Silmaril.coprod Bit X] :=
  .br rfl (.inl (.inl .unit))

section Route

variable {X : Ty Empty} {r : Bool → Bool → Region signature.Instr}

/-- The routing of four results, at any target with a returned Bit. -/
theorem genRouteAny_typed (h : ∀ x y, ValueBranches [U] (r x y) [Silmaril.coprod Bit X]) :
    ValueBranches [Silmaril.coprod Bit State] (genRoute r) [Silmaril.coprod Bit X] :=
  caseValueBranches (caseValueBranches (h false false) (h false true))
    (caseValueBranches (caseValueBranches (h true false) (h true true)) (deadAny_typed X))

theorem genRoute_rename (closed : ∀ x y ρ, (r x y).renameVars (lift ρ) = r x y) (ρ : Nat → Nat) :
    (genRoute r).renameVars (lift ρ) = genRoute r := by
  simp only [genRoute, pairSplit, Region.renameVars, Tm.rename, closed, lift]

theorem brInl_typed : ValueBranches [Bit] (.br 0 (.inl (.var 0)) : Region signature.Instr)
    [Silmaril.coprod Bit State] := .br rfl (.inl (.var rfl))

theorem brInrInl_typed : ValueBranches [Bit] (.br 0 (.inr (.inl (.var 0))) : Region signature.Instr)
    [Silmaril.coprod Bit State] := .br rfl (.inr (.inl (.var rfl)))

/-- A request sent with the constant `q`, whose replies are split into
four one-variable results, is the labelled request followed by the
routing of the results. The equation is of default Paper. -/
theorem ask_skeleton (l q : Bool) (h : ∀ x y, ValueBranches [U] (r x y) [Silmaril.coprod Bit X])
    (closed : ∀ x y ρ, (r x y).renameVars (lift ρ) = r x y)
    (hs : ValueBranches [U] (.case (.op (.ask l) (bitTm q)) (pairSplit (r false false) (r false true))
      (pairSplit (r true false) (r true true)) : Region signature.Instr) [Silmaril.coprod Bit X]) :
    ofRegion hs = ofRegion (seqValueBranches (bit_typed q) (labelPoll l).program.typed.packExits) ≫
      ofRegion (genRouteAny_typed h) := by
  have hl := caseValueBranches (h false false) (h false true)
  have hr := caseValueBranches (h true false) (h true true)
  have left₁ : ofRegion (seqValueBranches brInl_typed (genRouteAny_typed h)) = ofRegion hl :=
    (case_inl_arrow (X := Bit) (B := State) (t := (.var 0 : Tm signature.Instr)) (.var (i := 0) rfl) hl
      (caseValueBranches hr (deadAny_typed X))).trans
      ((ofRegion_comp idBit hl (seqValueBranches idBit hl)).symm.trans (by rw [ofRegion_id, Category.id_comp]))
  have right₁ : ofRegion (seqValueBranches brInrInl_typed (genRouteAny_typed h)) = ofRegion hr :=
    (case_inr_arrow (X := Bit) (A := Bit) (B := State) (t := (.inl (.var 0) : Tm signature.Instr))
      (.inl (.var (i := 0) rfl)) hl (caseValueBranches hr (deadAny_typed X))).trans
      ((case_inl_arrow (X := Bit) (B := Silmaril.empty) (t := (.var 0 : Tm signature.Instr)) (.var (i := 0) rfl)
        hr (deadAny_typed X)).trans
        ((ofRegion_comp idBit hr (seqValueBranches idBit hr)).symm.trans (by rw [ofRegion_id, Category.id_comp])))
  have left := Paper.Eqv.substVars (Δ := [Bit, U]) (θ := fun i => (.var i : Tm signature.Instr))
    ((Paper.TypeCategory.ofRegion_eq_iff _ _).mp left₁) (fun _ _ h => weakenU h)
  have right := Paper.Eqv.substVars (Δ := [Bit, U]) (θ := fun i => (.var i : Tm signature.Instr))
    ((Paper.TypeCategory.ofRegion_eq_iff _ _).mp right₁) (fun _ _ h => weakenU h)
  have hop : Tm.HasType [U] (.op (.ask l) (bitTm q) : Tm signature.Instr) (Silmaril.coprod Bit Bit) :=
    .op (bitTm_typed q).hasType
  have key := Paper.Eqv.case hop left right
  have cl := genRoute_rename closed Nat.succ
  rw [show (fun i => (.var i : Tm signature.Instr)) = Tm.var from rfl] at key
  simp only [Region.substVars_var] at key
  have e : ofRegion hs = ofRegion (seqValueBranches (seqValueBranches (bit_typed q)
      (labelPoll l).program.typed.packExits) (genRouteAny_typed h)) := by
    apply (Paper.TypeCategory.ofRegion_eq_iff _ _).mpr
    show Paper.Eqv [U] _ (Region.case (.op (.ask l) (bitTm q))
      ((((genRoute r).renameVars (lift Nat.succ)).renameVars (lift Nat.succ)).substVars
        (Tm.singleSubst (.inl (.var 0))))
      ((((genRoute r).renameVars (lift Nat.succ)).renameVars (lift Nat.succ)).substVars
        (Tm.singleSubst (.inr (.inl (.var 0)))))) _
    rw [cl, cl]
    have key' : Paper.Eqv [U] (Region.case (.op (.ask l) (bitTm q))
        ((genRoute r).substVars (Tm.singleSubst (.inl (.var 0))))
        ((genRoute r).substVars (Tm.singleSubst (.inr (.inl (.var 0))))))
        (Region.case (.op (.ask l) (bitTm q)) (pairSplit (r false false) (r false true))
          (pairSplit (r true false) (r true true))) [Silmaril.coprod Bit X] := by
      rw [← cl]
      exact key
    exact key'.symm
  exact e.trans (ofRegion_comp (seqValueBranches (bit_typed q) (labelPoll l).program.typed.packExits)
    (genRouteAny_typed h) _).symm

end Route

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables

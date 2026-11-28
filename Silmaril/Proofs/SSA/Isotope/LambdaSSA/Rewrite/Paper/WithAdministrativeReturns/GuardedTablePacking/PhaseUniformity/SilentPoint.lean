module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Silent.Defs
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.EntryPoint
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.SilentTables

/-! # Landings are determined in the request-prefix model -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.TableModel

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.WithAdministrativeReturns
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open Paper.WithCaseBind.BitQuery (signature Trace model modelCoherent Event)
open Paper.WithCaseBind.BitQuery.RequestTree
open Paper.Extension.Singleton (ofRegion ofType sumCofan)
open Paper.Extension.Singleton.ValueCoproducts (exactCopair)
open Paper.Extension.Singleton.Generation (exactCopair_ofRegion)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli (value instructions)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit bit)
open Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Silmaril.Semantics.NondeterministicTrace (Tagged)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.BitLoop

local notation "J" => _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli.J (m := Trace)
local notation "M" => _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli.types
local notation "PEqv" => WithGuardedTablePacking.WithPhaseUniformity.Eqv
local notation "N" => WithGuardedTablePacking.Step (τ := Ty Empty) (Φ := signature.Instr) false
local notation "Lit" => ofRegion N
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop.Prefix
open Paper.WithCaseBind.BitQuery (request)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Answer)

set_option backward.isDefEq.respectTransparency false

section Landing

noncomputable local instance landingInstructions : InstructionModel J M signature.Instr :=
  instructions prefixModel
local instance landingCoherent : RegionTypingCoherent (Φ := signature.Instr) J M := prefixCoherent

/-- A returned constant runs to that constant with no event. -/
theorem ret_denote {r : Region signature.Instr} (c : Bool) (h : ValueBranches [Ty.unit] r [Bit])
    (e : r = .br 0 (bitTm c)) (u : value Ty.unit) :
    (denoteSingletonRegion J M h.hasType).of u = (pure (bit c) : Trace (value Bit)) := by
  subst e
  have run := RouterRun.bitTm_run c u
  rw [RouterRun.lit_run (brOf (bitTm_typed c))] at run
  exact run

/-! ## The canonical silent self-loop has no observation -/

/-- A step of the canonical silent self-loop repeats with no event. -/
theorem spin_step (g : Bool) :
    spinRouter.prefixStepM (Sum.inl (bit g)) =
      (pure (actVal 0 (.go 0 false)) : Trace (value Bit ⊕ value (States 0))) := by
  have u : value Ty.unit := ()
  have row : PEqv false [Ty.unit] (constEntry g (spinRouter.rows 0)) (.br 0 (actTm 0 (.go 0 false)))
      [Silmaril.coprod Bit (States 0)] :=
    .paper ((Paper.TypeCategory.ofRegion_eq_iff (constEntry_typed g (spinRouter.rows_typed 0))
      (act_typed 0 (.go 0 false))).mp (Tables.pure_const 0 0 (fun _ _ => .go 0 false) g))
  have d := congrArg
    (fun k : (J).obj ((M).obj Ty.unit) ⟶ (J).obj ((M).obj (Silmaril.coprod Bit (States 0))) => k.of u)
    (valid_denote (constEntry_typed g (spinRouter.rows_typed 0)) (act_typed 0 (.go 0 false))
      (WithGuardedTablePacking.WithPhaseUniformity.valid_of_eqv false row _ _))
  have run := RouterRun.act_run 0 (.go 0 false) u
  rw [RouterRun.lit_run (act_typed 0 (.go 0 false))] at run
  exact (const_denote (spinRouter.rows_typed 0) g u).symm.trans (d.trans run)

/-- In the request-prefix model the canonical silent self-loop has no
observation: no completed run and no pending request. -/
theorem spin_obs (g : Bool) : spinRouter.prefixObservations 0 g = ∅ := by
  rw [prefix_obs_eq]
  apply Set.eq_empty_of_subset_empty
  have step : ∀ a : value (States 0), spinRouter.prefixStepM a =
      (pure (actVal 0 (.go 0 false)) : Trace (value Bit ⊕ value (States 0))) := fun a => by
    rcases a with b | e
    · rcases b with u | u
      · exact spin_step false
      · exact spin_step true
    · exact e.elim
  refine iter_induction spinRouter.prefixStepM (fun _ => ∅) (fun a t w h => ?_) (fun a b w h => ?_)
    (fun a next u r v _ h => h.elim) _
  · rw [step a] at h
    exact absurd (BitLoop.mem_pure.1 h).1 (by simp)
  · rw [step a] at h
    have e := Except.ok.inj (BitLoop.mem_pure.1 h).1
    cases e

theorem spin_denote (u : value Ty.unit) :
    ((denoteSingletonRegion J M spinRegion_typed.hasType).of u).outcomes = ∅ :=
  (congrArg Tagged.outcomes (const_denote (spinRouter.entered_typed 0) false u)).trans (spin_obs false)

variable {K K' : Nat}

/-- The observations of literal request trees entered with a constant
contain a pending request and show that constant. -/
theorem ltable_obs (t : LTable K) (x : Fin (K + 1)) (q : Bool) :
    ∃ (N' : Nat) (label : Fin (N' + 1) → Bool) (act : Fin (N' + 1) → Bool → Bool → Act N') (y : Fin (N' + 1)),
      ((denoteSingletonRegion J M (t.entered_typed x).hasType).of (Sum.inl (bit q))).outcomes =
        (Router.ofLabels label act).prefixObservations y q := by
  obtain ⟨N', label, act, e, E⟩ := t.exists_router
  have d := valid_denote (t.entered_typed x) ((Router.ofLabels label act).entered_typed (e x))
    (WithGuardedTablePacking.WithPhaseUniformity.valid_of_eqv false (E x) _ _)
  exact ⟨N', label, act, e x, by
    unfold Router.prefixObservations
    rw [← d]⟩

theorem ret_ne_spin (c : Bool) (u : value Ty.unit)
    (h : (pure (bit c) : Trace (value Bit)) =
      (denoteSingletonRegion J M spinRegion_typed.hasType).of u) : False := by
  have mem : (Except.ok (bit c), (1 : Word)) ∈ (pure (bit c) : Trace (value Bit)).outcomes :=
    BitLoop.mem_pure.2 ⟨rfl, rfl⟩
  rw [h, spin_denote u] at mem
  exact mem

theorem at_ne_spin (t : LTable K) (x : Fin (K + 1)) (q : Bool) (u : value Ty.unit)
    (h : (denoteSingletonRegion J M (Landing.region_typed (.at t x q)).hasType).of u =
      (denoteSingletonRegion J M spinRegion_typed.hasType).of u) : False := by
  obtain ⟨_, label, act, y, obs⟩ := ltable_obs t x q
  have pending := prefix_pending label act y q
  rw [← obs, ← const_denote (t.entered_typed x) q u] at pending
  have h' : ((denoteSingletonRegion J M (Landing.region_typed (.at t x q)).hasType).of u).outcomes = ∅ :=
    (congrArg Tagged.outcomes h).trans (spin_denote u)
  rw [h'] at pending
  exact pending

/-- Landings with the same run agree. -/
theorem landing_rel (L : Landing K) (L' : Landing K') (u : value Ty.unit)
    (h : (denoteSingletonRegion J M (Landing.region_typed L).hasType).of u =
      (denoteSingletonRegion J M (Landing.region_typed L').hasType).of u) : L.Rel L' := by
  cases L with
  | ret c =>
    cases L' with
    | ret c' =>
      have run : (pure (bit c) : Trace (value Bit)) = pure (bit c') :=
        (ret_denote c (Landing.region_typed (.ret c : Landing K)) rfl u).symm.trans
          (h.trans (ret_denote c' (Landing.region_typed (.ret c' : Landing K')) rfl u))
      have mem : (Except.ok (bit c), (1 : Word)) ∈ (pure (bit c') : Trace (value Bit)).outcomes :=
        run ▸ BitLoop.mem_pure.2 ⟨rfl, rfl⟩
      exact bit_inj (Except.ok.inj (BitLoop.mem_pure.1 mem).1)
    | «at» t' x' q' =>
      obtain ⟨_, label, act, y, obs⟩ := ltable_obs t' x' q'
      have pending := prefix_pending label act y q'
      rw [← obs, ← const_denote (t'.entered_typed x') q' u] at pending
      have h' : (denoteSingletonRegion J M (Landing.region_typed (.at t' x' q')).hasType).of u =
          (pure (bit c) : Trace (value Bit)) :=
        h.symm.trans (ret_denote c (Landing.region_typed (.ret c : Landing K)) rfl u)
      rw [h'] at pending
      exact absurd (BitLoop.mem_pure.1 pending).1 (by simp)
    | spin =>
      exact (ret_ne_spin c u ((ret_denote c (Landing.region_typed (.ret c : Landing K)) rfl u).symm.trans h)).elim
  | «at» t x q =>
    cases L' with
    | ret c' =>
      obtain ⟨_, label, act, y, obs⟩ := ltable_obs t x q
      have pending := prefix_pending label act y q
      rw [← obs, ← const_denote (t.entered_typed x) q u] at pending
      have h' : (denoteSingletonRegion J M (Landing.region_typed (.at t x q)).hasType).of u =
          (pure (bit c') : Trace (value Bit)) :=
        h.trans (ret_denote c' (Landing.region_typed (.ret c' : Landing K')) rfl u)
      rw [h'] at pending
      exact absurd (BitLoop.mem_pure.1 pending).1 (by simp)
    | «at» t' x' q' =>
      have run : (denoteSingletonRegion J M (t.entered_typed x).hasType).of (Sum.inl (bit q)) =
          (denoteSingletonRegion J M (t'.entered_typed x').hasType).of (Sum.inl (bit q')) :=
        (const_denote (t.entered_typed x) q u).symm.trans (h.trans (const_denote (t'.entered_typed x') q' u))
      obtain ⟨_, label, act, y, obs⟩ := ltable_obs t x q
      obtain ⟨_, label', act', y', obs'⟩ := ltable_obs t' x' q'
      have same : q = q' :=
        prefix_query label act label' act' y y' q q' (obs.symm.trans ((congrArg Tagged.outcomes run).trans obs'))
      subst same
      exact ⟨rfl, ltable_point t t' x x' q (congrArg Tagged.outcomes run)⟩
    | spin => exact (at_ne_spin t x q u h).elim
  | spin =>
    cases L' with
    | ret c' =>
      exact (ret_ne_spin c' u
        ((ret_denote c' (Landing.region_typed (.ret c' : Landing K')) rfl u).symm.trans h.symm)).elim
    | «at» t' x' q' => exact (at_ne_spin t' x' q' u h.symm).elim
    | spin => exact True.intro

variable {r r' : Region signature.Instr} {L : Bool → Landing K} {L' : Bool → Landing K'}

/-- Valid loops have agreeing landings at each constant. -/
theorem landed_rel (h : ValueBranches [State] r [Bit]) (h' : ValueBranches [State] r' [Bit])
    (hl : Landed r L) (hl' : Landed r' L')
    (v : WithGuardedTablePacking.Valid h.hasType h'.hasType) (q : Bool) : (L q).Rel (L' q) := by
  have u : value Ty.unit := ()
  have a := congrArg (fun k : (J).obj ((M).obj Ty.unit) ⟶ (J).obj ((M).obj Bit) => k.of u)
    (valid_denote (constEntry_typed q h) (Landing.region_typed (L q))
      (WithGuardedTablePacking.WithPhaseUniformity.valid_of_eqv false (hl q) _ _))
  have a' := congrArg (fun k : (J).obj ((M).obj Ty.unit) ⟶ (J).obj ((M).obj Bit) => k.of u)
    (valid_denote (constEntry_typed q h') (Landing.region_typed (L' q))
      (WithGuardedTablePacking.WithPhaseUniformity.valid_of_eqv false (hl' q) _ _))
  have m := congrArg (fun k : (J).obj ((M).obj State) ⟶ (J).obj ((M).obj Bit) => k.of (Sum.inl (bit q)))
    (valid_denote h h' v)
  exact landing_rel (L q) (L' q) u
    (a.symm.trans ((const_denote h q u).trans (m.trans ((const_denote h' q u).symm.trans a'))))

end Landing

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.TableModel

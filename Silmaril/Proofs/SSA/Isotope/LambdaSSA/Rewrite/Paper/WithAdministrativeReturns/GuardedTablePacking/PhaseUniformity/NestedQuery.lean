module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.NestedTables

/-! # Landings in tidy router tables are determined in the query-aware model -/

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

noncomputable local instance slandingInstructions : InstructionModel J M signature.Instr :=
  instructions queryModel
local instance slandingCoherent : RegionTypingCoherent (Φ := signature.Instr) J M := queryCoherent

theorem q_ret_denote {r : Region signature.Instr} (c : Bool) (h : ValueBranches [Ty.unit] r [Bit])
    (e : r = .br 0 (bitTm c)) (u : value Ty.unit) :
    (denoteSingletonRegion J M h.hasType).of u = (pure (bit c) : Trace (value Bit)) := by
  subst e
  have run := RouterRun.bitTm_run c u
  rw [RouterRun.lit_run (brOf (bitTm_typed c))] at run
  exact run

theorem at_obs {K : Nat} (label : Fin (K + 1) → Option Bool) (act : Fin (K + 1) → Bool → Bool → Act K)
    (x : Fin (K + 1)) (q : Bool) (u : value Ty.unit) :
    ((denoteSingletonRegion J M (SLanding.region_typed (.at label act x q)).hasType).of u).outcomes =
      (Router.ofSpin label act).queryObservations x q :=
  congrArg Tagged.outcomes (q_const_denote ((Router.ofSpin label act).entered_typed x) q u)

theorem ret_ne_at {K : Nat} (c : Bool) (label : Fin (K + 1) → Option Bool)
    (act : Fin (K + 1) → Bool → Bool → Act K) (x : Fin (K + 1)) (q : Bool) (u : value Ty.unit)
    (h : (pure (bit c) : Trace (value Bit)) =
      (denoteSingletonRegion J M (SLanding.region_typed (.at label act x q)).hasType).of u) : False := by
  have mem : (Except.ok (bit c), (1 : Word)) ∈ (pure (bit c) : Trace (value Bit)).outcomes :=
    BitLoop.mem_pure.2 ⟨rfl, rfl⟩
  rw [h, at_obs label act x q u] at mem
  exact query_no_one label act x q _ mem

/-- Tidy landings with the same run in the query-aware model are equal. -/
theorem slanding_eqv (L L' : SLanding) (ht : L.Tidy) (ht' : L'.Tidy) (u : value Ty.unit)
    (h : (denoteSingletonRegion J M (SLanding.region_typed L).hasType).of u =
      (denoteSingletonRegion J M (SLanding.region_typed L').hasType).of u) :
    PEqv false [Ty.unit] L.region L'.region [Bit] := by
  cases L with
  | ret c =>
    cases L' with
    | ret c' =>
      have run : (pure (bit c) : Trace (value Bit)) = pure (bit c') :=
        (q_ret_denote c (SLanding.region_typed (.ret c)) rfl u).symm.trans
          (h.trans (q_ret_denote c' (SLanding.region_typed (.ret c')) rfl u))
      have mem : (Except.ok (bit c), (1 : Word)) ∈ (pure (bit c') : Trace (value Bit)).outcomes :=
        run ▸ BitLoop.mem_pure.2 ⟨rfl, rfl⟩
      have e : c = c' := bit_inj (Except.ok.inj (BitLoop.mem_pure.1 mem).1)
      subst e
      exact Paper.Extension.Eqv.refl (SLanding.region_typed (.ret c)).hasType
    | «at» label' act' x' q' =>
      exact (ret_ne_at c label' act' x' q' u
        ((q_ret_denote c (SLanding.region_typed (.ret c)) rfl u).symm.trans h)).elim
  | «at» label act x q =>
    cases L' with
    | ret c' =>
      exact (ret_ne_at c' label act x q u
        ((q_ret_denote c' (SLanding.region_typed (.ret c')) rfl u).symm.trans h.symm)).elim
    | «at» label' act' x' q' =>
      have o : (Router.ofSpin label act).queryObservations x q =
          (Router.ofSpin label' act').queryObservations x' q' :=
        (at_obs label act x q u).symm.trans ((congrArg Tagged.outcomes h).trans (at_obs label' act' x' q' u))
      cases hl : label x with
      | none =>
        have hl' : label' x' = none := query_kind label' act' label act x' x q' q o.symm hl
        have empty : (Router.ofSpin label act).queryObservations x false =
            (Router.ofSpin label' act').queryObservations x' false :=
          (query_empty label act x hl false).trans (query_empty label' act' x' hl' false).symm
        exact (Tables.spin_entry_bit_eqv label act x hl q).trans
          ((Tables.const_congr ((Router.ofSpin label act).entered_typed x)
            ((Router.ofSpin label' act').entered_typed x')
            (query_eqv_of_obs label act label' act' ht ht' x x' false empty) false).trans
            (Tables.spin_entry_bit_eqv label' act' x' hl' q').symm)
      | some l =>
        cases hl' : label' x' with
        | none =>
          have bad := query_kind label act label' act' x x' q q' o hl'
          rw [hl] at bad
          cases bad
        | some l' =>
          have e : q = q' := (query_label_query label act label' act' x x' hl hl' q q' o).2
          subst e
          exact Tables.const_congr ((Router.ofSpin label act).entered_typed x)
            ((Router.ofSpin label' act').entered_typed x')
            (query_eqv_of_obs label act label' act' ht ht' x x' q o) q

variable {r r' : Region signature.Instr} {L L' : Bool → SLanding}

/-- Valid loops have equal landings at each constant. -/
theorem slanded_point (h : ValueBranches [State] r [Bit]) (h' : ValueBranches [State] r' [Bit])
    (hl : SLanded r L) (hl' : SLanded r' L') (ht : ∀ q, (L q).Tidy) (ht' : ∀ q, (L' q).Tidy)
    (v : WithGuardedTablePacking.Valid h.hasType h'.hasType) (q : Bool) :
    PEqv false [Ty.unit] (L q).region (L' q).region [Bit] := by
  have u : value Ty.unit := ()
  have a := congrArg (fun k : (J).obj ((M).obj Ty.unit) ⟶ (J).obj ((M).obj Bit) => k.of u)
    (q_valid_denote (constEntry_typed q h) (SLanding.region_typed (L q))
      (WithGuardedTablePacking.WithPhaseUniformity.valid_of_eqv false (hl q) _ _))
  have a' := congrArg (fun k : (J).obj ((M).obj Ty.unit) ⟶ (J).obj ((M).obj Bit) => k.of u)
    (q_valid_denote (constEntry_typed q h') (SLanding.region_typed (L' q))
      (WithGuardedTablePacking.WithPhaseUniformity.valid_of_eqv false (hl' q) _ _))
  have m := congrArg (fun k : (J).obj ((M).obj State) ⟶ (J).obj ((M).obj Bit) => k.of (Sum.inl (bit q)))
    (q_valid_denote h h' v)
  exact slanding_eqv (L q) (L' q) (ht q) (ht' q) u
    (a.symm.trans ((q_const_denote h q u).trans (m.trans ((q_const_denote h' q u).symm.trans a'))))

/-- Tidy tables with silent rows at each constant: equal loops have
bisimilar tables. -/
theorem query_pointed_bisim {K K' : Nat} {label : Fin (K + 1) → Option Bool}
    {act : Fin (K + 1) → Bool → Bool → Act K} {label' : Fin (K' + 1) → Option Bool}
    {act' : Fin (K' + 1) → Bool → Bool → Act K'} {x : Bool → Fin (K + 1)} {x' : Bool → Fin (K' + 1)}
    (ht : Tidy label act) (ht' : Tidy label' act') (h : ValueBranches [State] r [Bit])
    (h' : ValueBranches [State] r' [Bit]) (hp : SpinPointed r label act x) (hp' : SpinPointed r' label' act' x')
    (e : PEqv false [State] r r' [Bit]) (q : Bool) :
    ∃ R, Router.Bisimulation (Router.ofSpin label act) (Router.ofSpin label' act') R ∧ R (x q) (x' q) :=
  ⟨_, query_bisim label act label' act' ht ht', q, query_pointed_obs h h' hp hp'
    (WithGuardedTablePacking.WithPhaseUniformity.valid_of_eqv false e _ _) q⟩

end Landing

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.TableModel

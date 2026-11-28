module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.SpinTables
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.QueryPrefix

/-! # Completeness for tidy tables with silent rows, by the query-aware model -/

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
open Paper.WithAdministrativeReturns.WithGuardedTablePacking (Valid)
open Paper.WithCaseBind.BitQuery.RequestTree (Word event)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli (value)

section Complete

variable {M M' : Nat} {label : Fin (M + 1) → Option Bool} {act : Fin (M + 1) → Bool → Bool → Act M}
  {label' : Fin (M' + 1) → Option Bool} {act' : Fin (M' + 1) → Bool → Bool → Act M'}
  {r r' : Region signature.Instr} {x : Bool → Fin (M + 1)} {x' : Bool → Fin (M' + 1)}
  (ht : Tidy label act) (ht' : Tidy label' act')

include ht ht' in
/-- Tidy tables with silent rows: the loops are equal exactly when they
are valid in every supported model. No row has to be sighted. -/
theorem tidy_pointed_complete (h : ValueBranches [State] r [Bit]) (h' : ValueBranches [State] r' [Bit])
    (hp : SpinPointed r label act x) (hp' : SpinPointed r' label' act' x') :
    Eqv false [State] r r' [Bit] ↔ Valid h.hasType h'.hasType :=
  ⟨fun e => Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.valid_of_eqv false e _ _,
    fun v => spin_pointed_eqv h h' hp hp' fun q =>
      TableModel.query_eqv_of_obs label act label' act' ht ht' (x q) (x' q) q
        (TableModel.query_pointed_obs h h' hp hp' v q)⟩

include ht ht' in
/-- Tidy tables with silent rows have equal entered loops exactly when
their observations in the query-aware model are equal. -/
theorem tidy_eqv_iff_query (i : Fin (M + 1)) (i' : Fin (M' + 1)) :
    Eqv false [State] ((Router.ofSpin label act).entered i) ((Router.ofSpin label' act').entered i') [Bit] ↔
      (Router.ofSpin label act).queryObservations i false =
        (Router.ofSpin label' act').queryObservations i' false :=
  ⟨fun e => TableModel.query_obs_of_valid
      (Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.valid_of_eqv false e _ _) false,
    fun h => TableModel.query_eqv_of_obs label act label' act' ht ht' i i' false h⟩

include ht ht' in
/-- And exactly when they are valid in every supported model. -/
theorem tidy_eqv_iff_valid (i : Fin (M + 1)) (i' : Fin (M' + 1)) :
    Eqv false [State] ((Router.ofSpin label act).entered i) ((Router.ofSpin label' act').entered i') [Bit] ↔
      Valid ((Router.ofSpin label act).entered_typed i).hasType
        ((Router.ofSpin label' act').entered_typed i').hasType :=
  ⟨fun e => Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.valid_of_eqv false e _ _,
    fun v => TableModel.query_eqv_of_obs label act label' act' ht ht' i i' false
      (TableModel.query_obs_of_valid v false)⟩

include ht ht' in
theorem tidy_bisim_of_eqv (i : Fin (M + 1)) (i' : Fin (M' + 1))
    (e : Eqv false [State] ((Router.ofSpin label act).entered i) ((Router.ofSpin label' act').entered i') [Bit]) :
    ∃ R, Router.Bisimulation (Router.ofSpin label act) (Router.ofSpin label' act') R ∧ R i i' :=
  ⟨_, TableModel.query_bisim label act label' act' ht ht', false, (tidy_eqv_iff_query ht ht' i i').1 e⟩

end Complete

/-! ## Regression: a blind request -/

theorem blind_tidy (m l s : Bool) : Tidy (blindLabel m l) (blindAct s) := fun i l' hi tag pl j q ha hj => by
  match i with
  | 0 =>
    cases ha
    cases hj
  | 1 =>
    cases ha
    rfl
  | 2 => cases hi

theorem blind_row (m l s : Bool) (tag pl : Bool) :
    ∃ j q, blindAct s 1 tag pl = .go j q ∧ blindLabel m l j = none :=
  ⟨2, false, rfl, rfl⟩

/-- The request-prefix model does not see the query of the blind request:
the two tables have the same observations there. -/
theorem blind_prefix_obs (m l s s' g : Bool) :
    (Router.ofSpin (blindLabel m l) (blindAct s)).prefixObservations 0 g =
      (Router.ofSpin (blindLabel m l) (blindAct s')).prefixObservations 0 g := by
  have inner : ∀ t q, (Router.ofSpin (blindLabel m l) (blindAct t)).prefixObservations 1 q =
      {(Except.error l, 1)} := fun t q =>
    TableModel.blind_obs (blindLabel m l) (blindAct t) 1 rfl (blind_row m l t) q
  ext ⟨r, w⟩
  rw [TableModel.spin_unfold (blindLabel m l) (blindAct s) 0 rfl g r w,
    TableModel.spin_unfold (blindLabel m l) (blindAct s') 0 rfl g r w]
  have cont : ∀ t v, (Router.ofSpin (blindLabel m l) (blindAct t)).PrefixCont (.go 1 t) r v ↔
      (r, v) = (Except.error l, (1 : Word)) := fun t v => by
    show (r, v) ∈ (Router.ofSpin (blindLabel m l) (blindAct t)).prefixObservations 1 t ↔ _
    rw [inner t t]
    exact Set.mem_singleton_iff
  constructor
  · rintro (h | ⟨tag, pl, v, e, hc⟩)
    · exact .inl h
    · exact .inr ⟨tag, pl, v, e, (cont s' v).2 ((cont s v).1 hc)⟩
  · rintro (h | ⟨tag, pl, v, e, hc⟩)
    · exact .inl h
    · exact .inr ⟨tag, pl, v, e, (cont s v).2 ((cont s' v).1 hc)⟩

/-- The query-aware model does: the blind request shows its query. -/
theorem blind_query_obs (m l s g : Bool) :
    (Router.ofSpin (blindLabel m l) (blindAct s)).queryObservations 1 g = {(Except.error l, pendingWord l g)} :=
  TableModel.query_blind (blindLabel m l) (blindAct s) 1 rfl (blind_row m l s) g

/-- The same blind request with different queries: the loops are equal
exactly when the queries are. -/
theorem blind_eqv_iff (m l s s' : Bool) :
    Eqv false [State] ((Router.ofSpin (blindLabel m l) (blindAct s)).entered 0)
      ((Router.ofSpin (blindLabel m l) (blindAct s')).entered 0) [Bit] ↔ s = s' := by
  constructor
  · intro e
    obtain ⟨R, bis, r⟩ := tidy_bisim_of_eqv (blind_tidy m l s) (blind_tidy m l s') 0 0 e
    exact And.left (bis.act 0 0 r false false)
  · rintro rfl
    exact Paper.Extension.Eqv.refl ((Router.ofSpin (blindLabel m l) (blindAct s)).entered_typed 0).hasType

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables

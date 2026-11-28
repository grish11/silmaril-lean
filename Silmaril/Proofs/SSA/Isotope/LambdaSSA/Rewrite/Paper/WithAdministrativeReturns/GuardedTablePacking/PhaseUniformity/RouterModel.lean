module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.RouterTables
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.SwitchReflection

/-! # Router tables in the four-reply interpreter -/

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

noncomputable local instance routerInstructions : InstructionModel J M signature.Instr := instructions model
local instance routerCoherent : RegionTypingCoherent (Φ := signature.Instr) J M := modelCoherent

set_option backward.isDefEq.respectTransparency false

/-! ## Routing on values -/

theorem bitTm_run (c : Bool) (u : value Ty.unit) :
    (((F).map (Lit (brOf (bitTm_typed c)))).of u : Trace (value Bit)) = (pure (bit c) : Trace (value Bit)) := by
  cases c
  · exact (inl_run (B := Ty.unit) (.var (i := 0) rfl) u).trans
      ((congrArg (Bind.bind (m := Trace) · _) (id_run Ty.unit u)).trans (pure_bind _ _))
  · exact (inr_run (A := Ty.unit) (.var (i := 0) rfl) u).trans
      ((congrArg (Bind.bind (m := Trace) · _) (id_run Ty.unit u)).trans (pure_bind _ _))

theorem bitState_const_run (q : Bool) (u : value Ty.unit) :
    (((F).map (Lit (brOf (A := State) (.inl (bitTm_typed q))))).of u : Trace (value State)) =
      (pure (Sum.inl (bit q)) : Trace (value State)) :=
  (inl_run (B := packedExitType ([] : LCtx (Ty Empty))) (bitTm_typed q) u).trans
    ((congrArg (Bind.bind (m := Trace) · _) (bitTm_run q u)).trans (pure_bind _ _))

theorem act_run (K : Nat) (a : Act K) (u : value Ty.unit) :
    (((F).map (Lit (act_typed K a))).of u : Trace (value Bit ⊕ value (States K))) =
      (pure (actVal K a) : Trace (value Bit ⊕ value (States K))) := by
  cases a with
  | ret c =>
    exact (inl_run (B := States K) (bitTm_typed c) u).trans
      ((congrArg (Bind.bind (m := Trace) · _) (bitTm_run c u)).trans (pure_bind _ _))
  | go j q =>
    exact (inr_run (A := Bit) (injTm_typed (.inl (bitTm_typed q)) K j) u).trans
      ((congrArg (Bind.bind (m := Trace) · _)
        (inj_of_run (.inl (bitTm_typed q)) (fun _ => Sum.inl (bit q)) (bitState_const_run q) K j u)).trans
          (pure_bind _ _))

theorem bitSplit_run (K : Nat) (a₀ a₁ : Act K) (b : value Bit) :
    (((F).map (Lit (bitSplit_typed K a₀ a₁))).of b : Trace (value Bit ⊕ value (States K))) =
      (pure (actVal K (Sum.elim (fun _ => a₀) (fun _ => a₁) b)) : Trace (value Bit ⊕ value (States K))) := by
  have arrow : Lit (bitSplit_typed K a₀ a₁) = exactCopair N (Lit (act_typed K a₀)) (Lit (act_typed K a₁)) :=
    (exactCopair_ofRegion N (act_typed K a₀) (act_typed K a₁)).symm
  rw [arrow]
  rcases b with u | u
  · exact (copair_inl_of _ _ u).trans (act_run K a₀ u)
  · exact (copair_inr_of _ _ u).trans (act_run K a₁ u)

theorem routerRoute_run (K : Nat) (a : Bool → Bool → Act K) (v : value Bit ⊕ value State) :
    (((F).map (Lit (routerRoute_typed K a))).of v : Trace (value Bit ⊕ value (States K))) =
      routerRouteVal K a v := by
  have arrow : Lit (routerRoute_typed K a) =
      exactCopair N (Lit (bitSplit_typed K (a false false) (a false true)))
        (Lit (stateSplit_typed K (a true false) (a true true))) :=
    (exactCopair_ofRegion N (bitSplit_typed K (a false false) (a false true))
      (stateSplit_typed K (a true false) (a true true))).symm
  have inner : Lit (stateSplit_typed K (a true false) (a true true)) =
      exactCopair N (Lit (bitSplit_typed K (a true false) (a true true))) (Lit (dead_typed K)) :=
    (exactCopair_ofRegion N (bitSplit_typed K (a true false) (a true true)) (dead_typed K)).symm
  rw [arrow]
  rcases v with b | s
  · refine (copair_inl_of _ _ b).trans ((bitSplit_run K _ _ b).trans ?_)
    rcases b with u | u <;> rfl
  · refine (copair_inr_of _ _ s).trans ?_
    rw [inner]
    rcases s with b | e
    · refine (copair_inl_of _ _ b).trans ((bitSplit_run K _ _ b).trans ?_)
      rcases b with u | u <;> rfl
    · exact e.elim

theorem routerRow_run (K : Nat) (p : Program) (a : Bool → Bool → Act K) (s : value State) :
    (((F).map (Lit (routerRow_typed K p a))).of s : Trace (value Bit ⊕ value (States K))) =
      Bind.bind (m := Trace) (stepModel p s) (routerRouteVal K a) := by
  have arrow : Lit (routerRow_typed K p a) = stepArrow p ≫ Lit (routerRoute_typed K a) :=
    (congrArg (Paper.Extension.Singleton.projection N).map
      (Paper.TypeCategory.ofRegion_comp (step_typed p) (routerRoute_typed K a) (routerRow_typed K p a)).symm).trans
      ((Paper.Extension.Singleton.projection N).map_comp _ _)
  rw [arrow]
  exact (comp_run _ _ s).trans
    (congr (congrArg (Bind.bind (m := Trace)) (BitLoop.step_run p s)) (funext (routerRoute_run K a)))

/-- One step of the table at state `i`. -/
theorem router_step_run {K : Nat} (t : Router K) (i : Fin (K + 1)) (s : value State) :
    t.stepM (injVal K i s) = Bind.bind (m := Trace) (stepModel (t.prog i) s) (routerRouteVal K (t.act i)) := by
  have rows := dispatch_run K t.rows_typed i s
  have literal := congrArg (fun h : (J).obj ((M).obj (States K)) ⟶ (J).obj ((M).obj _) =>
    h.of (injVal K i s)) (lit_run (dispatch_typed K t.rows_typed))
  exact literal.symm.trans (rows.trans (routerRow_run K (t.prog i) (t.act i) s))

theorem router_obs_eq {K : Nat} (t : Router K) (i : Fin (K + 1)) (g : Bool) :
    t.observations i g =
      (Silmaril.Elgot.iter (m := Trace) t.stepM (injVal K i (Sum.inl (bit g)))).outcomes :=
  dispatch_obs_eq t.rows_typed i g

/-! ## One round of a table of labelled requests -/

section Labels

variable {K : Nat} (label : Fin (K + 1) → Bool) (act : Fin (K + 1) → Bool → Bool → Act K)

theorem route_reply (i : Fin (K + 1)) (tag pl : Bool) :
    routerRouteVal K (act i) (terminal (if tag then !(labelPoll (label i)).returnRight
      else (labelPoll (label i)).returnRight) pl) = pure (actVal K (act i tag pl)) := by
  cases tag <;> cases pl <;> rfl

/-- A round has one event, and its reply selects the action. -/
theorem router_step_iff (i : Fin (K + 1)) (g : Bool) {y : Except Bool (value Bit ⊕ value (States K))}
    {w : Word} :
    (y, w) ∈ ((Router.ofLabels label act).stepM (injVal K i (Sum.inl (bit g)))).outcomes ↔
      ∃ tag pl, w = FreeMonoid.of (event (label i) g (tag, pl)) ∧ y = .ok (actVal K (act i tag pl)) := by
  rw [router_step_run, Tagged.mem_bind]
  constructor
  · rintro (⟨t', rfl, ht⟩ | ⟨x, u, v, hx, hk, rfl⟩)
    · rw [WithGuardedTablePacking.BitLoop.stepModel_outcomes] at ht
      obtain ⟨tag, pl, hy, -⟩ := (poll_outcomes (labelPoll (label i)) g _ _).1 ht
      cases hy
    · rw [WithGuardedTablePacking.BitLoop.stepModel_outcomes] at hx
      obtain ⟨tag, pl, hy, rfl⟩ := (poll_outcomes (labelPoll (label i)) g _ _).1 hx
      cases hy
      have hk' : (y, v) ∈ (routerRouteVal K (act i) (terminal (if tag then !(labelPoll (label i)).returnRight
          else (labelPoll (label i)).returnRight) pl)).outcomes := hk
      rw [route_reply] at hk'
      obtain ⟨rfl, rfl⟩ := mem_pure.1 hk'
      exact ⟨tag, pl, mul_one _, rfl⟩
  · rintro ⟨tag, pl, rfl, rfl⟩
    refine .inr ⟨terminal (if tag then !(labelPoll (label i)).returnRight
      else (labelPoll (label i)).returnRight) pl, _, 1, ?_, ?_, mul_one _⟩
    · rw [WithGuardedTablePacking.BitLoop.stepModel_outcomes]
      exact (poll_outcomes (labelPoll (label i)) g _ _).2 ⟨tag, pl, rfl, rfl⟩
    · have e := route_reply label act i tag pl
      exact e ▸ mem_pure.2 ⟨rfl, rfl⟩

/-- The observation law: a complete run is one event followed by what the
action of its reply allows. -/
theorem router_unfold (i : Fin (K + 1)) (g : Bool) (r : Except Bool (value Bit)) (w : Word) :
    (r, w) ∈ (Router.ofLabels label act).observations i g ↔
      ∃ tag pl v, w = FreeMonoid.of (event (label i) g (tag, pl)) * v ∧
        (Router.ofLabels label act).Cont (act i tag pl) r v := by
  rw [router_obs_eq, iter_unfold]
  constructor
  · rintro (⟨t', -, ht⟩ | ⟨b, rfl, hb⟩ | ⟨nxt, u, v, hu, hv, rfl⟩)
    · obtain ⟨tag, pl, -, e⟩ := (router_step_iff label act i g).1 ht
      cases e
    · obtain ⟨tag, pl, rfl, e⟩ := (router_step_iff label act i g).1 hb
      refine ⟨tag, pl, 1, (mul_one _).symm, ?_⟩
      cases h : act i tag pl with
      | ret c =>
        rw [h] at e
        cases e
        exact ⟨rfl, rfl⟩
      | go j q =>
        rw [h] at e
        cases e
    · obtain ⟨tag, pl, rfl, e⟩ := (router_step_iff label act i g).1 hu
      refine ⟨tag, pl, v, rfl, ?_⟩
      cases h : act i tag pl with
      | ret c =>
        rw [h] at e
        cases e
      | go j q =>
        rw [h] at e
        cases e
        show (r, v) ∈ (Router.ofLabels label act).observations j q
        rw [router_obs_eq]
        exact hv
  · rintro ⟨tag, pl, v, rfl, hc⟩
    cases h : act i tag pl with
    | ret c =>
      rw [h] at hc
      obtain ⟨rfl, rfl⟩ : r = .ok (bit c) ∧ v = 1 := hc
      refine .inr (.inl ⟨bit c, rfl, ?_⟩)
      rw [mul_one]
      exact (router_step_iff label act i g).2
        ⟨tag, pl, rfl, congrArg (fun a => Except.ok (actVal K a)) h.symm⟩
    | go j q =>
      rw [h] at hc
      have hv : (r, v) ∈ (Router.ofLabels label act).observations j q := hc
      rw [router_obs_eq] at hv
      exact .inr (.inr ⟨_, _, v, (router_step_iff label act i g).2
        ⟨tag, pl, rfl, congrArg (fun a => Except.ok (actVal K a)) h.symm⟩, hv, rfl⟩)

end Labels

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.TableModel

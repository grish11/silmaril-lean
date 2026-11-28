module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Router.Prefix.Defs
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.RouterRun
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.RouterReflection
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.BitLoop.Prefix

/-! # Prefix observations of a router table determine its bisimulation class -/

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

/-! ## One request in the two models -/

/-- Under any continuation, the request-prefix model adds exactly the
observation of the pending request. -/
theorem prefix_bind_outcomes {A : Type} (l : Bool) (q : value Bit) (k : value Answer → Trace A) :
    (prefixRequest l q >>= k).outcomes = (request l q >>= k).outcomes ∪ {(Except.error l, 1)} := by
  ext ⟨r, w⟩
  constructor
  · intro h
    rw [Tagged.mem_bind] at h
    rcases h with ⟨t, rfl, ht⟩ | ⟨a, u, v, ha, hk, rfl⟩
    · rw [BitLoop.prefixRequest_outcomes] at ht
      rcases ht with ht | ht
      · refine .inl ?_
        rw [Tagged.mem_bind]
        exact .inl ⟨t, rfl, ht⟩
      · have e := Prod.mk.inj (Set.mem_singleton_iff.1 ht)
        cases e.1
        cases e.2
        exact .inr rfl
    · rw [BitLoop.prefixRequest_outcomes] at ha
      rcases ha with ha | bad
      · refine .inl ?_
        rw [Tagged.mem_bind]
        exact .inr ⟨a, u, v, ha, hk, rfl⟩
      · cases (Prod.mk.inj (Set.mem_singleton_iff.1 bad)).1
  · rintro (h | h)
    · exact bind_sub l q k h
    · cases Set.mem_singleton_iff.1 h
      rw [Tagged.mem_bind]
      exact .inl ⟨l, rfl, by rw [BitLoop.prefixRequest_outcomes]; exact .inr rfl⟩

section Labels

variable {K : Nat} (label : Fin (K + 1) → Bool) (act : Fin (K + 1) → Bool → Bool → Act K)

theorem prefix_router_step (i : Fin (K + 1)) (x : value Bit) :
    (Router.ofLabels label act).prefixStepM (injVal K i (Sum.inl x)) =
      prefixRequest (label i) x >>= fun ans =>
        (pure (route false true ans) : Trace (value Bit ⊕ value State)) >>= routerRouteVal K (act i) := by
  have step := @RouterRun.router_step_run_in (instructions prefixModel) prefixCoherent K
    (Router.ofLabels label act) i (Sum.inl x)
  have one : prefixStep (labelPoll (label i)).program (Sum.inl x) =
      prefixRequest (label i) x >>= fun ans => pure (route false true ans) := by
    rw [poll_oneAsk]
    exact BitLoop.prefix_oneAsk_step (label i) false true x
  exact step.trans ((congrArg (Bind.bind (m := Trace) · (routerRouteVal K (act i))) one).trans
    (bind_assoc _ _ _))

theorem complete_router_step (i : Fin (K + 1)) (x : value Bit) :
    (Router.ofLabels label act).stepM (injVal K i (Sum.inl x)) =
      request (label i) x >>= fun ans =>
        (pure (route false true ans) : Trace (value Bit ⊕ value State)) >>= routerRouteVal K (act i) := by
  have step := router_step_run (Router.ofLabels label act) i (Sum.inl x)
  have one : stepModel (labelPoll (label i)).program (Sum.inl x) =
      request (label i) x >>= fun ans => pure (route false true ans) := by
    rw [poll_oneAsk]
    exact complete_oneAsk_step (label i) false true x
  exact step.trans ((congrArg (Bind.bind (m := Trace) · (routerRouteVal K (act i))) one).trans
    (bind_assoc _ _ _))

/-- A round in the request-prefix model: the pending request, or one of
the four completed exchanges with its action. -/
theorem prefix_step_iff (i : Fin (K + 1)) (g : Bool) {y : Except Bool (value Bit ⊕ value (States K))}
    {w : Word} :
    (y, w) ∈ ((Router.ofLabels label act).prefixStepM (injVal K i (Sum.inl (bit g)))).outcomes ↔
      (y = .error (label i) ∧ w = 1) ∨
        ∃ tag pl, w = FreeMonoid.of (event (label i) g (tag, pl)) ∧ y = .ok (actVal K (act i tag pl)) := by
  have sets : ((Router.ofLabels label act).prefixStepM (injVal K i (Sum.inl (bit g)))).outcomes =
      ((Router.ofLabels label act).stepM (injVal K i (Sum.inl (bit g)))).outcomes ∪
        {(Except.error (label i), 1)} := by
    rw [prefix_router_step, complete_router_step]
    exact prefix_bind_outcomes (label i) (bit g) _
  rw [sets]
  constructor
  · rintro (h | h)
    · exact .inr ((router_step_iff label act i g).1 h)
    · exact .inl (Prod.mk.inj (Set.mem_singleton_iff.1 h))
  · rintro (⟨rfl, rfl⟩ | h)
    · exact .inr rfl
    · exact .inl ((router_step_iff label act i g).2 h)

theorem prefix_obs_eq (t : Router K) (i : Fin (K + 1)) (g : Bool) :
    t.prefixObservations i g =
      (Silmaril.Elgot.iter (m := Trace) t.prefixStepM (injVal K i (Sum.inl (bit g)))).outcomes :=
  @RouterRun.dispatch_obs_eq (instructions prefixModel) prefixCoherent K _ t.rows_typed i g

/-- The observation law of the request-prefix model: the pending first
request, or one completed exchange followed by what its action allows. -/
theorem prefix_unfold (i : Fin (K + 1)) (g : Bool) (r : Except Bool (value Bit)) (w : Word) :
    (r, w) ∈ (Router.ofLabels label act).prefixObservations i g ↔
      (r = .error (label i) ∧ w = 1) ∨
        ∃ tag pl v, w = FreeMonoid.of (event (label i) g (tag, pl)) * v ∧
          (Router.ofLabels label act).PrefixCont (act i tag pl) r v := by
  rw [prefix_obs_eq, iter_unfold]
  constructor
  · rintro (⟨t', rfl, ht⟩ | ⟨b, rfl, hb⟩ | ⟨nxt, u, v, hu, hv, rfl⟩)
    · rcases (prefix_step_iff label act i g).1 ht with ⟨e, rfl⟩ | ⟨tag, pl, -, e⟩
      · cases e
        exact .inl ⟨rfl, rfl⟩
      · cases e
    · rcases (prefix_step_iff label act i g).1 hb with ⟨e, -⟩ | ⟨tag, pl, rfl, e⟩
      · cases e
      · refine .inr ⟨tag, pl, 1, (mul_one _).symm, ?_⟩
        cases h : act i tag pl with
        | ret c =>
          rw [h] at e
          cases e
          exact ⟨rfl, rfl⟩
        | go j q =>
          rw [h] at e
          cases e
    · rcases (prefix_step_iff label act i g).1 hu with ⟨e, -⟩ | ⟨tag, pl, rfl, e⟩
      · cases e
      · refine .inr ⟨tag, pl, v, rfl, ?_⟩
        cases h : act i tag pl with
        | ret c =>
          rw [h] at e
          cases e
        | go j q =>
          rw [h] at e
          cases e
          show (r, v) ∈ (Router.ofLabels label act).prefixObservations j q
          rw [prefix_obs_eq]
          exact hv
  · rintro (⟨rfl, rfl⟩ | ⟨tag, pl, v, rfl, hc⟩)
    · exact .inl ⟨label i, rfl, (prefix_step_iff label act i g).2 (.inl ⟨rfl, rfl⟩)⟩
    · cases h : act i tag pl with
      | ret c =>
        rw [h] at hc
        obtain ⟨rfl, rfl⟩ : r = .ok (bit c) ∧ v = 1 := hc
        refine .inr (.inl ⟨bit c, rfl, ?_⟩)
        rw [mul_one]
        exact (prefix_step_iff label act i g).2
          (.inr ⟨tag, pl, rfl, congrArg (fun a => Except.ok (actVal K a)) h.symm⟩)
      | go j q =>
        rw [h] at hc
        have hv : (r, v) ∈ (Router.ofLabels label act).prefixObservations j q := hc
        rw [prefix_obs_eq] at hv
        exact .inr (.inr ⟨_, _, v, (prefix_step_iff label act i g).2
          (.inr ⟨tag, pl, rfl, congrArg (fun a => Except.ok (actVal K a)) h.symm⟩), hv, rfl⟩)

/-- The first request is always observed pending. -/
theorem prefix_pending (i : Fin (K + 1)) (g : Bool) :
    (Except.error (label i), (1 : Word)) ∈ (Router.ofLabels label act).prefixObservations i g :=
  (prefix_unfold label act i g _ _).2 (.inl ⟨rfl, rfl⟩)

/-- An observation with an empty log is that pending request. -/
theorem prefix_one (i : Fin (K + 1)) (g : Bool) {r : Except Bool (value Bit)}
    (h : (r, (1 : Word)) ∈ (Router.ofLabels label act).prefixObservations i g) : r = .error (label i) := by
  rcases (prefix_unfold label act i g r 1).1 h with ⟨e, -⟩ | ⟨tag, pl, v, e, -⟩
  · exact e
  · exact (one_ne_cons e).elim

/-- Every reply has an observation whose log is that one exchange. -/
theorem prefix_first (i : Fin (K + 1)) (g tag pl : Bool) :
    ∃ r, (r, FreeMonoid.of (event (label i) g (tag, pl)) * 1) ∈
      (Router.ofLabels label act).prefixObservations i g := by
  cases h : act i tag pl with
  | ret c =>
    refine ⟨.ok (bit c), (prefix_unfold label act i g _ _).2 (.inr ⟨tag, pl, 1, rfl, ?_⟩)⟩
    rw [h]
    exact ⟨rfl, rfl⟩
  | go j q =>
    refine ⟨.error (label j), (prefix_unfold label act i g _ _).2 (.inr ⟨tag, pl, 1, rfl, ?_⟩)⟩
    rw [h]
    exact prefix_pending label act j q

end Labels

/-! ## Reading a table from its prefix observations -/

section Rounds

variable {K K' : Nat} (label : Fin (K + 1) → Bool) (act : Fin (K + 1) → Bool → Bool → Act K)
  (label' : Fin (K' + 1) → Bool) (act' : Fin (K' + 1) → Bool → Bool → Act K')

theorem prefix_cont_sub (i : Fin (K + 1)) (i' : Fin (K' + 1)) (g : Bool) (hl : label i = label' i')
    (h : (Router.ofLabels label act).prefixObservations i g ⊆
      (Router.ofLabels label' act').prefixObservations i' g)
    (tag pl : Bool) (r : Except Bool (value Bit)) (v : Word)
    (hc : (Router.ofLabels label act).PrefixCont (act i tag pl) r v) :
    (Router.ofLabels label' act').PrefixCont (act' i' tag pl) r v := by
  have mem := h ((prefix_unfold label act i g r _).2 (.inr ⟨tag, pl, v, rfl, hc⟩))
  rcases (prefix_unfold label' act' i' g r _).1 mem with ⟨-, e⟩ | ⟨tag', pl', v', e, hc'⟩
  · exact (one_ne_cons e.symm).elim
  · rw [hl] at e
    obtain ⟨ev, rfl⟩ := word_cons e
    obtain ⟨-, -, rfl, rfl⟩ := event_inj ev
    exact hc'

/-- The pending first request shows the label, with no hypothesis. -/
theorem prefix_label (i : Fin (K + 1)) (i' : Fin (K' + 1)) (g g' : Bool)
    (h : (Router.ofLabels label act).prefixObservations i g =
      (Router.ofLabels label' act').prefixObservations i' g') : label i = label' i' := by
  have mem := prefix_pending label act i g
  rw [h] at mem
  exact Except.error.inj (prefix_one label' act' i' g' mem)

/-- Any completed first exchange shows the query. -/
theorem prefix_query (i : Fin (K + 1)) (i' : Fin (K' + 1)) (g g' : Bool)
    (h : (Router.ofLabels label act).prefixObservations i g =
      (Router.ofLabels label' act').prefixObservations i' g') : g = g' := by
  obtain ⟨r, mem⟩ := prefix_first label act i g false false
  rw [h] at mem
  rcases (prefix_unfold label' act' i' g' r _).1 mem with ⟨-, e⟩ | ⟨tag', pl', v', e, -⟩
  · exact (one_ne_cons e.symm).elim
  · exact (event_inj (word_cons e).1).2.1

/-- Equal prefix observations give matching actions on every reply. No
liveness is needed: a jump always has the pending request of its target. -/
theorem prefix_act_rel (i : Fin (K + 1)) (i' : Fin (K' + 1)) (g : Bool) (hl : label i = label' i')
    (h : (Router.ofLabels label act).prefixObservations i g =
      (Router.ofLabels label' act').prefixObservations i' g) (tag pl : Bool) :
    Act.Rel (fun j j' => ∃ q, (Router.ofLabels label act).prefixObservations j q =
      (Router.ofLabels label' act').prefixObservations j' q) (act i tag pl) (act' i' tag pl) := by
  have fwd := prefix_cont_sub label act label' act' i i' g hl h.subset tag pl
  have bwd := prefix_cont_sub label' act' label act i' i g hl.symm h.symm.subset tag pl
  cases ha : act i tag pl with
  | ret c =>
    cases ha' : act' i' tag pl with
    | ret c' =>
      rw [ha, ha'] at fwd
      have t : (Except.ok (bit c) : Except Bool (value Bit)) = .ok (bit c') ∧ (1 : Word) = 1 :=
        fwd (.ok (bit c)) 1 ⟨rfl, rfl⟩
      exact bit_inj (Except.ok.inj t.1)
    | go j' q' =>
      rw [ha, ha'] at fwd
      have t : (Except.ok (bit c), (1 : Word)) ∈ (Router.ofLabels label' act').prefixObservations j' q' :=
        fwd (.ok (bit c)) 1 ⟨rfl, rfl⟩
      cases prefix_one label' act' j' q' t
  | go j q =>
    cases ha' : act' i' tag pl with
    | ret c' =>
      rw [ha, ha'] at fwd
      have t : (Except.error (label j) : Except Bool (value Bit)) = .ok (bit c') ∧ (1 : Word) = 1 :=
        fwd (.error (label j)) 1 (prefix_pending label act j q)
      cases t.1
    | go j' q' =>
      rw [ha, ha'] at fwd bwd
      have eq : (Router.ofLabels label act).prefixObservations j q =
          (Router.ofLabels label' act').prefixObservations j' q' := Set.ext fun ⟨r, v⟩ => ⟨fwd r v, bwd r v⟩
      obtain rfl := prefix_query label act label' act' j j' q q' eq
      exact ⟨rfl, q, eq⟩

/-- Equal prefix observations give a bisimulation, for every table. -/
theorem prefix_bisim_of_obs (i : Fin (K + 1)) (i' : Fin (K' + 1))
    (h : (Router.ofLabels label act).prefixObservations i false =
      (Router.ofLabels label' act').prefixObservations i' false) :
    ∃ R : Fin (K + 1) → Fin (K' + 1) → Prop, (∀ x y, R x y → label x = label' y) ∧
      (∀ x y, R x y → ∀ tag pl, Act.Rel R (act x tag pl) (act' y tag pl)) ∧ R i i' :=
  ⟨fun x y => ∃ q, (Router.ofLabels label act).prefixObservations x q =
      (Router.ofLabels label' act').prefixObservations y q,
    fun x y ⟨q, e⟩ => prefix_label label act label' act' x y q q e,
    fun x y ⟨q, e⟩ tag pl => prefix_act_rel label act label' act' x y q
      (prefix_label label act label' act' x y q q e) e tag pl,
    ⟨false, h⟩⟩

end Rounds

/-! ## Soundness in the request-prefix model -/

section Sound

noncomputable local instance prefixSoundInstructions : InstructionModel J M signature.Instr :=
  instructions prefixModel
local instance prefixSoundCoherent : RegionTypingCoherent (Φ := signature.Instr) J M := prefixCoherent

theorem prefix_obs_of_valid {K K' : Nat} {t : Router K} {t' : Router K'} {i : Fin (K + 1)}
    {i' : Fin (K' + 1)}
    (h : WithGuardedTablePacking.Valid (t.entered_typed i).hasType (t'.entered_typed i').hasType) (g : Bool) :
    t.prefixObservations i g = t'.prefixObservations i' g := by
  have eq := h J M (fun _ _ => ⟨rfl, rfl⟩)
  unfold Router.prefixObservations denoteSingletonRegion
  rw [eq]

end Sound

/-- The request-prefix model is a supported model, so every equation of
`WithPhaseUniformity`, the phase-uniformity seed included, holds in it. -/
theorem prefix_obs_of_eqv {K K' : Nat} {t : Router K} {t' : Router K'} {i : Fin (K + 1)}
    {i' : Fin (K' + 1)} (e : PEqv false [State] (t.entered i) (t'.entered i') [Bit]) (g : Bool) :
    t.prefixObservations i g = t'.prefixObservations i' g :=
  prefix_obs_of_valid (WithGuardedTablePacking.WithPhaseUniformity.valid_of_eqv false e _ _) g

/-! ## The chain of two dead states -/

theorem chain_prefix (a b g : Bool) :
    (Except.error b, FreeMonoid.of (event a g (false, false)) * 1) ∈
      (Router.ofLabels (chainLabel a b) chainAct).prefixObservations 0 g :=
  (prefix_unfold (chainLabel a b) chainAct 0 g _ _).2 (.inr ⟨false, false, 1, rfl,
    show (_, _) ∈ (Router.ofLabels (chainLabel a b) chainAct).prefixObservations 1 false from
      prefix_pending (chainLabel a b) chainAct 1 false⟩)

theorem chain_prefix_not (a g : Bool) {b b' : Bool} (ne : b ≠ b') :
    (Except.error b, FreeMonoid.of (event a g (false, false)) * 1) ∉
      (Router.ofLabels (chainLabel a b') chainAct).prefixObservations 0 g := by
  intro h
  rcases (prefix_unfold (chainLabel a b') chainAct 0 g _ _).1 h with ⟨-, e⟩ | ⟨tag, pl, v, e, hc⟩
  · exact one_ne_cons e.symm
  · obtain ⟨ev, rfl⟩ := word_cons e
    obtain ⟨-, -, rfl, rfl⟩ := event_inj ev
    have h1 : (Except.error b, (1 : Word)) ∈
        (Router.ofLabels (chainLabel a b') chainAct).prefixObservations 1 false := hc
    exact ne (Except.error.inj (prefix_one (chainLabel a b') chainAct 1 false h1))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.TableModel

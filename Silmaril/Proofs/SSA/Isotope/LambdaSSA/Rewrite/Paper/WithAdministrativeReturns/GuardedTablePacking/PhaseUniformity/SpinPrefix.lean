module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Silent.Diverge.Defs
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.SilentPoint

/-! # Prefix observations of router tables with the canonical silent row -/

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

section Spin

noncomputable local instance spinPrefixInstructions : InstructionModel J M signature.Instr :=
  instructions prefixModel
local instance spinPrefixCoherent : RegionTypingCoherent (Φ := signature.Instr) J M := prefixCoherent

variable {K : Nat} (label : Fin (K + 1) → Option Bool) (act : Fin (K + 1) → Bool → Bool → Act K)

/-! ## One step -/

/-- At a labelled row the step is the step of a table of labelled rows. -/
theorem spin_step_lab (i : Fin (K + 1)) {l : Bool} (hl : label i = some l) (s : value State) :
    (Router.ofSpin label act).prefixStepM (injVal K i s) =
      (Router.ofLabels (fun _ => l) (fun _ => act i)).prefixStepM (injVal K i s) := by
  have a := RouterRun.router_step_run_in (Router.ofSpin label act) i s
  have b := RouterRun.router_step_run_in (Router.ofLabels (fun _ : Fin (K + 1) => l) (fun _ => act i)) i s
  have prog : (Router.ofSpin label act).prog i = (labelPoll l).program := by
    show lsProg (label i) = _
    rw [hl]
    rfl
  have acts : (Router.ofSpin label act).act i = act i := by
    show lsAct (label i) i (act i) = _
    rw [hl]
    rfl
  rw [prog, acts] at a
  exact a.trans b.symm

theorem spin_step_iff (i : Fin (K + 1)) {l : Bool} (hl : label i = some l) (g : Bool)
    {y : Except Bool (value Bit ⊕ value (States K))} {w : Word} :
    (y, w) ∈ ((Router.ofSpin label act).prefixStepM (injVal K i (Sum.inl (bit g)))).outcomes ↔
      (y = .error l ∧ w = 1) ∨
        ∃ tag pl, w = FreeMonoid.of (event l g (tag, pl)) ∧ y = .ok (actVal K (act i tag pl)) := by
  rw [spin_step_lab label act i hl]
  exact prefix_step_iff (fun _ => l) (fun _ => act i) i g

/-- At a silent row the step repeats to the row with no event. -/
theorem spin_step_none (i : Fin (K + 1)) (hn : label i = none) (g : Bool) :
    (Router.ofSpin label act).prefixStepM (injVal K i (Sum.inl (bit g))) =
      (pure (actVal K (.go i false)) : Trace (value Bit ⊕ value (States K))) := by
  have u : value Ty.unit := ()
  have rows := RouterRun.dispatch_run K (Router.ofSpin label act).rows_typed i (Sum.inl (bit g))
  rw [RouterRun.lit_run (dispatch_typed K (Router.ofSpin label act).rows_typed),
    RouterRun.lit_run ((Router.ofSpin label act).rows_typed i)] at rows
  have key : ∀ o : Option Bool, o = none →
      ∀ h : ValueBranches [State] (routerRow K (lsProg o) (lsAct o i (act i))) [Silmaril.coprod Bit (States K)],
        (denoteSingletonRegion J M h.hasType).of (Sum.inl (bit g)) =
          (pure (actVal K (.go i false)) : Trace (value Bit ⊕ value (States K))) := fun o ho h => by
    subst ho
    have row : PEqv false [Ty.unit] (constEntry g (routerRow K (.ret 0 0) fun _ _ => .go i false))
        (.br 0 (actTm K (.go i false))) [Silmaril.coprod Bit (States K)] :=
      .paper ((Paper.TypeCategory.ofRegion_eq_iff (constEntry_typed g h) (act_typed K (.go i false))).mp
        (Tables.pure_const K 0 (fun _ _ => .go i false) g))
    have d := congrArg
      (fun k : (J).obj ((M).obj Ty.unit) ⟶ (J).obj ((M).obj (Silmaril.coprod Bit (States K))) => k.of u)
      (valid_denote (constEntry_typed g h) (act_typed K (.go i false))
        (WithGuardedTablePacking.WithPhaseUniformity.valid_of_eqv false row _ _))
    have run := RouterRun.act_run K (.go i false) u
    rw [RouterRun.lit_run (act_typed K (.go i false))] at run
    exact (const_denote h g u).symm.trans (d.trans run)
  exact rows.trans (key (label i) hn ((Router.ofSpin label act).rows_typed i))

/-! ## Observations -/

/-- The observation law at a labelled row: the pending request, or one
completed exchange followed by what its action allows. -/
theorem spin_unfold (i : Fin (K + 1)) {l : Bool} (hl : label i = some l) (g : Bool)
    (r : Except Bool (value Bit)) (w : Word) :
    (r, w) ∈ (Router.ofSpin label act).prefixObservations i g ↔
      (r = .error l ∧ w = 1) ∨
        ∃ tag pl v, w = FreeMonoid.of (event l g (tag, pl)) * v ∧
          (Router.ofSpin label act).PrefixCont (act i tag pl) r v := by
  rw [prefix_obs_eq, iter_unfold]
  constructor
  · rintro (⟨t', rfl, ht⟩ | ⟨b, rfl, hb⟩ | ⟨nxt, u, v, hu, hv, rfl⟩)
    · rcases (spin_step_iff label act i hl g).1 ht with ⟨e, rfl⟩ | ⟨tag, pl, -, e⟩
      · cases e
        exact .inl ⟨rfl, rfl⟩
      · cases e
    · rcases (spin_step_iff label act i hl g).1 hb with ⟨e, -⟩ | ⟨tag, pl, rfl, e⟩
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
    · rcases (spin_step_iff label act i hl g).1 hu with ⟨e, -⟩ | ⟨tag, pl, rfl, e⟩
      · cases e
      · refine .inr ⟨tag, pl, v, rfl, ?_⟩
        cases h : act i tag pl with
        | ret c =>
          rw [h] at e
          cases e
        | go j q =>
          rw [h] at e
          cases e
          show (r, v) ∈ (Router.ofSpin label act).prefixObservations j q
          rw [prefix_obs_eq]
          exact hv
  · rintro (⟨rfl, rfl⟩ | ⟨tag, pl, v, rfl, hc⟩)
    · exact .inl ⟨l, rfl, (spin_step_iff label act i hl g).2 (.inl ⟨rfl, rfl⟩)⟩
    · cases h : act i tag pl with
      | ret c =>
        rw [h] at hc
        obtain ⟨rfl, rfl⟩ : r = .ok (bit c) ∧ v = 1 := hc
        refine .inr (.inl ⟨bit c, rfl, ?_⟩)
        rw [mul_one]
        exact (spin_step_iff label act i hl g).2
          (.inr ⟨tag, pl, rfl, congrArg (fun a => Except.ok (actVal K a)) h.symm⟩)
      | go j q =>
        rw [h] at hc
        have hv : (r, v) ∈ (Router.ofSpin label act).prefixObservations j q := hc
        rw [prefix_obs_eq] at hv
        exact .inr (.inr ⟨_, _, v, (spin_step_iff label act i hl g).2
          (.inr ⟨tag, pl, rfl, congrArg (fun a => Except.ok (actVal K a)) h.symm⟩), hv, rfl⟩)

/-- A silent row has no observation. -/
theorem spin_empty (i : Fin (K + 1)) (hn : label i = none) (g : Bool) :
    (Router.ofSpin label act).prefixObservations i g = ∅ := by
  rw [prefix_obs_eq]
  apply Set.eq_empty_of_subset_empty
  intro x hx
  have sub := iter_induction (Router.ofSpin label act).prefixStepM
    (fun a => {_x | ∀ j s, a = injVal K j s → label j = none → False})
    (fun a t w h j s e hj => by
      subst e
      rcases s with b | z
      · have step : (Router.ofSpin label act).prefixStepM (injVal K j (Sum.inl b)) =
            (pure (actVal K (.go j false)) : Trace (value Bit ⊕ value (States K))) := by
          rcases b with u | u
          · exact spin_step_none label act j hj false
          · exact spin_step_none label act j hj true
        rw [step] at h
        exact absurd (BitLoop.mem_pure.1 h).1 (by simp)
      · exact z.elim)
    (fun a b w h j s e hj => by
      subst e
      rcases s with b' | z
      · have step : (Router.ofSpin label act).prefixStepM (injVal K j (Sum.inl b')) =
            (pure (actVal K (.go j false)) : Trace (value Bit ⊕ value (States K))) := by
          rcases b' with u | u
          · exact spin_step_none label act j hj false
          · exact spin_step_none label act j hj true
        rw [step] at h
        have e := Except.ok.inj (BitLoop.mem_pure.1 h).1
        cases e
      · exact z.elim)
    (fun a next u r v h hk j s e hj => by
      subst e
      rcases s with b' | z
      · have step : (Router.ofSpin label act).prefixStepM (injVal K j (Sum.inl b')) =
            (pure (actVal K (.go j false)) : Trace (value Bit ⊕ value (States K))) := by
          rcases b' with u | u
          · exact spin_step_none label act j hj false
          · exact spin_step_none label act j hj true
        rw [step] at h
        have e := Sum.inr.inj (Except.ok.inj (BitLoop.mem_pure.1 h).1)
        exact hk j (Sum.inl (bit false)) e hj
      · exact z.elim)
    (injVal K i (Sum.inl (bit g))) hx
  exact sub i (Sum.inl (bit g)) rfl hn

theorem spin_pending (i : Fin (K + 1)) {l : Bool} (hl : label i = some l) (g : Bool) :
    (Except.error l, (1 : Word)) ∈ (Router.ofSpin label act).prefixObservations i g :=
  (spin_unfold label act i hl g _ _).2 (.inl ⟨rfl, rfl⟩)

theorem spin_one (i : Fin (K + 1)) {l : Bool} (hl : label i = some l) (g : Bool)
    {r : Except Bool (value Bit)}
    (h : (r, (1 : Word)) ∈ (Router.ofSpin label act).prefixObservations i g) : r = .error l := by
  rcases (spin_unfold label act i hl g r 1).1 h with ⟨e, -⟩ | ⟨tag, pl, v, e, -⟩
  · exact e
  · exact (one_ne_cons e).elim

/-- Something is observed after an action that returns or repeats to a
labelled row. -/
theorem seen_cont (a : Act K) (h : a.Seen label) :
    ∃ r v, (Router.ofSpin label act).PrefixCont a r v := by
  cases a with
  | ret c => exact ⟨.ok (bit c), 1, rfl, rfl⟩
  | go j q =>
    obtain ⟨l, hl⟩ : ∃ l, label j = some l := h
    exact ⟨.error l, 1, spin_pending label act j hl q⟩

/-- A blind row shows only its pending request: its observations do not
depend on its query. -/
theorem blind_obs (i : Fin (K + 1)) {l : Bool} (hl : label i = some l)
    (blind : ∀ tag pl, ∃ j q, act i tag pl = .go j q ∧ label j = none) (g : Bool) :
    (Router.ofSpin label act).prefixObservations i g = {(Except.error l, 1)} := by
  ext ⟨r, w⟩
  rw [spin_unfold label act i hl g r w]
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨tag, pl, v, -, hc⟩)
    · rfl
    · obtain ⟨j, q, ha, hj⟩ := blind tag pl
      rw [ha] at hc
      have mem : (r, v) ∈ (Router.ofSpin label act).prefixObservations j q := hc
      rw [spin_empty label act j hj q] at mem
      exact mem.elim
  · intro h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 h)
    exact .inl ⟨rfl, rfl⟩

end Spin

/-! ## Reading a table with silent rows from its prefix observations -/

section Reflect

noncomputable local instance spinReflectInstructions : InstructionModel J M signature.Instr :=
  instructions prefixModel
local instance spinReflectCoherent : RegionTypingCoherent (Φ := signature.Instr) J M := prefixCoherent

variable {K K' : Nat} (label : Fin (K + 1) → Option Bool) (act : Fin (K + 1) → Bool → Bool → Act K)
  (label' : Fin (K' + 1) → Option Bool) (act' : Fin (K' + 1) → Bool → Bool → Act K')

theorem spin_cont_sub (i : Fin (K + 1)) (i' : Fin (K' + 1)) {l : Bool} (hl : label i = some l)
    (hl' : label' i' = some l) (g : Bool)
    (h : (Router.ofSpin label act).prefixObservations i g ⊆ (Router.ofSpin label' act').prefixObservations i' g)
    (tag pl : Bool) (r : Except Bool (value Bit)) (v : Word)
    (hc : (Router.ofSpin label act).PrefixCont (act i tag pl) r v) :
    (Router.ofSpin label' act').PrefixCont (act' i' tag pl) r v := by
  have mem := h ((spin_unfold label act i hl g r _).2 (.inr ⟨tag, pl, v, rfl, hc⟩))
  rcases (spin_unfold label' act' i' hl' g r _).1 mem with ⟨-, e⟩ | ⟨tag', pl', v', e, hc'⟩
  · exact (one_ne_cons e.symm).elim
  · obtain ⟨ev, rfl⟩ := word_cons e
    obtain ⟨-, -, rfl, rfl⟩ := event_inj ev
    exact hc'

/-- Equal observations show the same kind of row. -/
theorem spin_kind (i : Fin (K + 1)) (i' : Fin (K' + 1)) (g g' : Bool)
    (h : (Router.ofSpin label act).prefixObservations i g = (Router.ofSpin label' act').prefixObservations i' g')
    (hn : label' i' = none) : label i = none := by
  cases hl : label i with
  | none => rfl
  | some l =>
    have mem := spin_pending label act i hl g
    rw [h, spin_empty label' act' i' hn g'] at mem
    exact mem.elim

/-- The pending first request shows the label. -/
theorem spin_label (i : Fin (K + 1)) (i' : Fin (K' + 1)) {l l' : Bool} (hl : label i = some l)
    (hl' : label' i' = some l') (g g' : Bool)
    (h : (Router.ofSpin label act).prefixObservations i g = (Router.ofSpin label' act').prefixObservations i' g') :
    l = l' := by
  have mem := spin_pending label act i hl g
  rw [h] at mem
  exact Except.error.inj (spin_one label' act' i' hl' g' mem)

/-- A reply after which something is observed shows the query. -/
theorem spin_query (hs : Sighted label act) (i : Fin (K + 1)) (i' : Fin (K' + 1)) {l l' : Bool}
    (hl : label i = some l) (hl' : label' i' = some l') (g g' : Bool)
    (h : (Router.ofSpin label act).prefixObservations i g = (Router.ofSpin label' act').prefixObservations i' g') :
    g = g' := by
  obtain ⟨tag, pl, seen⟩ := hs i l hl
  obtain ⟨r, v, hc⟩ := seen_cont label act _ seen
  have mem := (spin_unfold label act i hl g r _).2 (.inr ⟨tag, pl, v, rfl, hc⟩)
  rw [h] at mem
  rcases (spin_unfold label' act' i' hl' g' r _).1 mem with ⟨-, e⟩ | ⟨tag', pl', v', e, -⟩
  · exact (one_ne_cons e.symm).elim
  · exact (event_inj (word_cons e).1).2.1

variable (ht : Tidy label act) (ht' : Tidy label' act') (hs : Sighted label act)

include ht ht' hs in
/-- Equal observations give matching actions on every reply: the same
returned Bit, successors with equal observations, or silent rows. -/
theorem spin_act_rel (i : Fin (K + 1)) (i' : Fin (K' + 1)) {l : Bool} (hl : label i = some l)
    (hl' : label' i' = some l) (g : Bool)
    (h : (Router.ofSpin label act).prefixObservations i g = (Router.ofSpin label' act').prefixObservations i' g)
    (tag pl : Bool) :
    Act.Rel (fun j j' => ∃ q, (Router.ofSpin label act).prefixObservations j q =
      (Router.ofSpin label' act').prefixObservations j' q) (act i tag pl) (act' i' tag pl) := by
  have fwd := spin_cont_sub label act label' act' i i' hl hl' g h.subset tag pl
  have bwd := spin_cont_sub label' act' label act i' i hl' hl g h.symm.subset tag pl
  have no_ok : ∀ {W : Nat} (lab : Fin (W + 1) → Option Bool) (a : Fin (W + 1) → Bool → Bool → Act W)
      (j : Fin (W + 1)) (q c : Bool),
      (Except.ok (bit c), (1 : Word)) ∉ (Router.ofSpin lab a).prefixObservations j q := fun lab a j q c mem => by
    cases hj : lab j with
    | none =>
      rw [spin_empty lab a j hj q] at mem
      exact mem
    | some lj => cases spin_one lab a j hj q mem
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
      exact (no_ok label' act' j' q' c (fwd (.ok (bit c)) 1 ⟨rfl, rfl⟩)).elim
  | go j q =>
    cases ha' : act' i' tag pl with
    | ret c' =>
      rw [ha, ha'] at bwd
      exact (no_ok label act j q c' (bwd (.ok (bit c')) 1 ⟨rfl, rfl⟩)).elim
    | go j' q' =>
      rw [ha, ha'] at fwd bwd
      have same : (Router.ofSpin label act).prefixObservations j q =
          (Router.ofSpin label' act').prefixObservations j' q' :=
        Set.ext fun ⟨r, v⟩ => ⟨fun m => fwd r v m, fun m => bwd r v m⟩
      cases hj : label j with
      | none =>
        have hj' : label' j' = none := spin_kind label' act' label act j' j q' q same.symm hj
        have e : q = false := ht i l hl tag pl j q ha hj
        have e' : q' = false := ht' i' l hl' tag pl j' q' ha' hj'
        subst e
        subst e'
        exact ⟨rfl, false, same⟩
      | some lj =>
        cases hj' : label' j' with
        | none =>
          have bad := spin_kind label act label' act' j j' q q' same hj'
          rw [hj] at bad
          cases bad
        | some lj' =>
          have e : q = q' := spin_query label act label' act' hs j j' hj hj' q q' same
          subst e
          exact ⟨rfl, q, same⟩

include ht ht' hs in
/-- Equal prefix observations are a bisimulation. -/
theorem spin_bisim :
    Router.Bisimulation (Router.ofSpin label act) (Router.ofSpin label' act')
      (fun j j' => ∃ q, (Router.ofSpin label act).prefixObservations j q =
        (Router.ofSpin label' act').prefixObservations j' q) :=
  ⟨fun x y ⟨q, h⟩ => by
      show lsProg (label x) = lsProg (label' y)
      cases hx : label x with
      | none =>
        have hy : label' y = none := spin_kind label' act' label act y x q q h.symm hx
        rw [hy]
      | some l =>
        cases hy : label' y with
        | none =>
          have bad := spin_kind label act label' act' x y q q h hy
          rw [hx] at bad
          cases bad
        | some l' => rw [spin_label label act label' act' x y hx hy q q h],
    fun x y ⟨q, h⟩ f b => by
      show Act.Rel _ (lsAct (label x) x (act x) f b) (lsAct (label' y) y (act' y) f b)
      cases hx : label x with
      | none =>
        have hy : label' y = none := spin_kind label' act' label act y x q q h.symm hx
        rw [hy]
        exact ⟨rfl, q, h⟩
      | some l =>
        cases hy : label' y with
        | none =>
          have bad := spin_kind label act label' act' x y q q h hy
          rw [hx] at bad
          cases bad
        | some l' =>
          have e := spin_label label act label' act' x y hx hy q q h
          subst e
          exact spin_act_rel label act label' act' ht ht' hs x y hx hy q h f b⟩

include ht ht' hs in
/-- Equal prefix observations at one query give equal entered loops. -/
theorem spin_eqv_of_obs (i : Fin (K + 1)) (i' : Fin (K' + 1)) (q : Bool)
    (h : (Router.ofSpin label act).prefixObservations i q = (Router.ofSpin label' act').prefixObservations i' q) :
    PEqv false [State] ((Router.ofSpin label act).entered i) ((Router.ofSpin label' act').entered i') [Bit] :=
  Tables.router_bisimulation_eqv _ _ _ (spin_bisim label act label' act' ht ht' hs) i i' ⟨q, h⟩

end Reflect

/-! ## Loops that are tables with silent rows at each constant -/

section Pointed

noncomputable local instance spinPointedInstructions : InstructionModel J M signature.Instr :=
  instructions prefixModel
local instance spinPointedCoherent : RegionTypingCoherent (Φ := signature.Instr) J M := prefixCoherent

variable {K K' : Nat} {label : Fin (K + 1) → Option Bool} {act : Fin (K + 1) → Bool → Bool → Act K}
  {label' : Fin (K' + 1) → Option Bool} {act' : Fin (K' + 1) → Bool → Bool → Act K'}
  {r r' : Region signature.Instr} {x : Bool → Fin (K + 1)} {x' : Bool → Fin (K' + 1)}

/-- Valid loops have the same prefix observations at each constant. -/
theorem spin_pointed_obs (h : ValueBranches [State] r [Bit]) (h' : ValueBranches [State] r' [Bit])
    (hp : SpinPointed r label act x) (hp' : SpinPointed r' label' act' x')
    (v : WithGuardedTablePacking.Valid h.hasType h'.hasType) (q : Bool) :
    (Router.ofSpin label act).prefixObservations (x q) q =
      (Router.ofSpin label' act').prefixObservations (x' q) q := by
  have u : value Ty.unit := ()
  have a := congrArg (fun k : (J).obj ((M).obj Ty.unit) ⟶ (J).obj ((M).obj Bit) => k.of u)
    (valid_denote (constEntry_typed q h) (constEntry_typed q ((Router.ofSpin label act).entered_typed (x q)))
      (WithGuardedTablePacking.WithPhaseUniformity.valid_of_eqv false (hp q) _ _))
  have a' := congrArg (fun k : (J).obj ((M).obj Ty.unit) ⟶ (J).obj ((M).obj Bit) => k.of u)
    (valid_denote (constEntry_typed q h') (constEntry_typed q ((Router.ofSpin label' act').entered_typed (x' q)))
      (WithGuardedTablePacking.WithPhaseUniformity.valid_of_eqv false (hp' q) _ _))
  have m := congrArg (fun k : (J).obj ((M).obj State) ⟶ (J).obj ((M).obj Bit) => k.of (Sum.inl (bit q)))
    (valid_denote h h' v)
  exact congrArg Tagged.outcomes
    ((const_denote ((Router.ofSpin label act).entered_typed (x q)) q u).symm.trans (a.symm.trans
      ((const_denote h q u).trans (m.trans ((const_denote h' q u).symm.trans
        (a'.trans (const_denote ((Router.ofSpin label' act').entered_typed (x' q)) q u)))))))

end Pointed

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.TableModel

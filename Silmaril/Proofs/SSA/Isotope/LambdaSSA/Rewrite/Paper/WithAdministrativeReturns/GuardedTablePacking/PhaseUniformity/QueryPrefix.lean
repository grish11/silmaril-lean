module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Silent.Diverge.Query.Defs
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.SpinPrefix

/-! # Router tables with silent rows in the query-aware model -/

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
open Paper.WithCaseBind.BitQuery (queryBit)

section Query

noncomputable local instance queryInstructions : InstructionModel J M signature.Instr :=
  instructions queryModel
local instance queryRegionCoherent : RegionTypingCoherent (Φ := signature.Instr) J M := queryCoherent

/-! ## The model on regions -/

theorem q_valid_denote {X D : Ty Empty} {r r' : Region signature.Instr} (h : ValueBranches [X] r [D])
    (h' : ValueBranches [X] r' [D]) (v : WithGuardedTablePacking.Valid h.hasType h'.hasType) :
    denoteSingletonRegion J M h.hasType = denoteSingletonRegion J M h'.hasType := by
  have eq := v J M (fun _ _ => ⟨rfl, rfl⟩)
  unfold denoteSingletonRegion
  rw [eq]

theorem q_const_denote {D : Ty Empty} {r : Region signature.Instr} (h : ValueBranches [State] r [D]) (q : Bool)
    (u : value Ty.unit) :
    (denoteSingletonRegion J M (constEntry_typed q h).hasType).of u =
      (denoteSingletonRegion J M h.hasType).of (Sum.inl (bit q)) := by
  have arrow : Lit (constEntry_typed q h) = Lit (const_typed q) ≫ Lit h :=
    (congrArg (Paper.Extension.Singleton.projection N).map
      (Paper.TypeCategory.ofRegion_comp (const_typed q) h (constEntry_typed q h)).symm).trans
      ((Paper.Extension.Singleton.projection N).map_comp _ _)
  have run := RouterRun.comp_run (Lit (const_typed q)) (Lit h) u
  rw [← arrow] at run
  have c := RouterRun.bitState_const_run q u
  have lhs := congrArg (fun k : (J).obj ((M).obj Ty.unit) ⟶ (J).obj ((M).obj D) => k.of u)
    (RouterRun.lit_run (constEntry_typed q h))
  have rhs := congrArg (fun k : (J).obj ((M).obj State) ⟶ (J).obj ((M).obj D) => k.of (Sum.inl (bit q)))
    (RouterRun.lit_run h)
  exact lhs.symm.trans (run.trans (((congrArg (Bind.bind (m := Trace) · _) c).trans (pure_bind _ _)).trans rhs))

/-- Valid loops have the same observations in the query-aware model. -/
theorem query_obs_of_valid {K K' : Nat} {t : Router K} {t' : Router K'} {i : Fin (K + 1)} {i' : Fin (K' + 1)}
    (h : WithGuardedTablePacking.Valid (t.entered_typed i).hasType (t'.entered_typed i').hasType) (g : Bool) :
    t.queryObservations i g = t'.queryObservations i' g := by
  have eq := h J M (fun _ _ => ⟨rfl, rfl⟩)
  unfold Router.queryObservations denoteSingletonRegion
  rw [eq]

/-! ## One request -/

theorem queryBit_bit (g : Bool) : queryBit (bit g) = g := by
  cases g <;> rfl

theorem queryRequest_outcomes (l : Bool) (q : value Bit) :
    (queryRequest l q).outcomes = (request l q).outcomes ∪ {(Except.error l, pendingWord l (queryBit q))} := by
  unfold queryRequest Tagged.withIncomplete
  rw [Tagged.outcomes_ofOutcomes, Set.image_singleton]

/-- Under any continuation, the query-aware model adds exactly the
observation of the pending request with its mark. -/
theorem query_bind_outcomes {A : Type} (l : Bool) (q : value Bit) (k : value Answer → Trace A) :
    (queryRequest l q >>= k).outcomes =
      (request l q >>= k).outcomes ∪ {(Except.error l, pendingWord l (queryBit q))} := by
  ext ⟨r, w⟩
  constructor
  · intro h
    rw [Tagged.mem_bind] at h
    rcases h with ⟨t, rfl, ht⟩ | ⟨a, u, v, ha, hk, rfl⟩
    · rw [queryRequest_outcomes] at ht
      rcases ht with ht | ht
      · refine .inl ?_
        rw [Tagged.mem_bind]
        exact .inl ⟨t, rfl, ht⟩
      · have e := Prod.mk.inj (Set.mem_singleton_iff.1 ht)
        cases e.1
        cases e.2
        exact .inr rfl
    · rw [queryRequest_outcomes] at ha
      rcases ha with ha | bad
      · refine .inl ?_
        rw [Tagged.mem_bind]
        exact .inr ⟨a, u, v, ha, hk, rfl⟩
      · cases (Prod.mk.inj (Set.mem_singleton_iff.1 bad)).1
  · rintro (h | h)
    · rw [Tagged.mem_bind] at h ⊢
      rcases h with ⟨t, rfl, ht⟩ | ⟨a, u, v, ha, hk, rfl⟩
      · exact .inl ⟨t, rfl, by rw [queryRequest_outcomes]; exact .inl ht⟩
      · exact .inr ⟨a, u, v, by rw [queryRequest_outcomes]; exact .inl ha, hk, rfl⟩
    · cases Set.mem_singleton_iff.1 h
      rw [Tagged.mem_bind]
      exact .inl ⟨l, rfl, by rw [queryRequest_outcomes]; exact .inr rfl⟩

variable {K : Nat} (label : Fin (K + 1) → Option Bool) (act : Fin (K + 1) → Bool → Bool → Act K)

/-! ## One step -/

theorem query_step_lab (i : Fin (K + 1)) {l : Bool} (hl : label i = some l) (x : value Bit) :
    (Router.ofSpin label act).queryStepM (injVal K i (Sum.inl x)) =
      queryRequest l x >>= fun ans =>
        (pure (route false true ans) : Trace (value Bit ⊕ value State)) >>= routerRouteVal K (act i) := by
  have a := RouterRun.router_step_run_in (Router.ofSpin label act) i (Sum.inl x)
  have prog : (Router.ofSpin label act).prog i = (labelPoll l).program := by
    show lsProg (label i) = _
    rw [hl]
    rfl
  have acts : (Router.ofSpin label act).act i = act i := by
    show lsAct (label i) i (act i) = _
    rw [hl]
    rfl
  rw [prog, acts] at a
  have one : stepIn (labelPoll l).program (Sum.inl x) =
      queryRequest l x >>= fun ans => pure (route false true ans) := by
    rw [poll_oneAsk]
    exact oneAsk_step l false true x
  exact a.trans ((congrArg (Bind.bind (m := Trace) · (routerRouteVal K (act i))) one).trans (bind_assoc _ _ _))

theorem query_step_iff (i : Fin (K + 1)) {l : Bool} (hl : label i = some l) (g : Bool)
    {y : Except Bool (value Bit ⊕ value (States K))} {w : Word} :
    (y, w) ∈ ((Router.ofSpin label act).queryStepM (injVal K i (Sum.inl (bit g)))).outcomes ↔
      (y = .error l ∧ w = pendingWord l g) ∨
        ∃ tag pl, w = FreeMonoid.of (event l g (tag, pl)) ∧ y = .ok (actVal K (act i tag pl)) := by
  have sets : ((Router.ofSpin label act).queryStepM (injVal K i (Sum.inl (bit g)))).outcomes =
      ((Router.ofLabels (fun _ : Fin (K + 1) => l) (fun _ => act i)).stepM (injVal K i (Sum.inl (bit g)))).outcomes ∪
        {(Except.error l, pendingWord l g)} := by
    rw [query_step_lab label act i hl, complete_router_step (fun _ => l) (fun _ => act i) i (bit g)]
    have e := query_bind_outcomes l (bit g)
      (fun ans => (pure (route false true ans) : Trace (value Bit ⊕ value State)) >>= routerRouteVal K (act i))
    rw [queryBit_bit] at e
    exact e
  rw [sets]
  constructor
  · rintro (h | h)
    · exact .inr ((router_step_iff (fun _ => l) (fun _ => act i) i g).1 h)
    · exact .inl (Prod.mk.inj (Set.mem_singleton_iff.1 h))
  · rintro (⟨rfl, rfl⟩ | h)
    · exact .inr rfl
    · exact .inl ((router_step_iff (fun _ => l) (fun _ => act i) i g).2 h)

/-- At a silent row the step repeats to the row with no event. -/
theorem query_step_none (i : Fin (K + 1)) (hn : label i = none) (g : Bool) :
    (Router.ofSpin label act).queryStepM (injVal K i (Sum.inl (bit g))) =
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
      (q_valid_denote (constEntry_typed g h) (act_typed K (.go i false))
        (WithGuardedTablePacking.WithPhaseUniformity.valid_of_eqv false row _ _))
    have run := RouterRun.act_run K (.go i false) u
    rw [RouterRun.lit_run (act_typed K (.go i false))] at run
    exact (q_const_denote h g u).symm.trans (d.trans run)
  exact rows.trans (key (label i) hn ((Router.ofSpin label act).rows_typed i))

theorem query_obs_eq (t : Router K) (i : Fin (K + 1)) (g : Bool) :
    t.queryObservations i g =
      (Silmaril.Elgot.iter (m := Trace) t.queryStepM (injVal K i (Sum.inl (bit g)))).outcomes :=
  RouterRun.dispatch_obs_eq t.rows_typed i g

/-! ## Observations -/

/-- The observation law at a labelled row: the pending request, or one
completed exchange followed by what its action allows. -/
theorem query_unfold (i : Fin (K + 1)) {l : Bool} (hl : label i = some l) (g : Bool)
    (r : Except Bool (value Bit)) (w : Word) :
    (r, w) ∈ (Router.ofSpin label act).queryObservations i g ↔
      (r = .error l ∧ w = pendingWord l g) ∨
        ∃ tag pl v, w = FreeMonoid.of (event l g (tag, pl)) * v ∧
          (Router.ofSpin label act).QueryCont (act i tag pl) r v := by
  rw [query_obs_eq, iter_unfold]
  constructor
  · rintro (⟨t', rfl, ht⟩ | ⟨b, rfl, hb⟩ | ⟨nxt, u, v, hu, hv, rfl⟩)
    · rcases (query_step_iff label act i hl g).1 ht with ⟨e, rfl⟩ | ⟨tag, pl, -, e⟩
      · cases e
        exact .inl ⟨rfl, rfl⟩
      · cases e
    · rcases (query_step_iff label act i hl g).1 hb with ⟨e, -⟩ | ⟨tag, pl, rfl, e⟩
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
    · rcases (query_step_iff label act i hl g).1 hu with ⟨e, -⟩ | ⟨tag, pl, rfl, e⟩
      · cases e
      · refine .inr ⟨tag, pl, v, rfl, ?_⟩
        cases h : act i tag pl with
        | ret c =>
          rw [h] at e
          cases e
        | go j q =>
          rw [h] at e
          cases e
          show (r, v) ∈ (Router.ofSpin label act).queryObservations j q
          rw [query_obs_eq]
          exact hv
  · rintro (⟨rfl, rfl⟩ | ⟨tag, pl, v, rfl, hc⟩)
    · exact .inl ⟨l, rfl, (query_step_iff label act i hl g).2 (.inl ⟨rfl, rfl⟩)⟩
    · cases h : act i tag pl with
      | ret c =>
        rw [h] at hc
        obtain ⟨rfl, rfl⟩ : r = .ok (bit c) ∧ v = 1 := hc
        refine .inr (.inl ⟨bit c, rfl, ?_⟩)
        rw [mul_one]
        exact (query_step_iff label act i hl g).2
          (.inr ⟨tag, pl, rfl, congrArg (fun a => Except.ok (actVal K a)) h.symm⟩)
      | go j q =>
        rw [h] at hc
        have hv : (r, v) ∈ (Router.ofSpin label act).queryObservations j q := hc
        rw [query_obs_eq] at hv
        exact .inr (.inr ⟨_, _, v, (query_step_iff label act i hl g).2
          (.inr ⟨tag, pl, rfl, congrArg (fun a => Except.ok (actVal K a)) h.symm⟩), hv, rfl⟩)

/-- A silent row has no observation. -/
theorem query_empty (i : Fin (K + 1)) (hn : label i = none) (g : Bool) :
    (Router.ofSpin label act).queryObservations i g = ∅ := by
  rw [query_obs_eq]
  apply Set.eq_empty_of_subset_empty
  intro x hx
  have sub := iter_induction (Router.ofSpin label act).queryStepM
    (fun a => {_x | ∀ j s, a = injVal K j s → label j = none → False})
    (fun a t w h j s e hj => by
      subst e
      rcases s with b | z
      · have step : (Router.ofSpin label act).queryStepM (injVal K j (Sum.inl b)) =
            (pure (actVal K (.go j false)) : Trace (value Bit ⊕ value (States K))) := by
          rcases b with u | u
          · exact query_step_none label act j hj false
          · exact query_step_none label act j hj true
        rw [step] at h
        exact absurd (BitLoop.mem_pure.1 h).1 (by simp)
      · exact z.elim)
    (fun a b w h j s e hj => by
      subst e
      rcases s with b' | z
      · have step : (Router.ofSpin label act).queryStepM (injVal K j (Sum.inl b')) =
            (pure (actVal K (.go j false)) : Trace (value Bit ⊕ value (States K))) := by
          rcases b' with u | u
          · exact query_step_none label act j hj false
          · exact query_step_none label act j hj true
        rw [step] at h
        have e := Except.ok.inj (BitLoop.mem_pure.1 h).1
        cases e
      · exact z.elim)
    (fun a next u r v h hk j s e hj => by
      subst e
      rcases s with b' | z
      · have step : (Router.ofSpin label act).queryStepM (injVal K j (Sum.inl b')) =
            (pure (actVal K (.go j false)) : Trace (value Bit ⊕ value (States K))) := by
          rcases b' with u | u
          · exact query_step_none label act j hj false
          · exact query_step_none label act j hj true
        rw [step] at h
        have e := Sum.inr.inj (Except.ok.inj (BitLoop.mem_pure.1 h).1)
        exact hk j (Sum.inl (bit false)) e hj
      · exact z.elim)
    (injVal K i (Sum.inl (bit g))) hx
  exact sub i (Sum.inl (bit g)) rfl hn

theorem query_pending (i : Fin (K + 1)) {l : Bool} (hl : label i = some l) (g : Bool) :
    (Except.error l, pendingWord l g) ∈ (Router.ofSpin label act).queryObservations i g :=
  (query_unfold label act i hl g _ _).2 (.inl ⟨rfl, rfl⟩)

/-- No observation has an empty log: a pending request has its mark. -/
theorem query_no_one (i : Fin (K + 1)) (g : Bool) (r : Except Bool (value Bit)) :
    (r, (1 : Word)) ∉ (Router.ofSpin label act).queryObservations i g := fun mem => by
  cases hl : label i with
  | none =>
    rw [query_empty label act i hl g] at mem
    exact mem
  | some l =>
    rcases (query_unfold label act i hl g r 1).1 mem with ⟨-, e⟩ | ⟨tag, pl, v, e, -⟩
    · exact one_ne_cons (e.trans (mul_one _).symm)
    · exact one_ne_cons e

/-- After an empty log an action has returned. -/
theorem query_cont_one (a : Act K) (r : Except Bool (value Bit))
    (h : (Router.ofSpin label act).QueryCont a r 1) : ∃ c, a = .ret c ∧ r = .ok (bit c) := by
  cases a with
  | ret c => exact ⟨c, rfl, h.1⟩
  | go j q => exact (query_no_one label act j q r h).elim

/-- A blind row shows its pending request with its query. -/
theorem query_blind (i : Fin (K + 1)) {l : Bool} (hl : label i = some l)
    (blind : ∀ tag pl, ∃ j q, act i tag pl = .go j q ∧ label j = none) (g : Bool) :
    (Router.ofSpin label act).queryObservations i g = {(Except.error l, pendingWord l g)} := by
  ext ⟨r, w⟩
  rw [query_unfold label act i hl g r w]
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨tag, pl, v, -, hc⟩)
    · rfl
    · obtain ⟨j, q, ha, hj⟩ := blind tag pl
      rw [ha] at hc
      have mem : (r, v) ∈ (Router.ofSpin label act).queryObservations j q := hc
      rw [query_empty label act j hj q] at mem
      exact mem.elim
  · intro h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 h)
    exact .inl ⟨rfl, rfl⟩

end Query

/-! ## Reading a table with silent rows from its observations, with no blind spot -/

section QueryReflect

noncomputable local instance queryReflectInstructions : InstructionModel J M signature.Instr :=
  instructions queryModel
local instance queryReflectCoherent : RegionTypingCoherent (Φ := signature.Instr) J M := queryCoherent

variable {K K' : Nat} (label : Fin (K + 1) → Option Bool) (act : Fin (K + 1) → Bool → Bool → Act K)
  (label' : Fin (K' + 1) → Option Bool) (act' : Fin (K' + 1) → Bool → Bool → Act K')

theorem pending_inj {l l' g g' : Bool} (e : pendingWord l g = pendingWord l' g') : l = l' ∧ g = g' := by
  have w : FreeMonoid.of (event l g (false, false)) * (1 : Word) =
      FreeMonoid.of (event l' g' (false, false)) * 1 := by
    rw [mul_one, mul_one]
    exact e
  have ev := event_inj (word_cons w).1
  exact ⟨ev.1, ev.2.1⟩

theorem query_cont_sub (i : Fin (K + 1)) (i' : Fin (K' + 1)) {l : Bool} (hl : label i = some l)
    (hl' : label' i' = some l) (g : Bool)
    (h : (Router.ofSpin label act).queryObservations i g ⊆ (Router.ofSpin label' act').queryObservations i' g)
    (tag pl : Bool) (r : Except Bool (value Bit)) (v : Word)
    (hc : (Router.ofSpin label act).QueryCont (act i tag pl) r v) :
    (Router.ofSpin label' act').QueryCont (act' i' tag pl) r v := by
  have mem := h ((query_unfold label act i hl g r _).2 (.inr ⟨tag, pl, v, rfl, hc⟩))
  rcases (query_unfold label' act' i' hl' g r _).1 mem with ⟨hr, e⟩ | ⟨tag', pl', v', e, hc'⟩
  · have w : FreeMonoid.of (event l g (tag, pl)) * v = FreeMonoid.of (event l g (false, false)) * 1 :=
      e.trans (mul_one _).symm
    obtain ⟨-, rfl⟩ := word_cons w
    obtain ⟨c, -, rc⟩ := query_cont_one label act _ r hc
    rw [hr] at rc
    cases rc
  · obtain ⟨ev, rfl⟩ := word_cons e
    obtain ⟨-, -, rfl, rfl⟩ := event_inj ev
    exact hc'

theorem query_kind (i : Fin (K + 1)) (i' : Fin (K' + 1)) (g g' : Bool)
    (h : (Router.ofSpin label act).queryObservations i g = (Router.ofSpin label' act').queryObservations i' g')
    (hn : label' i' = none) : label i = none := by
  cases hl : label i with
  | none => rfl
  | some l =>
    have mem := query_pending label act i hl g
    rw [h, query_empty label' act' i' hn g'] at mem
    exact mem.elim

/-- The pending first request shows the label and the query. -/
theorem query_label_query (i : Fin (K + 1)) (i' : Fin (K' + 1)) {l l' : Bool} (hl : label i = some l)
    (hl' : label' i' = some l') (g g' : Bool)
    (h : (Router.ofSpin label act).queryObservations i g = (Router.ofSpin label' act').queryObservations i' g') :
    l = l' ∧ g = g' := by
  have mem := query_pending label act i hl g
  rw [h] at mem
  rcases (query_unfold label' act' i' hl' g' _ _).1 mem with ⟨e₁, e₂⟩ | ⟨tag', pl', v', e, hc'⟩
  · cases e₁
    exact pending_inj e₂
  · have w : FreeMonoid.of (event l g (false, false)) * (1 : Word) =
        FreeMonoid.of (event l' g' (tag', pl')) * v' := (mul_one _).trans e
    obtain ⟨-, rfl⟩ := word_cons w
    obtain ⟨c, -, rc⟩ := query_cont_one label' act' _ _ hc'
    cases rc

variable (ht : Tidy label act) (ht' : Tidy label' act')

include ht ht' in
/-- Equal observations give matching actions on every reply. No reply has
to be observed after: the pending request shows the query. -/
theorem query_act_rel (i : Fin (K + 1)) (i' : Fin (K' + 1)) {l : Bool} (hl : label i = some l)
    (hl' : label' i' = some l) (g : Bool)
    (h : (Router.ofSpin label act).queryObservations i g = (Router.ofSpin label' act').queryObservations i' g)
    (tag pl : Bool) :
    Act.Rel (fun j j' => ∃ q, (Router.ofSpin label act).queryObservations j q =
      (Router.ofSpin label' act').queryObservations j' q) (act i tag pl) (act' i' tag pl) := by
  have fwd := query_cont_sub label act label' act' i i' hl hl' g h.subset tag pl
  have bwd := query_cont_sub label' act' label act i' i hl' hl g h.symm.subset tag pl
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
      exact (query_no_one label' act' j' q' _ (fwd (.ok (bit c)) 1 ⟨rfl, rfl⟩)).elim
  | go j q =>
    cases ha' : act' i' tag pl with
    | ret c' =>
      rw [ha, ha'] at bwd
      exact (query_no_one label act j q _ (bwd (.ok (bit c')) 1 ⟨rfl, rfl⟩)).elim
    | go j' q' =>
      rw [ha, ha'] at fwd bwd
      have same : (Router.ofSpin label act).queryObservations j q =
          (Router.ofSpin label' act').queryObservations j' q' :=
        Set.ext fun ⟨r, v⟩ => ⟨fun m => fwd r v m, fun m => bwd r v m⟩
      cases hj : label j with
      | none =>
        have hj' : label' j' = none := query_kind label' act' label act j' j q' q same.symm hj
        have e : q = false := ht i l hl tag pl j q ha hj
        have e' : q' = false := ht' i' l hl' tag pl j' q' ha' hj'
        subst e
        subst e'
        exact ⟨rfl, false, same⟩
      | some lj =>
        cases hj' : label' j' with
        | none =>
          have bad := query_kind label act label' act' j j' q q' same hj'
          rw [hj] at bad
          cases bad
        | some lj' =>
          have e : q = q' := (query_label_query label act label' act' j j' hj hj' q q' same).2
          subst e
          exact ⟨rfl, q, same⟩

include ht ht' in
/-- Equal observations in the query-aware model are a bisimulation. -/
theorem query_bisim :
    Router.Bisimulation (Router.ofSpin label act) (Router.ofSpin label' act')
      (fun j j' => ∃ q, (Router.ofSpin label act).queryObservations j q =
        (Router.ofSpin label' act').queryObservations j' q) :=
  ⟨fun x y ⟨q, h⟩ => by
      show lsProg (label x) = lsProg (label' y)
      cases hx : label x with
      | none =>
        have hy : label' y = none := query_kind label' act' label act y x q q h.symm hx
        rw [hy]
      | some l =>
        cases hy : label' y with
        | none =>
          have bad := query_kind label act label' act' x y q q h hy
          rw [hx] at bad
          cases bad
        | some l' => rw [(query_label_query label act label' act' x y hx hy q q h).1],
    fun x y ⟨q, h⟩ f b => by
      show Act.Rel _ (lsAct (label x) x (act x) f b) (lsAct (label' y) y (act' y) f b)
      cases hx : label x with
      | none =>
        have hy : label' y = none := query_kind label' act' label act y x q q h.symm hx
        rw [hy]
        exact ⟨rfl, q, h⟩
      | some l =>
        cases hy : label' y with
        | none =>
          have bad := query_kind label act label' act' x y q q h hy
          rw [hx] at bad
          cases bad
        | some l' =>
          have e := (query_label_query label act label' act' x y hx hy q q h).1
          subst e
          exact query_act_rel label act label' act' ht ht' x y hx hy q h f b⟩

include ht ht' in
theorem query_eqv_of_obs (i : Fin (K + 1)) (i' : Fin (K' + 1)) (q : Bool)
    (h : (Router.ofSpin label act).queryObservations i q = (Router.ofSpin label' act').queryObservations i' q) :
    PEqv false [State] ((Router.ofSpin label act).entered i) ((Router.ofSpin label' act').entered i') [Bit] :=
  Tables.router_bisimulation_eqv _ _ _ (query_bisim label act label' act' ht ht') i i' ⟨q, h⟩

end QueryReflect

/-! ## Loops that are tables with silent rows at each constant -/

section QueryPointed

noncomputable local instance queryPointedInstructions : InstructionModel J M signature.Instr :=
  instructions queryModel
local instance queryPointedCoherent : RegionTypingCoherent (Φ := signature.Instr) J M := queryCoherent

variable {K K' : Nat} {label : Fin (K + 1) → Option Bool} {act : Fin (K + 1) → Bool → Bool → Act K}
  {label' : Fin (K' + 1) → Option Bool} {act' : Fin (K' + 1) → Bool → Bool → Act K'}
  {r r' : Region signature.Instr} {x : Bool → Fin (K + 1)} {x' : Bool → Fin (K' + 1)}

theorem query_pointed_obs (h : ValueBranches [State] r [Bit]) (h' : ValueBranches [State] r' [Bit])
    (hp : SpinPointed r label act x) (hp' : SpinPointed r' label' act' x')
    (v : WithGuardedTablePacking.Valid h.hasType h'.hasType) (q : Bool) :
    (Router.ofSpin label act).queryObservations (x q) q =
      (Router.ofSpin label' act').queryObservations (x' q) q := by
  have u : value Ty.unit := ()
  have a := congrArg (fun k : (J).obj ((M).obj Ty.unit) ⟶ (J).obj ((M).obj Bit) => k.of u)
    (q_valid_denote (constEntry_typed q h) (constEntry_typed q ((Router.ofSpin label act).entered_typed (x q)))
      (WithGuardedTablePacking.WithPhaseUniformity.valid_of_eqv false (hp q) _ _))
  have a' := congrArg (fun k : (J).obj ((M).obj Ty.unit) ⟶ (J).obj ((M).obj Bit) => k.of u)
    (q_valid_denote (constEntry_typed q h') (constEntry_typed q ((Router.ofSpin label' act').entered_typed (x' q)))
      (WithGuardedTablePacking.WithPhaseUniformity.valid_of_eqv false (hp' q) _ _))
  have m := congrArg (fun k : (J).obj ((M).obj State) ⟶ (J).obj ((M).obj Bit) => k.of (Sum.inl (bit q)))
    (q_valid_denote h h' v)
  exact congrArg Tagged.outcomes
    ((q_const_denote ((Router.ofSpin label act).entered_typed (x q)) q u).symm.trans (a.symm.trans
      ((q_const_denote h q u).trans (m.trans ((q_const_denote h' q u).symm.trans
        (a'.trans (q_const_denote ((Router.ofSpin label' act').entered_typed (x' q)) q u)))))))

end QueryPointed

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.TableModel

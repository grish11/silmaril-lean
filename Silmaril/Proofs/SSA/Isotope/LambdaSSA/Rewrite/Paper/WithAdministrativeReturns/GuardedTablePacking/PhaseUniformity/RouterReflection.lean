module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.RouterModel

/-! # Complete runs of a live router table determine its bisimulation class -/

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

noncomputable local instance routerReflInstructions : InstructionModel J M signature.Instr := instructions model
local instance routerReflCoherent : RegionTypingCoherent (Φ := signature.Instr) J M := modelCoherent

set_option backward.isDefEq.respectTransparency false

theorem bit_inj {c c' : Bool} (h : bit c = bit c') : c = c' := by
  cases c <;> cases c' <;> first | rfl | cases h

section Rounds

variable {K K' : Nat} (label : Fin (K + 1) → Bool) (act : Fin (K + 1) → Bool → Bool → Act K)
  (label' : Fin (K' + 1) → Bool) (act' : Fin (K' + 1) → Bool → Bool → Act K')

theorem router_obs_ne_one (i : Fin (K + 1)) (g : Bool) {r : Except Bool (value Bit)}
    (h : (r, (1 : Word)) ∈ (Router.ofLabels label act).observations i g) : False := by
  obtain ⟨tag, pl, v, e, -⟩ := (router_unfold label act i g r 1).1 h
  exact one_ne_cons e

/-- Cancelling the first event: what may follow a reply in one table may
follow it in the other. -/
theorem router_cont_sub (i : Fin (K + 1)) (i' : Fin (K' + 1)) (g : Bool) (hl : label i = label' i')
    (h : (Router.ofLabels label act).observations i g ⊆ (Router.ofLabels label' act').observations i' g)
    (tag pl : Bool) (r : Except Bool (value Bit)) (v : Word)
    (hc : (Router.ofLabels label act).Cont (act i tag pl) r v) :
    (Router.ofLabels label' act').Cont (act' i' tag pl) r v := by
  have mem := h ((router_unfold label act i g r _).2 ⟨tag, pl, v, rfl, hc⟩)
  obtain ⟨tag', pl', v', e, hc'⟩ := (router_unfold label' act' i' g r _).1 mem
  rw [hl] at e
  obtain ⟨ev, rfl⟩ := word_cons e
  obtain ⟨-, -, rfl, rfl⟩ := event_inj ev
  exact hc'

/-- The first event of any complete run shows the label and the query. -/
theorem router_head (i : Fin (K + 1)) (i' : Fin (K' + 1)) (g g' : Bool)
    (live : ((Router.ofLabels label act).observations i g).Nonempty)
    (h : (Router.ofLabels label act).observations i g = (Router.ofLabels label' act').observations i' g') :
    label i = label' i' ∧ g = g' := by
  obtain ⟨⟨r, w⟩, hw⟩ := live
  obtain ⟨tag, pl, v, e, -⟩ := (router_unfold label act i g r w).1 hw
  rw [h] at hw
  obtain ⟨tag', pl', v', e', -⟩ := (router_unfold label' act' i' g' r w).1 hw
  obtain ⟨ev, -⟩ := word_cons (e.symm.trans e')
  exact ⟨(event_inj ev).1, (event_inj ev).2.1⟩

/-- Equal complete runs give matching actions on every reply: the same
returned Bit, or the same next query and equal complete runs there. -/
theorem router_act_rel (live : ∀ j q, ((Router.ofLabels label act).observations j q).Nonempty)
    (i : Fin (K + 1)) (i' : Fin (K' + 1)) (g : Bool) (hl : label i = label' i')
    (h : (Router.ofLabels label act).observations i g = (Router.ofLabels label' act').observations i' g)
    (tag pl : Bool) :
    Act.Rel (fun j j' => ∃ q, (Router.ofLabels label act).observations j q =
      (Router.ofLabels label' act').observations j' q) (act i tag pl) (act' i' tag pl) := by
  have fwd := router_cont_sub label act label' act' i i' g hl h.subset tag pl
  have bwd := router_cont_sub label' act' label act i' i g hl.symm h.symm.subset tag pl
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
      have t : (Except.ok (bit c), (1 : Word)) ∈ (Router.ofLabels label' act').observations j' q' :=
        fwd (.ok (bit c)) 1 ⟨rfl, rfl⟩
      exact (router_obs_ne_one label' act' j' q' t).elim
  | go j q =>
    cases ha' : act' i' tag pl with
    | ret c' =>
      rw [ha, ha'] at bwd
      have t : (Except.ok (bit c'), (1 : Word)) ∈ (Router.ofLabels label act).observations j q :=
        bwd (.ok (bit c')) 1 ⟨rfl, rfl⟩
      exact (router_obs_ne_one label act j q t).elim
    | go j' q' =>
      rw [ha, ha'] at fwd bwd
      have eq : (Router.ofLabels label act).observations j q =
          (Router.ofLabels label' act').observations j' q' := Set.ext fun ⟨r, v⟩ => ⟨fwd r v, bwd r v⟩
      obtain ⟨-, rfl⟩ := router_head label act label' act' j j' q q' (live j q) eq
      exact ⟨rfl, q, eq⟩

/-- Equal complete runs of a live table give a bisimulation. -/
theorem router_bisim_of_obs (live : ∀ j q, ((Router.ofLabels label act).observations j q).Nonempty)
    (i : Fin (K + 1)) (i' : Fin (K' + 1))
    (h : (Router.ofLabels label act).observations i false = (Router.ofLabels label' act').observations i' false) :
    ∃ R : Fin (K + 1) → Fin (K' + 1) → Prop, (∀ x y, R x y → label x = label' y) ∧
      (∀ x y, R x y → ∀ tag pl, Act.Rel R (act x tag pl) (act' y tag pl)) ∧ R i i' :=
  ⟨fun x y => ∃ q, (Router.ofLabels label act).observations x q = (Router.ofLabels label' act').observations y q,
    fun x y ⟨q, e⟩ => (router_head label act label' act' x y q q (live x q) e).1,
    fun x y ⟨q, e⟩ tag pl => router_act_rel label act label' act' live x y q
      (router_head label act label' act' x y q q (live x q) e).1 e tag pl,
    ⟨false, h⟩⟩

theorem router_eqv_of_bisim (R : Fin (K + 1) → Fin (K' + 1) → Prop) (hl : ∀ x y, R x y → label x = label' y)
    (ha : ∀ x y, R x y → ∀ tag pl, Act.Rel R (act x tag pl) (act' y tag pl)) (i : Fin (K + 1))
    (i' : Fin (K' + 1)) (r : R i i') :
    PEqv false [State] ((Router.ofLabels label act).entered i) ((Router.ofLabels label' act').entered i') [Bit] :=
  Tables.router_bisimulation_eqv (Router.ofLabels label act) (Router.ofLabels label' act') R
    ⟨fun x y r => congrArg (fun l => (labelPoll l).program) (hl x y r), ha⟩ i i' r

/-- A returning reply at every state makes every state live. -/
theorem router_live_of_ret (h : ∀ i, ∃ tag pl c, act i tag pl = .ret c) (i : Fin (K + 1)) (g : Bool) :
    ((Router.ofLabels label act).observations i g).Nonempty := by
  obtain ⟨tag, pl, c, hc⟩ := h i
  refine ⟨(.ok (bit c), _), (router_unfold label act i g _ _).2 ⟨tag, pl, 1, rfl, ?_⟩⟩
  rw [hc]
  exact ⟨rfl, rfl⟩

/-- A table without returning replies has no complete run. -/
theorem router_dead (h : ∀ i tag pl, ∃ j q, act i tag pl = .go j q) (i : Fin (K + 1)) (g : Bool) :
    (Router.ofLabels label act).observations i g = ∅ := by
  rw [router_obs_eq]
  refine Set.eq_empty_of_subset_empty
    (iter_induction (Router.ofLabels label act).stepM (fun _ => ∅) ?_ ?_ ?_ _)
  · intro v t' w hw
    obtain ⟨i, s, rfl⟩ := injVal_cases K v
    obtain ⟨g, rfl⟩ := state_cases s
    obtain ⟨tag, pl, -, e⟩ := (router_step_iff label act i g).1 hw
    cases e
  · intro v b w hw
    obtain ⟨i, s, rfl⟩ := injVal_cases K v
    obtain ⟨g, rfl⟩ := state_cases s
    obtain ⟨tag, pl, -, e⟩ := (router_step_iff label act i g).1 hw
    obtain ⟨j, q, hj⟩ := h i tag pl
    rw [hj] at e
    cases e
  · intro v nxt u r v' _ hv
    exact False.elim hv

end Rounds

theorem router_obs_of_valid {K K' : Nat} {t : Router K} {t' : Router K'} {i : Fin (K + 1)}
    {i' : Fin (K' + 1)}
    (h : WithGuardedTablePacking.Valid (t.entered_typed i).hasType (t'.entered_typed i').hasType) (g : Bool) :
    t.observations i g = t'.observations i' g := by
  have eq := h J M (fun _ _ => ⟨rfl, rfl⟩)
  unfold Router.observations denoteSingletonRegion
  rw [eq]

theorem router_obs_of_eqv {K K' : Nat} {t : Router K} {t' : Router K'} {i : Fin (K + 1)}
    {i' : Fin (K' + 1)} (e : PEqv false [State] (t.entered i) (t'.entered i') [Bit]) (g : Bool) :
    t.observations i g = t'.observations i' g :=
  router_obs_of_valid (WithGuardedTablePacking.WithPhaseUniformity.valid_of_eqv false e _ _) g

/-! ## The hub and the spread table -/

abbrev hubSpread (x : Fin 4) (y : Fin 6) : Prop :=
  (x = 0 ∧ y = 0) ∨ (x = 1 ∧ y = 1) ∨ (x = 2 ∧ y = 2) ∨ (x = 3 ∧ y = 3) ∨ (x = 0 ∧ y = 4) ∨ (x = 3 ∧ y = 5)

theorem hubSpread_label (a b c d : Bool) (x : Fin 4) (y : Fin 6) (r : hubSpread x y) :
    hubLabel a b c d x = spreadLabel a b c d y := by
  rcases r with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

theorem hubSpread_act (x : Fin 4) (y : Fin 6) (r : hubSpread x y) (tag pl : Bool) :
    Act.Rel hubSpread (hubAct x tag pl) (spreadAct false y tag pl) := by
  rcases r with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    cases tag <;> cases pl <;> decide

/-- The hub's run along `hubWord` returns `false`. -/
theorem hub_trace (a b c d g : Bool) :
    (Except.ok (bit false), hubWord a d g) ∈ (Router.ofLabels (hubLabel a b c d) hubAct).observations 0 g :=
  (router_unfold (hubLabel a b c d) hubAct 0 g _ _).2 ⟨true, true, _, rfl,
    show (_, _) ∈ (Router.ofLabels (hubLabel a b c d) hubAct).observations 3 false from
      (router_unfold (hubLabel a b c d) hubAct 3 false _ _).2 ⟨true, false, _, rfl,
        show (_, _) ∈ (Router.ofLabels (hubLabel a b c d) hubAct).observations 0 false from
          (router_unfold (hubLabel a b c d) hubAct 0 false _ _).2 ⟨false, false, 1, rfl, ⟨rfl, rfl⟩⟩⟩⟩

/-- The variant's run along the same word returns `true`. -/
theorem spread_trace (a b c d g : Bool) :
    (Except.ok (bit true), hubWord a d g) ∈
      (Router.ofLabels (spreadLabel a b c d) (spreadAct true)).observations 0 g :=
  (router_unfold (spreadLabel a b c d) (spreadAct true) 0 g _ _).2 ⟨true, true, _, rfl,
    show (_, _) ∈ (Router.ofLabels (spreadLabel a b c d) (spreadAct true)).observations 3 false from
      (router_unfold (spreadLabel a b c d) (spreadAct true) 3 false _ _).2 ⟨true, false, _, rfl,
        show (_, _) ∈ (Router.ofLabels (spreadLabel a b c d) (spreadAct true)).observations 4 false from
          (router_unfold (spreadLabel a b c d) (spreadAct true) 4 false _ _).2
            ⟨false, false, 1, rfl, ⟨rfl, rfl⟩⟩⟩⟩

/-- The variant has no run along that word that returns `false`. -/
theorem hub_trace_not_spread (a b c d g : Bool) :
    (Except.ok (bit false), hubWord a d g) ∉
      (Router.ofLabels (spreadLabel a b c d) (spreadAct true)).observations 0 g := by
  intro h
  obtain ⟨t0, p0, v0, e, hc⟩ := (router_unfold (spreadLabel a b c d) (spreadAct true) 0 g _ _).1 h
  obtain ⟨ev, rfl⟩ := word_cons e
  obtain ⟨-, -, rfl, rfl⟩ := event_inj ev
  have h1 : (_, _) ∈ (Router.ofLabels (spreadLabel a b c d) (spreadAct true)).observations 3 false := hc
  obtain ⟨t1, p1, v1, e, hc⟩ := (router_unfold (spreadLabel a b c d) (spreadAct true) 3 false _ _).1 h1
  obtain ⟨ev, rfl⟩ := word_cons e
  obtain ⟨-, -, rfl, rfl⟩ := event_inj ev
  have h2 : (_, _) ∈ (Router.ofLabels (spreadLabel a b c d) (spreadAct true)).observations 4 false := hc
  obtain ⟨t2, p2, v2, e, hc⟩ := (router_unfold (spreadLabel a b c d) (spreadAct true) 4 false _ _).1 h2
  obtain ⟨ev, rfl⟩ := word_cons e
  obtain ⟨-, -, rfl, rfl⟩ := event_inj ev
  have bad : (Except.ok (bit false) : Except Bool (value Bit)) = .ok (bit true) ∧ (1 : Word) = 1 := hc
  cases bad.1

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.TableModel

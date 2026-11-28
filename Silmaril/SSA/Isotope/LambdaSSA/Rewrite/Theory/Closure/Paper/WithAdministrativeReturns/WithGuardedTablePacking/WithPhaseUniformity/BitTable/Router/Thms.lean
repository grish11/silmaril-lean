module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Router.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Switch.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.RouterReflection

/-! # Replay and completeness for arbitrary routing of the four replies

No seed is added. Default Paper, `WithGuardedTablePacking` and
`WithPhaseUniformity` are unchanged.

## The rows

A router row runs a written program and inspects its whole packed result
by literal case splits. Each of the four results has its own action:
return a chosen Bit, or continue at a chosen state with a chosen query.
For a row of one labelled request, `act i tag pl` is the action on the
reply `(tag, pl)`. The returned Bit and the next query need not be the
reply payload. A row may send its replies to up to four different states.

## Replay, for arbitrary row programs

* `Router.quotient_eqv`, `Router.tail_arrow` (default Paper),
  `Router.morphism_eqv`: a state map that preserves row programs and
  renames the targets of all four actions identifies the entered loops.
  The row square is assembled from the squares of the case splits and
  fed to the dispatcher square of `dispatch_quotient_eqv`.
* `Router.bisimilar_eqv`, `Router.bisimulation_eqv`: bisimilar states of
  one table, and any bisimulation between two tables. A bisimulation
  preserves the row program, the returned Bit of every returning reply
  and the next query and target class of every other reply.

## The observation law

`Router.observations_unfold`: a complete run is one event followed by
what the action of its reply allows: nothing after a return, with that
Bit as the result, or a complete run of the target at the chosen query.

## Completeness, for live tables of labelled requests

A table is live when every state has a complete run for every query.
`Router.live_of_ret`: a returning reply at every state is enough. If the
first table is live, these are equivalent for any entries
(`Router.labels_eqv_iff_bisimulation`, `Router.labels_eqv_iff_valid`,
`Router.labels_eqv_iff_observations`):

* the entered loops are equal in `WithPhaseUniformity`,
* they are valid in every supported model,
* they have the same complete runs in the four-reply interpreter,
* some relation that preserves labels and all four actions relates them.

The converse cancels the first event (`Router.observations_act`). A
return against a jump is told apart because a complete run is never
empty, two returns by their Bit, and two jumps by the first event of the
target, which shows the label and the query (`Router.observations_head`).
Replay from a bisimulation needs no liveness.

## Liveness cannot be dropped for complete runs

`Router.observations_empty`: a table without returning replies has no
complete run. `dead_observations`, `dead_no_bisimulation`: two one-state
tables whose every reply repeats, with different labels, have the same
complete runs and are not bisimilar. So complete runs do not reflect
bisimulation at dead states. The two loops are separated in
`BitTable/Router/Prefix/Thms.lean`, with the request-prefix model, where
the liveness hypothesis is also removed.

## Regression

`hub_eqv_spread`: a four-state table whose first row returns on one
reply and sends the other three to three different states, against six
states with other wiring. `hub_ne_spread`: a variant that returns
another Bit at one copy differs. The distinguishing complete run is
explicit: `hub_trace` has three requests and returns `false`, the variant
returns `true` along the same word (`spread_trace`) and has no run along
it that returns `false` (`hub_trace_not_spread`).

## Not proved

* The converse for rows that are not single labelled requests. Tables
  that are not live are handled in `BitTable/Router/Prefix/Thms.lean`.
* Rows with several requests per round, and the relay rows.
* Nothing is claimed about packed dispatchers in general. The interpreter
  is used for the converse and for separation only.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory (ofRegion)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery (signature Trace)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree (Word event)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli (value)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit bit)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity

variable {K K' K₁ K₂ P : Nat}

/-! ## Replay -/

/-- A router table equals its quotient by a surjective class map. -/
theorem Router.quotient_eqv (s : Router K) (t : Router K') (cls : Fin (K + 1) → Fin (K' + 1))
    (surj : Function.Surjective cls) (hprog : ∀ i, s.prog i = t.prog (cls i))
    (hact : ∀ i x b, t.act (cls i) x b = (s.act i x b).map cls) (i : Fin (K + 1)) :
    Eqv false [State] (s.entered i) (t.entered (cls i)) [Bit] :=
  Tables.router_quotient_eqv s t cls surj hprog hact i

/-- A table at the tail of another one, closed under its actions, has the
same entered loops as arrows of default Paper. -/
theorem Router.tail_arrow (w : Router (K + (P + 1))) (s : Router K)
    (hprog : ∀ j, s.prog j = w.prog (tailIdx P j))
    (hact : ∀ j x b, w.act (tailIdx P j) x b = (s.act j x b).map (tailIdx P)) (j : Fin (K + 1)) :
    ofRegion (s.entered_typed j) = ofRegion (w.entered_typed (tailIdx P j)) :=
  Tables.router_tail_arrow w s hprog hact j

/-- Any map of states that preserves row programs and renames the targets
of all four actions identifies the entered loops. -/
theorem Router.morphism_eqv (s : Router K) (t : Router P) (ρ : Fin (K + 1) → Fin (P + 1))
    (hprog : ∀ j, s.prog j = t.prog (ρ j)) (hact : ∀ j x b, t.act (ρ j) x b = (s.act j x b).map ρ)
    (j : Fin (K + 1)) : Eqv false [State] (s.entered j) (t.entered (ρ j)) [Bit] :=
  Tables.router_morphism_eqv s t ρ hprog hact j

/-- Bisimilar states of one table. -/
theorem Router.bisimilar_eqv (t : Router K) (x y : Fin (K + 1)) (h : t.Bisimilar t x y) :
    Eqv false [State] (t.entered x) (t.entered y) [Bit] :=
  Tables.router_self_eqv t x y h

/-- Replay from a bisimulation between two tables. -/
theorem Router.bisimulation_eqv (t₁ : Router K₁) (t₂ : Router K₂) (R : Fin (K₁ + 1) → Fin (K₂ + 1) → Prop)
    (bis : Router.Bisimulation t₁ t₂ R) (i₁ : Fin (K₁ + 1)) (i₂ : Fin (K₂ + 1)) (r : R i₁ i₂) :
    Eqv false [State] (t₁.entered i₁) (t₂.entered i₂) [Bit] :=
  Tables.router_bisimulation_eqv t₁ t₂ R bis i₁ i₂ r

/-! ## The fixed interpreter -/

/-- One step at state `i`: the step of the row's program, then its routing. -/
theorem Router.step_run (t : Router K) (i : Fin (K + 1)) (s : value State) :
    t.stepM (injVal K i s) = Bind.bind (m := Trace) (stepModel (t.prog i) s) (routerRouteVal K (t.act i)) :=
  TableModel.router_step_run t i s

section Labels

variable (label₁ : Fin (K₁ + 1) → Bool) (act₁ : Fin (K₁ + 1) → Bool → Bool → Act K₁)
  (label₂ : Fin (K₂ + 1) → Bool) (act₂ : Fin (K₂ + 1) → Bool → Bool → Act K₂)
  (i₁ : Fin (K₁ + 1)) (i₂ : Fin (K₂ + 1))

/-- The observation law. -/
theorem Router.observations_unfold (g : Bool) (r : Except Bool (value Bit)) (w : Word) :
    (r, w) ∈ (Router.ofLabels label₁ act₁).observations i₁ g ↔
      ∃ tag pl v, w = FreeMonoid.of (event (label₁ i₁) g (tag, pl)) * v ∧
        (Router.ofLabels label₁ act₁).Cont (act₁ i₁ tag pl) r v :=
  TableModel.router_unfold label₁ act₁ i₁ g r w

/-- A returning reply at every state makes every state live. -/
theorem Router.live_of_ret (h : ∀ i, ∃ tag pl c, act₁ i tag pl = .ret c) (i : Fin (K₁ + 1)) (g : Bool) :
    ((Router.ofLabels label₁ act₁).observations i g).Nonempty :=
  TableModel.router_live_of_ret label₁ act₁ h i g

/-- A table without returning replies has no complete run. -/
theorem Router.observations_empty (h : ∀ i tag pl, ∃ j q, act₁ i tag pl = .go j q) (i : Fin (K₁ + 1))
    (g : Bool) : (Router.ofLabels label₁ act₁).observations i g = ∅ :=
  TableModel.router_dead label₁ act₁ h i g

/-- The first event of a complete run shows the label and the query. -/
theorem Router.observations_head (g g' : Bool)
    (live : ((Router.ofLabels label₁ act₁).observations i₁ g).Nonempty)
    (h : (Router.ofLabels label₁ act₁).observations i₁ g = (Router.ofLabels label₂ act₂).observations i₂ g') :
    label₁ i₁ = label₂ i₂ ∧ g = g' :=
  TableModel.router_head label₁ act₁ label₂ act₂ i₁ i₂ g g' live h

/-- Equal complete runs give matching actions on every reply. -/
theorem Router.observations_act (live : ∀ j q, ((Router.ofLabels label₁ act₁).observations j q).Nonempty)
    (g : Bool) (hl : label₁ i₁ = label₂ i₂)
    (h : (Router.ofLabels label₁ act₁).observations i₁ g = (Router.ofLabels label₂ act₂).observations i₂ g)
    (tag pl : Bool) :
    Act.Rel (fun j j' => ∃ q, (Router.ofLabels label₁ act₁).observations j q =
      (Router.ofLabels label₂ act₂).observations j' q) (act₁ i₁ tag pl) (act₂ i₂ tag pl) :=
  TableModel.router_act_rel label₁ act₁ label₂ act₂ live i₁ i₂ g hl h tag pl

/-! ## Completeness for live tables of labelled requests -/

/-- Replay from a relation that preserves labels and all four actions.
No liveness is needed. -/
theorem Router.labels_eqv_of_bisimulation (R : Fin (K₁ + 1) → Fin (K₂ + 1) → Prop)
    (hl : ∀ x y, R x y → label₁ x = label₂ y)
    (ha : ∀ x y, R x y → ∀ tag pl, Act.Rel R (act₁ x tag pl) (act₂ y tag pl)) (r : R i₁ i₂) :
    Eqv false [State] ((Router.ofLabels label₁ act₁).entered i₁) ((Router.ofLabels label₂ act₂).entered i₂)
      [Bit] :=
  TableModel.router_eqv_of_bisim label₁ act₁ label₂ act₂ R hl ha i₁ i₂ r

variable (live : ∀ j q, ((Router.ofLabels label₁ act₁).observations j q).Nonempty)

include live

/-- The entered loops are equal exactly when a bisimulation relates the
entries. -/
theorem Router.labels_eqv_iff_bisimulation :
    Eqv false [State] ((Router.ofLabels label₁ act₁).entered i₁) ((Router.ofLabels label₂ act₂).entered i₂)
        [Bit] ↔
      ∃ R : Fin (K₁ + 1) → Fin (K₂ + 1) → Prop, (∀ x y, R x y → label₁ x = label₂ y) ∧
        (∀ x y, R x y → ∀ tag pl, Act.Rel R (act₁ x tag pl) (act₂ y tag pl)) ∧ R i₁ i₂ :=
  ⟨fun e => TableModel.router_bisim_of_obs label₁ act₁ label₂ act₂ live i₁ i₂
      (TableModel.router_obs_of_eqv e false),
    fun ⟨R, hl, ha, r⟩ => TableModel.router_eqv_of_bisim label₁ act₁ label₂ act₂ R hl ha i₁ i₂ r⟩

/-- Exactly when the complete runs in the four-reply interpreter agree. -/
theorem Router.labels_eqv_iff_observations :
    Eqv false [State] ((Router.ofLabels label₁ act₁).entered i₁) ((Router.ofLabels label₂ act₂).entered i₂)
        [Bit] ↔
      (Router.ofLabels label₁ act₁).observations i₁ false = (Router.ofLabels label₂ act₂).observations i₂ false :=
  ⟨fun e => TableModel.router_obs_of_eqv e false,
    fun o => (Router.labels_eqv_iff_bisimulation label₁ act₁ label₂ act₂ i₁ i₂ live).2
      (TableModel.router_bisim_of_obs label₁ act₁ label₂ act₂ live i₁ i₂ o)⟩

/-- Exactly when they are valid in every supported model. -/
theorem Router.labels_eqv_iff_valid :
    Eqv false [State] ((Router.ofLabels label₁ act₁).entered i₁) ((Router.ofLabels label₂ act₂).entered i₂)
        [Bit] ↔
      Valid ((Router.ofLabels label₁ act₁).entered_typed i₁).hasType
        ((Router.ofLabels label₂ act₂).entered_typed i₂).hasType :=
  ⟨fun e => valid_of_eqv false e _ _,
    fun v => (Router.labels_eqv_iff_observations label₁ act₁ label₂ act₂ i₁ i₂ live).2
      (TableModel.router_obs_of_valid v false)⟩

end Labels

/-! ## Dead states -/

/-- Two one-state tables whose every reply repeats have the same complete
runs, whatever their labels: none. -/
theorem dead_observations (l l' g : Bool) :
    (Router.ofLabels (fun _ => l) deadAct).observations 0 g =
      (Router.ofLabels (fun _ => l') deadAct).observations 0 g :=
  (TableModel.router_dead (fun _ => l) deadAct (fun _ _ pl => ⟨0, pl, rfl⟩) 0 g).trans
    (TableModel.router_dead (fun _ => l') deadAct (fun _ _ pl => ⟨0, pl, rfl⟩) 0 g).symm

/-- With different labels no label-preserving relation relates them. -/
theorem dead_no_bisimulation {l l' : Bool} (ne : l ≠ l') :
    ¬ ∃ R : Fin 1 → Fin 1 → Prop, (∀ x y, R x y → (fun _ : Fin 1 => l) x = (fun _ : Fin 1 => l') y) ∧ R 0 0 :=
  fun ⟨_, hl, r⟩ => ne (hl 0 0 r)

/-! ## The hub and the spread table -/

/-- The four-state table equals the six-state table at their entries. -/
theorem hub_eqv_spread (a b c d : Bool) :
    Eqv false [State] ((Router.ofLabels (hubLabel a b c d) hubAct).entered 0)
      ((Router.ofLabels (spreadLabel a b c d) (spreadAct false)).entered 0) [Bit] :=
  TableModel.router_eqv_of_bisim (hubLabel a b c d) hubAct (spreadLabel a b c d) (spreadAct false)
    TableModel.hubSpread (TableModel.hubSpread_label a b c d) TableModel.hubSpread_act 0 0 (.inl ⟨rfl, rfl⟩)

/-- The hub's run along `hubWord` returns `false`. -/
theorem hub_trace (a b c d g : Bool) :
    (Except.ok (bit false), hubWord a d g) ∈ (Router.ofLabels (hubLabel a b c d) hubAct).observations 0 g :=
  TableModel.hub_trace a b c d g

/-- The variant's run along the same word returns `true`. -/
theorem spread_trace (a b c d g : Bool) :
    (Except.ok (bit true), hubWord a d g) ∈
      (Router.ofLabels (spreadLabel a b c d) (spreadAct true)).observations 0 g :=
  TableModel.spread_trace a b c d g

/-- The variant has no run along that word that returns `false`. -/
theorem hub_trace_not_spread (a b c d g : Bool) :
    (Except.ok (bit false), hubWord a d g) ∉
      (Router.ofLabels (spreadLabel a b c d) (spreadAct true)).observations 0 g :=
  TableModel.hub_trace_not_spread a b c d g

/-- So the hub differs from the variant. -/
theorem hub_ne_spread (a b c d : Bool) :
    ¬ Eqv false [State] ((Router.ofLabels (hubLabel a b c d) hubAct).entered 0)
      ((Router.ofLabels (spreadLabel a b c d) (spreadAct true)).entered 0) [Bit] :=
  fun e => hub_trace_not_spread a b c d false
    ((Set.ext_iff.1 (TableModel.router_obs_of_eqv e false) _).1 (hub_trace a b c d false))

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable

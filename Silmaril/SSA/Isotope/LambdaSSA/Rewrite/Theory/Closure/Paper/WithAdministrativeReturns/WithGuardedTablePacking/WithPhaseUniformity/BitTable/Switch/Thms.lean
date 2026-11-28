module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Switch.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Bisimulation.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.SwitchReflection

/-! # Replay and completeness for tables whose successor depends on the reply

No seed is added. Default Paper, `WithGuardedTablePacking` and
`WithPhaseUniformity` are unchanged.

## The rows

A switch row runs a written program and routes its packed result by two
literal case splits: a returned `true` leaves, a returned `false`
continues at one successor, a repeat continues at another. For a poll the
four replies of its one request are split as follows.

* returning tag, payload `true`: the run ends with `true`;
* returning tag, payload `false`: successor `next i false`, next query `false`;
* repeating tag, payload `pl`: successor `next i true`, next query `pl`.

So every state has a terminating reply and two independently chosen
successors. The interface has no third successor and no terminating reply
that returns `false`: a row has one request and four replies.

## Replay, for arbitrary row programs

* `dispatch_quotient_eqv`: for dispatchers of any rows, a surjective
  class map with one default-Paper square per row identifies the entered
  loops. Onto one state this is the seed's fold, onto more it is
  `class_fold_uniform`.
* `Switch.quotient_eqv`, `Switch.tail_arrow`, `Switch.morphism_eqv`: the
  quotient, the removal of unreachable front states in default Paper, and
  hence any state map that preserves row programs and both successors.
* `Switch.tree_eqv`, `Switch.bisim_eqv`, `Switch.bisimulation_eqv`:
  states that run the same programs along every word of successor
  choices, in one table or in two, and any bisimulation.

## Completeness, for tables of written polls

For two such tables and any entries these are equivalent
(`Switch.polls_eqv_iff`, `Switch.polls_eqv_iff_bisimulation`,
`Switch.polls_eqv_iff_valid`, `Switch.polls_eqv_iff_observations`):

* the entered loops are equal in `WithPhaseUniformity`,
* they are valid in every supported model,
* they have the same complete runs in the four-reply interpreter,
* the entries run the same poll after every word of successor choices,
* some relation that preserves polls and both successors relates them.

## The observation law

`Switch.observations_unfold`: a complete run either leaves after one
request, with the returning tag and payload `true`, or starts with the
event of one of the two continuing replies followed by a complete run of
that successor. The converse reads a table from it:

* the run with one request shows the label and which tag returns
  (`Switch.observations_poll`);
* cancelling the first event gives the complete runs of each successor
  (`Switch.observations_step`). After a returned `false` only the query
  `false` is seen, so the relation used is equality of complete runs for
  some query.

## Regression

`tri_eqv_wide`: three states, where state zero has two different
successors running different polls, against six states with other wiring.
`tri_ne_wide`: with another poll at state four the tables differ.
`wide_only`: they then still agree on every word of length at most three
except `false, false, false`.

## Not proved

* The converse for rows that are not written polls. Replay holds for all
  programs; rows that spell a poll with other syntax are not exchanged
  here.
* Other reply splits are not handled here. Arbitrary routing of the four
  replies is in `BitTable/Router/Thms.lean`. The relay rows are not
  instances.
* No explicit separating run is constructed. The converse shows that the
  sets of complete runs differ.
* The interpreter is used for the converse only. No equation is inferred
  from it, and nothing is claimed about packed dispatchers in general.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory (ofType ofRegion sumIso classFold)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery (signature Trace)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree (Word event)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli (value)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit bit)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity

variable {K K' K₁ K₂ P : Nat}

/-! ## Dispatchers of any rows -/

/-- A surjective class map with one default-Paper square per row
identifies the entered loops of two dispatchers. -/
theorem dispatch_quotient_eqv {rows : Fin (K + 1) → Region signature.Instr}
    {rows' : Fin (K' + 1) → Region signature.Instr}
    (h : ∀ i, ValueBranches [State] (rows i) [Silmaril.coprod Bit (States K)])
    (h' : ∀ i, ValueBranches [State] (rows' i) [Silmaril.coprod Bit (States K')])
    (cls : Fin (K + 1) → Fin (K' + 1)) (surj : Function.Surjective cls)
    (row : ∀ i, (ofRegion (h i) ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom) ≫
        coprod.map (𝟙 _) (classFold State cls) =
      ofRegion (h' (cls i)) ≫ (sumIso (Φ := signature.Instr) Bit (States K')).hom) (i : Fin (K + 1)) :
    Eqv false [State] (dispatchEntered K rows i) (dispatchEntered K' rows' (cls i)) [Bit] :=
  Tables.dispatch_quotient h h' cls surj row i

/-! ## Replay -/

/-- A switch table equals its quotient by a surjective class map. -/
theorem Switch.quotient_eqv (t : Switch K) (t' : Switch K') (cls : Fin (K + 1) → Fin (K' + 1))
    (surj : Function.Surjective cls) (hprog : ∀ i, t.prog i = t'.prog (cls i))
    (hnext : ∀ i b, cls (t.next i b) = t'.next (cls i) b) (i : Fin (K + 1)) :
    Eqv false [State] (t.entered i) (t'.entered (cls i)) [Bit] :=
  Tables.switch_quotient_eqv t t' cls surj hprog hnext i

/-- A table at the tail of another one, closed under both successors, has
the same entered loops as arrows of default Paper. -/
theorem Switch.tail_arrow (w : Switch (K + (P + 1))) (s : Switch K)
    (hprog : ∀ j, s.prog j = w.prog (tailIdx P j))
    (hnext : ∀ j b, tailIdx P (s.next j b) = w.next (tailIdx P j) b) (j : Fin (K + 1)) :
    ofRegion (s.entered_typed j) = ofRegion (w.entered_typed (tailIdx P j)) :=
  Tables.switch_tail_arrow w s hprog hnext j

/-- Any map of states that preserves row programs and commutes with both
successors identifies the entered loops. -/
theorem Switch.morphism_eqv (s : Switch K) (t : Switch P) (ρ : Fin (K + 1) → Fin (P + 1))
    (hprog : ∀ j, s.prog j = t.prog (ρ j)) (hnext : ∀ j b, ρ (s.next j b) = t.next (ρ j) b)
    (j : Fin (K + 1)) : Eqv false [State] (s.entered j) (t.entered (ρ j)) [Bit] :=
  Tables.switch_morphism_eqv s t ρ hprog hnext j

/-- Two states of one table that run the same programs along every word. -/
theorem Switch.tree_eqv (t : Switch K) (x y : Fin (K + 1))
    (h : ∀ w, t.prog (t.walk x w) = t.prog (t.walk y w)) :
    Eqv false [State] (t.entered x) (t.entered y) [Bit] :=
  Tables.switch_tree_eqv t x y h

/-- Entries of two tables that run the same programs along every word. -/
theorem Switch.bisim_eqv (t₁ : Switch K₁) (t₂ : Switch K₂) (i₁ : Fin (K₁ + 1)) (i₂ : Fin (K₂ + 1))
    (h : ∀ w, t₁.prog (t₁.walk i₁ w) = t₂.prog (t₂.walk i₂ w)) :
    Eqv false [State] (t₁.entered i₁) (t₂.entered i₂) [Bit] :=
  Tables.switch_bisim_eqv t₁ t₂ i₁ i₂ h

/-- Replay from a bisimulation. -/
theorem Switch.bisimulation_eqv (t₁ : Switch K₁) (t₂ : Switch K₂) (R : Fin (K₁ + 1) → Fin (K₂ + 1) → Prop)
    (bis : Switch.Bisimulation t₁ t₂ R) (i₁ : Fin (K₁ + 1)) (i₂ : Fin (K₂ + 1)) (r : R i₁ i₂) :
    Eqv false [State] (t₁.entered i₁) (t₂.entered i₂) [Bit] :=
  Tables.switch_bisimulation_eqv t₁ t₂ R bis i₁ i₂ r

/-! ## The fixed interpreter -/

/-- One step at state `i`: the step of the row's program, then its routing. -/
theorem Switch.step_run (t : Switch K) (i : Fin (K + 1)) (s : value State) :
    t.stepM (injVal K i s) =
      Bind.bind (m := Trace) (stepModel (t.prog i) s) (switchRouteVal K (t.next i false) (t.next i true)) :=
  TableModel.switch_step_run t i s

section Polls

variable (poll₁ : Fin (K₁ + 1) → Poll) (next₁ : Fin (K₁ + 1) → Bool → Fin (K₁ + 1))
  (poll₂ : Fin (K₂ + 1) → Poll) (next₂ : Fin (K₂ + 1) → Bool → Fin (K₂ + 1))
  (i₁ : Fin (K₁ + 1)) (i₂ : Fin (K₂ + 1))

/-- The observation law of a table of polls. -/
theorem Switch.observations_unfold (g : Bool) (r : Except Bool (value Bit)) (w : Word) :
    (r, w) ∈ (Switch.ofPolls poll₁ next₁).observations i₁ g ↔
      (r = .ok (bit true) ∧ w = FreeMonoid.of (event (poll₁ i₁).label g ((poll₁ i₁).returnRight, true))) ∨
      (∃ v, (r, v) ∈ (Switch.ofPolls poll₁ next₁).observations (next₁ i₁ false) false ∧
        w = FreeMonoid.of (event (poll₁ i₁).label g ((poll₁ i₁).returnRight, false)) * v) ∨
      (∃ pl v, (r, v) ∈ (Switch.ofPolls poll₁ next₁).observations (next₁ i₁ true) pl ∧
        w = FreeMonoid.of (event (poll₁ i₁).label g (!(poll₁ i₁).returnRight, pl)) * v) :=
  TableModel.switch_unfold poll₁ next₁ i₁ g r w

/-- Equal complete runs show the same poll. -/
theorem Switch.observations_poll (g : Bool)
    (h : (Switch.ofPolls poll₁ next₁).observations i₁ g = (Switch.ofPolls poll₂ next₂).observations i₂ g) :
    poll₁ i₁ = poll₂ i₂ :=
  TableModel.switch_obs_poll poll₁ next₁ poll₂ next₂ i₁ i₂ g h

/-- Equal complete runs give equal complete runs at both successors. -/
theorem Switch.observations_step (g : Bool)
    (h : (Switch.ofPolls poll₁ next₁).observations i₁ g = (Switch.ofPolls poll₂ next₂).observations i₂ g)
    (b : Bool) :
    ∃ g', (Switch.ofPolls poll₁ next₁).observations (next₁ i₁ b) g' =
      (Switch.ofPolls poll₂ next₂).observations (next₂ i₂ b) g' :=
  (TableModel.switch_obs_step poll₁ next₁ poll₂ next₂ i₁ i₂ g h).2 b

/-! ## Completeness for tables of written polls -/

/-- The entered loops are equal exactly when the entries run the same poll
after every word of successor choices. -/
theorem Switch.polls_eqv_iff :
    Eqv false [State] ((Switch.ofPolls poll₁ next₁).entered i₁) ((Switch.ofPolls poll₂ next₂).entered i₂)
        [Bit] ↔
      ∀ w, poll₁ ((Switch.ofPolls poll₁ next₁).walk i₁ w) = poll₂ ((Switch.ofPolls poll₂ next₂).walk i₂ w) :=
  ⟨fun e w => TableModel.switch_obs_walk poll₁ next₁ poll₂ next₂ w i₁ i₂
      ⟨false, TableModel.switch_obs_of_eqv e false⟩,
    TableModel.switch_eqv_of_polls poll₁ next₁ poll₂ next₂ i₁ i₂⟩

/-- Exactly when the complete runs in the four-reply interpreter agree. -/
theorem Switch.polls_eqv_iff_observations :
    Eqv false [State] ((Switch.ofPolls poll₁ next₁).entered i₁) ((Switch.ofPolls poll₂ next₂).entered i₂)
        [Bit] ↔
      (Switch.ofPolls poll₁ next₁).observations i₁ false = (Switch.ofPolls poll₂ next₂).observations i₂ false :=
  ⟨fun e => TableModel.switch_obs_of_eqv e false,
    fun o => TableModel.switch_eqv_of_polls poll₁ next₁ poll₂ next₂ i₁ i₂
      (fun w => TableModel.switch_obs_walk poll₁ next₁ poll₂ next₂ w i₁ i₂ ⟨false, o⟩)⟩

/-- Exactly when they are valid in every supported model. -/
theorem Switch.polls_eqv_iff_valid :
    Eqv false [State] ((Switch.ofPolls poll₁ next₁).entered i₁) ((Switch.ofPolls poll₂ next₂).entered i₂)
        [Bit] ↔
      Valid ((Switch.ofPolls poll₁ next₁).entered_typed i₁).hasType
        ((Switch.ofPolls poll₂ next₂).entered_typed i₂).hasType :=
  ⟨fun e => valid_of_eqv false e _ _,
    fun v => (Switch.polls_eqv_iff_observations poll₁ next₁ poll₂ next₂ i₁ i₂).2
      (TableModel.switch_obs_of_valid v false)⟩

/-- Exactly when a relation that preserves polls and both successors
relates the entries. -/
theorem Switch.polls_eqv_iff_bisimulation :
    Eqv false [State] ((Switch.ofPolls poll₁ next₁).entered i₁) ((Switch.ofPolls poll₂ next₂).entered i₂)
        [Bit] ↔
      ∃ R : Fin (K₁ + 1) → Fin (K₂ + 1) → Prop, (∀ x y, R x y → poll₁ x = poll₂ y) ∧
        (∀ x y, R x y → ∀ b, R (next₁ x b) (next₂ y b)) ∧ R i₁ i₂ :=
  ⟨fun e => TableModel.switch_bisim_of_obs poll₁ next₁ poll₂ next₂ i₁ i₂ (TableModel.switch_obs_of_eqv e false),
    fun ⟨R, hp, hn, r⟩ => TableModel.switch_eqv_of_polls poll₁ next₁ poll₂ next₂ i₁ i₂
      (TableModel.switch_polls_of_bisim poll₁ next₁ poll₂ next₂ R hp hn i₁ i₂ r)⟩

end Polls

/-! ## Three states against six -/

/-- The three-state table equals the six-state table at their entries. -/
theorem tri_eqv_wide (a b c : Poll) :
    Eqv false [State] ((Switch.ofPolls (triPolls a b c) triNext).entered 0)
      ((Switch.ofPolls (widePolls a b c b) wideNext).entered 0) [Bit] :=
  (Switch.polls_eqv_iff (triPolls a b c) triNext (widePolls a b c b) wideNext 0 0).2
    (TableModel.tri_wide_polls a b c)

/-- With another poll at state four they differ. -/
theorem tri_ne_wide {a b c d : Poll} (other : b ≠ d) :
    ¬ Eqv false [State] ((Switch.ofPolls (triPolls a b c) triNext).entered 0)
      ((Switch.ofPolls (widePolls a b c d) wideNext).entered 0) [Bit] :=
  fun e => other
    ((Switch.polls_eqv_iff (triPolls a b c) triNext (widePolls a b c d) wideNext 0 0).1 e [false, false, false])

/-- The difference is on one word only, among the words of length at most
three. -/
theorem wide_only (a b c d : Poll) (w : List Bool) (short : w.length ≤ 3) (ne : w ≠ [false, false, false]) :
    triPolls a b c ((Switch.ofPolls (triPolls a b c) triNext).walk 0 w) =
      widePolls a b c d ((Switch.ofPolls (widePolls a b c d) wideNext).walk 0 w) :=
  TableModel.wide_only a b c d w short ne

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable

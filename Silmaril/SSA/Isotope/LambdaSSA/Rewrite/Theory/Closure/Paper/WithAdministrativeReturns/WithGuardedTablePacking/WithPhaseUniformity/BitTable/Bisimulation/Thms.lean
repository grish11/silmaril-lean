module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Bisimulation.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Quotient.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.TableKeys

/-! # Replay from bisimulation, and completeness for tables of polls

No seed is added. Everything here is derived in the unchanged
`WithPhaseUniformity`, or already in `WithGuardedTablePacking` or
default Paper where stated.

## Replay, for arbitrary row programs

* `Table.tail_arrow`: a table that sits at the tail of a larger one and
  is closed under successors has the same entered loops. The states in
  front are arbitrary, so this removes unreachable states. It is an
  equation of default Paper, because the embedding is constructor-valued.
* `Table.morphism_eqv`: any map of states that preserves row programs and
  commutes with successors identifies the entered loops. It need not be
  surjective. The proof maps the disjoint union onto the target by
  `Table.quotient_eqv` and removes the front by `Table.tail_arrow`.
* `Table.bisim_eqv`: entries of two tables with equal streams of row
  programs are equal. Inside one table (`Table.stream_eqv`) every
  successor is sent to a chosen representative of its stream class, which
  is a morphism onto `Table.minimized`. Two tables are compared inside
  their disjoint union.
* `Table.rows_eqv`: rows with equal reflected tree keys may be exchanged,
  already in `WithGuardedTablePacking`.
* `Table.key_bisim_eqv`, `Table.key_bisimulation_eqv`: hence equal
  streams of row keys, or any relation that preserves row keys and
  successors, give equal entered loops.

## Completeness, for tables whose rows spell polls

For two such tables and any entries, these are equivalent
(`Table.polls_eqv_iff`, `Table.polls_eqv_iff_keys`,
`Table.polls_eqv_iff_valid`, `Table.polls_eqv_iff_observations`):

* the entered loops are equal in `WithPhaseUniformity`,
* they are valid in every supported model,
* they have the same complete runs in the four-reply interpreter,
* the two entries run the same poll in every round, that is, the same
  row key in every round.

The converse uses finite runs only. `Table.runWord_mem`: the run that
repeats `n` times and then returns is a complete run. `Table.observation_trail`:
every complete run has one event per round with that round's label, and
its reply tag tells a return from a repeat. A difference in round `n` is
therefore seen by a run with `n + 1` requests.

## Regression

`ring_eqv_lasso`: a ring `a b a b` against a table with a transient
state, a two-state cycle and an unreachable state running a third poll.
Neither is a quotient of the other and the tables have two reachable row
keys. `ring_ne_lasso`: with another poll in the cycle the tables differ.
The first two rounds agree (`ring_lasso_prefix`) and the separating run
has three requests (`ring_lasso_witness`, `ring_lasso_not_mem`).

## Not proved

* The converse for rows that are not polls. A row that cannot repeat hides
  every later round, so equal behaviour does not give equal streams. No
  completeness is claimed there.
* Rows with several successors are not handled here. Reply-dependent
  successors are in `BitTable/Switch/Thms.lean`. The relay rows and packed
  dispatchers in general are not covered.
* The interpreter is used for the converse and for separation only. No
  equation is inferred from it.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory (ofRegion)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery (signature Event)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree (Word)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli (value)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit bit)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity

variable {K K₁ K₂ P : Nat}

/-! ## Morphisms and unreachable states -/

/-- A table at the tail of another one, closed under successors, has the
same entered loops as arrows of default Paper. -/
theorem Table.tail_arrow (w : Table (K + (P + 1))) (s : Table K)
    (hprog : ∀ j, s.prog j = w.prog (tailIdx P j)) (hnext : ∀ j, tailIdx P (s.next j) = w.next (tailIdx P j))
    (j : Fin (K + 1)) :
    ofRegion (s.entered_typed j) = ofRegion (w.entered_typed (tailIdx P j)) :=
  Tables.tail_arrow w s hprog hnext j

/-- Any map of states that preserves row programs and commutes with
successors identifies the entered loops. -/
theorem Table.morphism_eqv (s : Table K) (t : Table P) (ρ : Fin (K + 1) → Fin (P + 1))
    (hprog : ∀ j, s.prog j = t.prog (ρ j)) (hnext : ∀ j, ρ (s.next j) = t.next (ρ j)) (j : Fin (K + 1)) :
    Eqv false [State] (s.entered j) (t.entered (ρ j)) [Bit] :=
  Tables.morphism_eqv s t ρ hprog hnext j

/-! ## Equal streams -/

/-- Two states of one table with equal streams. -/
theorem Table.stream_eqv (t : Table K) (x y : Fin (K + 1)) (h : ∀ n, t.stream x n = t.stream y n) :
    Eqv false [State] (t.entered x) (t.entered y) [Bit] :=
  Tables.stream_eqv t x y h

/-- Entries of two tables with equal streams of row programs. -/
theorem Table.bisim_eqv (t₁ : Table K₁) (t₂ : Table K₂) (i₁ : Fin (K₁ + 1)) (i₂ : Fin (K₂ + 1))
    (h : ∀ n, t₁.stream i₁ n = t₂.stream i₂ n) :
    Eqv false [State] (t₁.entered i₁) (t₂.entered i₂) [Bit] :=
  Tables.bisim_eqv t₁ t₂ i₁ i₂ h

/-! ## Row keys -/

/-- Rows with equal keys may be exchanged, already in
`WithGuardedTablePacking`. -/
theorem Table.rows_eqv (t t' : Table K) (hnext : ∀ i, t.next i = t'.next i)
    (hkey : ∀ i, (t.prog i).tree.key = (t'.prog i).tree.key) (i : Fin (K + 1)) :
    WithGuardedTablePacking.Eqv false [State] (t.entered i) (t'.entered i) [Bit] :=
  TableModel.rows_eqv t t' hnext hkey i

/-- Entries of two tables whose streams of row keys agree. -/
theorem Table.key_bisim_eqv (t₁ : Table K₁) (t₂ : Table K₂) (i₁ : Fin (K₁ + 1)) (i₂ : Fin (K₂ + 1))
    (h : ∀ n, (t₁.stream i₁ n).tree.key = (t₂.stream i₂ n).tree.key) :
    Eqv false [State] (t₁.entered i₁) (t₂.entered i₂) [Bit] :=
  TableModel.key_bisim_eqv t₁ t₂ i₁ i₂ h

/-- Replay from a bisimulation that preserves row keys and successors. -/
theorem Table.key_bisimulation_eqv (t₁ : Table K₁) (t₂ : Table K₂) (R : Fin (K₁ + 1) → Fin (K₂ + 1) → Prop)
    (hkey : ∀ x y, R x y → (t₁.prog x).tree.key = (t₂.prog y).tree.key)
    (hnext : ∀ x y, R x y → R (t₁.next x) (t₂.next y)) (i₁ : Fin (K₁ + 1)) (i₂ : Fin (K₂ + 1))
    (r : R i₁ i₂) : Eqv false [State] (t₁.entered i₁) (t₂.entered i₂) [Bit] :=
  TableModel.key_bisimulation_eqv t₁ t₂ R hkey hnext i₁ i₂ r

/-! ## Finite runs of a table of polls -/

/-- The run that repeats `n` times and then returns is a complete run. -/
theorem Table.runWord_mem (poll : Fin (K + 1) → Poll) (next : Fin (K + 1) → Fin (K + 1)) (n : Nat)
    (i : Fin (K + 1)) (g : Bool) :
    (Except.ok (bit false), Table.runWord poll next n i g) ∈ (Table.ofPolls poll next).observations i g :=
  TableModel.run_mem poll next n i g

/-- Every complete run has a trail as its request word. -/
theorem Table.observation_trail (poll : Fin (K + 1) → Poll) (next : Fin (K + 1) → Fin (K + 1))
    (i : Fin (K + 1)) (g : Bool) {obs : Except Bool (value Bit) × Word}
    (h : obs ∈ (Table.ofPolls poll next).observations i g) :
    Table.Trail poll next i (FreeMonoid.toList obs.2) :=
  TableModel.trail_of_obs poll next i g h

/-! ## Completeness for tables whose rows spell polls -/

section Polls

variable (t₁ : Table K₁) (t₂ : Table K₂) (poll₁ : Fin (K₁ + 1) → Poll) (poll₂ : Fin (K₂ + 1) → Poll)
  (h₁ : ∀ i, Spells (t₁.prog i) (poll₁ i)) (h₂ : ∀ i, Spells (t₂.prog i) (poll₂ i))
  (i₁ : Fin (K₁ + 1)) (i₂ : Fin (K₂ + 1))

include h₁ h₂

/-- The entered loops are equal exactly when the entries run the same
poll in every round. -/
theorem Table.polls_eqv_iff :
    Eqv false [State] (t₁.entered i₁) (t₂.entered i₂) [Bit] ↔
      ∀ n, poll₁ (t₁.next^[n] i₁) = poll₂ (t₂.next^[n] i₂) :=
  ⟨fun e => TableModel.polls_of_obs t₁ t₂ poll₁ poll₂ h₁ h₂ i₁ i₂ (TableModel.observations_of_eqv e false),
    TableModel.eqv_of_polls t₁ t₂ poll₁ poll₂ h₁ h₂ i₁ i₂⟩

/-- Exactly when the complete runs in the four-reply interpreter agree. -/
theorem Table.polls_eqv_iff_observations :
    Eqv false [State] (t₁.entered i₁) (t₂.entered i₂) [Bit] ↔
      t₁.observations i₁ false = t₂.observations i₂ false :=
  ⟨fun e => TableModel.observations_of_eqv e false,
    fun obs => TableModel.eqv_of_polls t₁ t₂ poll₁ poll₂ h₁ h₂ i₁ i₂
      (TableModel.polls_of_obs t₁ t₂ poll₁ poll₂ h₁ h₂ i₁ i₂ obs)⟩

/-- Exactly when they are valid in every supported model. -/
theorem Table.polls_eqv_iff_valid :
    Eqv false [State] (t₁.entered i₁) (t₂.entered i₂) [Bit] ↔
      Valid (t₁.entered_typed i₁).hasType (t₂.entered_typed i₂).hasType :=
  ⟨fun e => valid_of_eqv false e _ _,
    fun v => (Table.polls_eqv_iff_observations t₁ t₂ poll₁ poll₂ h₁ h₂ i₁ i₂).2
      (TableModel.observations_of_valid v false)⟩

/-- Exactly when the entries run the same row key in every round. -/
theorem Table.polls_eqv_iff_keys :
    Eqv false [State] (t₁.entered i₁) (t₂.entered i₂) [Bit] ↔
      ∀ n, (t₁.stream i₁ n).tree.key = (t₂.stream i₂ n).tree.key :=
  ⟨fun e n => (h₁ _).trans ((congrArg (fun a : Poll => a.program.tree.key)
      ((Table.polls_eqv_iff t₁ t₂ poll₁ poll₂ h₁ h₂ i₁ i₂).1 e n)).trans (h₂ _).symm),
    Table.key_bisim_eqv t₁ t₂ i₁ i₂⟩

end Polls

/-- The statement for tables of written polls. -/
theorem Table.ofPolls_eqv_iff (poll₁ : Fin (K₁ + 1) → Poll) (next₁ : Fin (K₁ + 1) → Fin (K₁ + 1))
    (poll₂ : Fin (K₂ + 1) → Poll) (next₂ : Fin (K₂ + 1) → Fin (K₂ + 1)) (i₁ : Fin (K₁ + 1))
    (i₂ : Fin (K₂ + 1)) :
    Eqv false [State] ((Table.ofPolls poll₁ next₁).entered i₁) ((Table.ofPolls poll₂ next₂).entered i₂) [Bit] ↔
      ∀ n, poll₁ (next₁^[n] i₁) = poll₂ (next₂^[n] i₂) :=
  Table.polls_eqv_iff (Table.ofPolls poll₁ next₁) (Table.ofPolls poll₂ next₂) poll₁ poll₂ (fun _ => rfl)
    (fun _ => rfl) i₁ i₂

/-! ## The ring and the lasso -/

/-- The ring `a b a b` equals the table with a transient state, a
two-state cycle and an unreachable state. -/
theorem ring_eqv_lasso (a b c : Poll) :
    Eqv false [State] ((Table.ofPolls (ringPolls a b) ringNext).entered 0)
      ((Table.ofPolls (lassoPolls a b c a) lassoNext).entered 0) [Bit] :=
  (Table.ofPolls_eqv_iff (ringPolls a b) ringNext (lassoPolls a b c a) lassoNext 0 0).2
    (TableModel.ring_lasso_polls a b c)

/-- With another poll in the cycle the first two rounds still agree. -/
theorem ring_lasso_prefix (a b c d : Poll) (n : Nat) (early : n < 2) :
    ringPolls a b (ringNext^[n] 0) = lassoPolls a b c d (lassoNext^[n] 0) := by
  match n, early with
  | 0, _ => rfl
  | 1, _ => rfl

/-- The tables differ when the poll in the cycle differs, in its label or
only in which reply returns. -/
theorem ring_ne_lasso {a b c d : Poll} (other : a ≠ d) :
    ¬ Eqv false [State] ((Table.ofPolls (ringPolls a b) ringNext).entered 0)
      ((Table.ofPolls (lassoPolls a b c d) lassoNext).entered 0) [Bit] :=
  fun e => other ((Table.ofPolls_eqv_iff (ringPolls a b) ringNext (lassoPolls a b c d) lassoNext 0 0).1 e 2)

/-- The separating run of the ring: two repeats and a return. -/
theorem ring_lasso_witness (a b : Poll) :
    (Except.ok (bit false), Table.runWord (ringPolls a b) ringNext 2 0 false) ∈
      (Table.ofPolls (ringPolls a b) ringNext).observations 0 false :=
  TableModel.run_mem (ringPolls a b) ringNext 2 0 false

/-- The variant has no such run. -/
theorem ring_lasso_not_mem {a b c d : Poll} (other : a ≠ d) :
    (Except.ok (bit false), Table.runWord (ringPolls a b) ringNext 2 0 false) ∉
      (Table.ofPolls (lassoPolls a b c d) lassoNext).observations 0 false :=
  fun mem => other (TableModel.poll_of_trail (ringPolls a b) ringNext (lassoPolls a b c d) lassoNext 2 0 0 false
    (TableModel.trail_of_obs (lassoPolls a b c d) lassoNext 0 false mem))

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable

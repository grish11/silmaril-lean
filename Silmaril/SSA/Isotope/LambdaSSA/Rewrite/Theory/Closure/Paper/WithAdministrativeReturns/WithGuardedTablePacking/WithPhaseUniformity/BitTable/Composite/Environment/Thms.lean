module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Environment.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Entry.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.BitFragment.Recursive.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.EnvRegression

/-! # Written rows with an environment, at the original entries

One proof for a fragment of written rows, in place of one proof for each
row. No seed is added. Nothing here is inferred from a model.

## The fragment

A row of the fragment is a first request on the entry state followed by a
finite schedule of requests that read their queries from an environment
of Bits: the entry state and the earlier replies. Leaves return or repeat
with a Bit of the environment.

* `labelPoll_eq_row`, `duoProgram_eq_row`, `capProgram_eq_row`,
  `entryProgram_eq_row`: the rows of the earlier files are rows of the
  fragment, as literal equalities.
* `Router.eqv_envRouter_of_normal`: written code with Bit lets, unit lets
  and constructor-known queries is covered through its normal form. A
  table of written programs whose normal forms are rows of the fragment
  equals the table of those rows at every entry. This is the existing
  normalization of written code, an equation of the administrative-return
  quotient. `letProgram_normal` is an instance.

## Literal equalities and default Paper

* `EnvRow.packed_const`: the packed written row entered with a constant
  is its schedule on that constant. A literal equality of regions.
* `LTable.matched_of_carries`: a table of literal request trees all of
  whose repeats carry the Bit of their target is `Matched`. An equation
  of default Paper.

## The opt-in quotient: specialization

* `bitVar_split`: the compositional specialization lemma. A region with a
  Bit variable above a unit variable is the case on the Bit of the region
  on each constant. It is the native case on a variable, and then unit η
  to build each constant on the unit payload of the case. It is used once
  for each request of a schedule.
* `envSpec_route_eqv`: a schedule on constants followed by a routing is
  its literal request tree. By induction on the schedule: a leaf reduces
  in default Paper, and a request is the labelled request followed by the
  routing of the schedules of its four replies.
* `EnvRow.const_eqv`: a written row entered with the constant `c` is the
  labelled row of its literal request trees entered with `c`.

## The opt-in quotient: the original entries

* `splitRouter_eqv`: the split of any router table, entered at a split
  state of row `j`, is the table entered at `j`. The router-morphism fold
  of #5273, which rests on the phase-uniformity seed.
* `envRouter_pointed`: the table of written rows entered with each
  constant is the split table of literal request trees entered with that
  constant. It uses the reset of #5273 on both tables.
* `envRouter_eqv_envCase`: the table on an arbitrary state is the split
  table entered by a case on that state.
* `envRouter_complete`, `envRouter_eqv_ltable_iff_valid`,
  `Router.complete_of_normal`: two tables of the fragment, a table of the
  fragment and literal request trees, or two tables of written code with
  normal forms in the fragment, are equal at given original entries
  exactly when they are valid in every supported model. These depend on
  phase uniformity, unit η and the request-prefix model. They are not
  statements about default Paper.

## Regression

`slotRow l₁ l₂ sL sR` returns slot `sL` after the second left reply and
slot `sR` after the second right reply, among the second reply, the first
reply and the entry state. Its repeat carries the negated Bit.

* `slotRouter_eqv_iff`: two such tables are equal exactly when both slots
  agree. So the row that reads the entry state on one reply and the first
  reply on the other is separated from every row that erases or exchanges
  either.
* `slotRouter_ne_frozen`: that row differs from the frozen table, whose
  repeats stay in their copy. The two agree until a repeat; the proof
  separates them after a repeat that changes the Bit.

## Scope

A row whose normal form is a return without a request is not a row of the
fragment; `Composite.Silent` treats such rows in mixed tables. The
environment holds Bits and the entry state is one Bit.
Nothing is claimed for packed dispatchers in general, and no completeness
is claimed for default Paper.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (seqValueBranches caseValueBranches)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory (ofRegion ofType)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery (signature)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking
  (Valid.symm Valid.trans)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity

open Silmaril.DeBruijn (lift)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.BitFragment.Recursive (Normal)

variable {K K₁ K₂ : Nat}

/-! ## The fragment -/

theorem labelPoll_eq_row (l : Bool) : (labelPoll l).program = (EnvRow.mk l (.ret 0 0) (.ret 1 0)).program := rfl

theorem duoProgram_eq_row (l₁ l₂ : Bool) :
    duoProgram l₁ l₂ = (EnvRow.mk l₁ (.ask l₂ 0 (.ret 0 0) (.ret 1 0)) (.ret 1 0)).program := rfl

theorem capProgram_eq_row (l₁ l₂ : Bool) :
    capProgram l₁ l₂ = (EnvRow.mk l₁ (.ask l₂ 0 (.ret 0 1) (.ret 1 0)) (.ret 1 0)).program := rfl

theorem entryProgram_eq_row (l₁ l₂ : Bool) :
    entryProgram l₁ l₂ = (EnvRow.mk l₁ (.ask l₂ 0 (.ret 0 2) (.ret 1 0)) (.ret 1 0)).program := rfl

/-- The row with lets normalizes to its row in the fragment. -/
theorem letProgram_normal (l₁ l₂ : Bool) : (letProgram l₁ l₂).normalize id = (letRow l₁ l₂).normal := rfl

/-- A table of written code whose normal forms are rows of the fragment
equals the table of those rows at every entry. -/
theorem Router.eqv_envRouter_of_normal (t : Router K) (row : Fin (K + 1) → EnvRow)
    (h : ∀ i, (t.prog i).normalize id = (row i).normal) (j : Fin (K + 1)) :
    Eqv false [State] (t.entered j) ((envRouter row t.act).entered j) [Bit] :=
  Tables.normal_table t row h j

/-! ## Literal equalities and default Paper -/

/-- The packed written row entered with a constant is its schedule on
that constant. -/
theorem EnvRow.packed_const (r : EnvRow) (g : Bool) :
    ((Region.br 0 (bitTm g)).lsubst fun _ => r.program.written.packExits.renameVars (lift Nat.succ)) =
      envSpec r.normal fun _ => g :=
  Tables.envCode_const r.normal g

/-- A table of literal request trees all of whose repeats carry the Bit
of their target is matched. In default Paper. -/
theorem LTable.matched_of_carries {M : Nat} (c : Fin (M + 1) → Bool) (t : LTable M)
    (h : ∀ x a b, (t.kids x a b).Carries c) : Matched c t.toTable.rows_typed :=
  Tables.ltable_matched c t h

/-! ## The opt-in quotient: specialization -/

/-- A region with a Bit variable above a unit variable is the case on the
Bit of the region on each constant. -/
theorem bitVar_split {D : Ty Empty} {X : Region signature.Instr} (h : ValueBranches [Bit, Ty.unit] X [D]) :
    Eqv false [Bit, Ty.unit] X (pairSplit (X.substVars (splitSubst false)) (X.substVars (splitSubst true)))
      [D] :=
  Tables.bit_split h

/-- A schedule on constants followed by a routing is its literal request
tree. -/
theorem envSpec_route_eqv (K : Nat) (a : Bool → Bool → Act K) {n : Nat} (c : Normal 2 n) (env : Fin n → Bool) :
    Eqv false [(Ty.unit : Ty Empty)]
      ((envSpec c env).lsubst fun _ => (routerRoute K a).renameVars (lift Nat.succ))
      (treeRegion K (envTree a c env).toTree) [Silmaril.coprod Bit (States K)] :=
  Tables.env_tree_eqv K a c env

/-- A written row entered with the constant `c` is the labelled row of
its literal request trees entered with `c`. -/
theorem EnvRow.const_eqv (K : Nat) (r : EnvRow) (a : Bool → Bool → Act K) (c : Bool) :
    Eqv false [(Ty.unit : Ty Empty)] (constEntry c (routerRow K r.program a))
      (constEntry c (genRow (labelPoll r.label).program fun x y => treeRegion K (r.kids a c x y).toTree))
      [Silmaril.coprod Bit (States K)] :=
  Tables.env_row_const_eqv K r a c

/-! ## The opt-in quotient: the original entries -/

/-- The split of any router table, entered at a split state of row `j`,
is the table entered at `j`. -/
theorem splitRouter_eqv (t : Router K) (j : Fin (K + 1)) (q : Bool) :
    Eqv false [State] ((splitRouter t).entered (splitIdx j q)) (t.entered j) [Bit] :=
  Tables.router_split_fold t j q

section Tables

variable (row : Fin (K + 1) → EnvRow) (act : Fin (K + 1) → Bool → Bool → Act K)

/-- The table of written rows entered with each constant is the split
table of literal request trees entered with that constant. -/
theorem envRouter_pointed (j : Fin (K + 1)) :
    Pointed ((envRouter row act).entered j) (fun _ => envSource row act) (splitIdx j) :=
  Tables.env_pointed row act j

/-- The table on an arbitrary state is the split table of literal request
trees entered by a case on that state. -/
theorem envRouter_eqv_envCase (j : Fin (K + 1)) :
    Eqv false [State] ((envRouter row act).entered j) (envCase row act j) [Bit] :=
  Tables.env_case_eqv row act j

end Tables

/-- A table of written code whose normal forms are rows of the fragment
is the split table of literal request trees at each constant. -/
theorem Router.pointed_of_normal (t : Router K) (row : Fin (K + 1) → EnvRow)
    (h : ∀ i, (t.prog i).normalize id = (row i).normal) (j : Fin (K + 1)) :
    Pointed (t.entered j) (fun _ => envSource row t.act) (splitIdx j) :=
  Tables.normal_pointed t row h j

/-- Two tables of the fragment are equal at given original entries
exactly when they are valid in every supported model. -/
theorem envRouter_complete (row : Fin (K₁ + 1) → EnvRow) (act : Fin (K₁ + 1) → Bool → Bool → Act K₁)
    (row' : Fin (K₂ + 1) → EnvRow) (act' : Fin (K₂ + 1) → Bool → Bool → Act K₂) (i₁ : Fin (K₁ + 1))
    (i₂ : Fin (K₂ + 1)) :
    Eqv false [State] ((envRouter row act).entered i₁) ((envRouter row' act').entered i₂) [Bit] ↔
      Valid ((envRouter row act).entered_typed i₁).hasType ((envRouter row' act').entered_typed i₂).hasType :=
  (envRouter_pointed row act i₁).complete (envRouter_pointed row' act' i₂)
    ((envRouter row act).entered_typed i₁) ((envRouter row' act').entered_typed i₂)

/-- The same against any table of literal request trees. -/
theorem envRouter_eqv_ltable_iff_valid (row : Fin (K₁ + 1) → EnvRow)
    (act : Fin (K₁ + 1) → Bool → Bool → Act K₁) (s : LTable K₂) (i₁ : Fin (K₁ + 1))
    (i₂ : Fin (K₂ + 1)) :
    Eqv false [State] ((envRouter row act).entered i₁) (s.entered i₂) [Bit] ↔
      Valid ((envRouter row act).entered_typed i₁).hasType (s.entered_typed i₂).hasType :=
  (envRouter_pointed row act i₁).complete
    (LTable.pointed_of_eqv (s.entered_typed i₂) s i₂ (Paper.Extension.Eqv.refl (s.entered_typed i₂).hasType))
    ((envRouter row act).entered_typed i₁) (s.entered_typed i₂)

/-- Two tables of written code whose normal forms are rows of the
fragment are equal at given original entries exactly when they are valid
in every supported model. -/
theorem Router.complete_of_normal (t : Router K₁) (row : Fin (K₁ + 1) → EnvRow)
    (h : ∀ i, (t.prog i).normalize id = (row i).normal) (t' : Router K₂) (row' : Fin (K₂ + 1) → EnvRow)
    (h' : ∀ i, (t'.prog i).normalize id = (row' i).normal) (i₁ : Fin (K₁ + 1)) (i₂ : Fin (K₂ + 1)) :
    Eqv false [State] (t.entered i₁) (t'.entered i₂) [Bit] ↔
      Valid (t.entered_typed i₁).hasType (t'.entered_typed i₂).hasType :=
  (t.pointed_of_normal row h i₁).complete (t'.pointed_of_normal row' h' i₂) (t.entered_typed i₁)
    (t'.entered_typed i₂)

/-! ## Regression -/

/-- Two rows give equal loops exactly when their final actions read the
same slots. -/
theorem slotRouter_eqv_iff (l₁ l₂ : Bool) (sL sR sL' sR' : Fin 3) :
    Eqv false [State] ((slotRouter l₁ l₂ sL sR).entered 0) ((slotRouter l₁ l₂ sL' sR').entered 0) [Bit] ↔
      sL = sL' ∧ sR = sR' :=
  Tables.slot_eqv_iff l₁ l₂ sL sR sL' sR'

/-- After a repeat the entry slot holds the Bit the repeat carried: the
row that reads its entry state and its first reply differs from the
frozen table. -/
theorem slotRouter_ne_frozen (l₁ l₂ : Bool) :
    ¬ Eqv false [State] ((slotRouter l₁ l₂ 2 1).entered 0) (slotFrozen l₁ l₂ 2 1) [Bit] :=
  Tables.slot_ne_frozen l₁ l₂

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable

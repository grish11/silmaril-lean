module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Written.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Silent.Diverge.Nested.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.BitFragment.Recursive.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.WrittenTables

/-! # Router tables of written programs, at their original entries

No seed is added. No equality of the quotient is inferred from a model.

## The syntactic condition, and why it always holds

`Router.Normalizes t row` says that the normal form of each written
program of `t` is the request schedule of the row `row i` of a mixed
table.

* `MixRow.ofNormal_normal`: every request schedule on one slot is the
  schedule of a row of a mixed table. A leaf is a request-free row; a
  schedule that starts with a request is a row of the environment
  fragment.
* `Router.normalizes_mixRows`: so every router table satisfies the
  condition, with the rows `t.mixRows` read from the normal forms. The
  existing normalizer `Code.normalize` is total on written programs, so
  no syntax of `Code 2 1` is left out: returns, unit lets, Bit lets, and
  requests with read or constructor-known queries.

## The transfer

* `Router.eqv_mixWritten_of_normalizes`: a table of written programs
  equals the mixed table of the rows it normalizes to, at every entry and
  on every state. The actions are the same functions, the rows have the
  same indices, and nothing is specialized: a request-free row keeps its
  action, its destination rows and the Bits it carries. The equation is
  the existing normalization of written code, in the administrative-return
  part of the opt-in quotient, applied row by row. It generalizes
  `Router.eqv_envRouter_of_normal`, which needed every row to start with
  a request.
* `Router.eqv_mixWritten`: the instance with `t.mixRows`.

## Landings and completeness

* `Router.slanded`: every entry of every router table has tidy landings:
  a returned Bit, or a tidy table of labelled rows and canonical silent
  rows entered at a labelled row or at a silent row.
* `Router.complete`: two router tables are equal at given original
  entries exactly when they are valid in every supported model. Nested
  requests, lets, request-free rows and silent cycles are all allowed.

These depend on phase uniformity, unit η and the query-aware model. They
are not statements about default Paper.

## Regression

`letStash l₁ l₂ s n f` has a written row with a Bit let, which captures
the first reply or, when `s`, the entry state, and sends a second, blind
request with the captured Bit; and a written request-free row with a unit
let, which is a silent cycle that negates the Bit when `f`.

* `letStash_normalizes`: it normalizes to `stashRow l₁ l₂ s`.
* `letStash_eqv_stash`: it equals the mixed table of those rows at both
  entries.
* `letStash_eqv`: extensionally equivalent presentations are equal,
  whichever Bit the blind request enters the cycle with and whether the
  cycle negates the Bit.
* `letStash_ne_slot`: a changed blind query is distinguished. The let
  that binds the first reply differs from the let that binds the entry
  state.

## Scope

The rows are written programs in `Code 2 1`, with one Bit of entry state.
A row that is not the packed region of such a program is not covered:
nothing is claimed for packed dispatchers in general. No completeness is
claimed for default Paper.
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

open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.BitFragment.Recursive (Normal)

variable {K K₁ K₂ : Nat}

/-! ## The syntactic condition -/

/-- Every request schedule on one slot is the schedule of a mixed row. -/
theorem MixRow.ofNormal_normal (n : Normal 2 1) : (MixRow.ofNormal n).normal = n :=
  Tables.ofNormal_normal n

/-- The program of a mixed row is the code of its schedule. -/
theorem MixRow.program_eq (m : MixRow) : m.program = envCode m.normal :=
  Tables.mixRow_program m

/-- Every router table normalizes to the rows read from its normal forms. -/
theorem Router.normalizes_mixRows (t : Router K) : t.Normalizes t.mixRows :=
  Tables.normalizes_mixRows t

/-! ## The transfer -/

/-- A table of written programs equals the mixed table of the rows it
normalizes to, with the same actions, at every entry. -/
theorem Router.eqv_mixWritten_of_normalizes (t : Router K) (row : Fin (K + 1) → MixRow) (h : t.Normalizes row)
    (j : Fin (K + 1)) : Eqv false [State] (t.entered j) ((mixWritten row t.act).entered j) [Bit] :=
  Tables.mixed_normal_table t row h j

/-- Every table of written programs is a mixed table. -/
theorem Router.eqv_mixWritten (t : Router K) (j : Fin (K + 1)) :
    Eqv false [State] (t.entered j) ((mixWritten t.mixRows t.act).entered j) [Bit] :=
  Tables.written_mixed t j

/-! ## Landings and completeness -/

/-- Every entry of a router table has tidy landings. -/
theorem Router.slanded (t : Router K) (j : Fin (K + 1)) :
    ∃ L : Bool → SLanding, (∀ q, (L q).Tidy) ∧ SLanded (t.entered j) L :=
  Tables.written_slanded t j

/-- Two router tables are equal at given original entries exactly when
they are valid in every supported model. -/
theorem Router.complete (t : Router K₁) (t' : Router K₂) (i₁ : Fin (K₁ + 1)) (i₂ : Fin (K₂ + 1)) :
    Eqv false [State] (t.entered i₁) (t'.entered i₂) [Bit] ↔
      Valid (t.entered_typed i₁).hasType (t'.entered_typed i₂).hasType :=
  Tables.written_complete t t' i₁ i₂

/-! ## Regression -/

theorem letStash_normalizes (l₁ l₂ s n f : Bool) : (letStash l₁ l₂ s n f).Normalizes (stashRow l₁ l₂ s) :=
  Tables.letStash_normalizes l₁ l₂ s n f

/-- The written table with lets equals the mixed table of its rows. -/
theorem letStash_eqv_stash (l₁ l₂ s n f : Bool) (j : Fin 2) :
    Eqv false [State] ((letStash l₁ l₂ s n f).entered j)
      ((mixWritten (stashRow l₁ l₂ s) (stashAct n f)).entered j) [Bit] :=
  Tables.letStash_eqv_stash l₁ l₂ s n f j

/-- Extensionally equivalent presentations are equal. -/
theorem letStash_eqv (l₁ l₂ s n f n' f' : Bool) :
    Eqv false [State] ((letStash l₁ l₂ s n f).entered 0) ((letStash l₁ l₂ s n' f').entered 0) [Bit] :=
  Tables.letStash_eqv l₁ l₂ s n f n' f'

/-- A changed blind query is distinguished. -/
theorem letStash_ne_slot (l₁ l₂ n f n' f' : Bool) :
    ¬ Eqv false [State] ((letStash l₁ l₂ false n f).entered 0) ((letStash l₁ l₂ true n' f').entered 0) [Bit] :=
  Tables.letStash_ne_slot l₁ l₂ n f n' f'

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable

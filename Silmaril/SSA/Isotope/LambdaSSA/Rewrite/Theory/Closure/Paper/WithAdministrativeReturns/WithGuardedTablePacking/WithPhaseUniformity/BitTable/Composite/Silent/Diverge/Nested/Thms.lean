module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Silent.Diverge.Nested.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Silent.Diverge.Query.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.NestedRegression

/-! # Nested request rows with silent divergence, at every original entry

No seed is added. No equality of the quotient is inferred from a model:
equalities are replayed from bisimulations and from the earlier files,
and the query-aware model gives the converse.

## Default Paper: from request trees to a tidy router table

* `TreeTable.outlineAt_spun`: moving an inner request into a new state
  keeps a table one of labelled rows with tidy trees and silent rows.
* `TreeTable.spun_router`: the transfer. Every table of labelled request
  trees and canonical silent rows has a tidy router table of labelled
  rows and canonical silent rows with the same entered loops at the
  images of its states. It is the outlining of `TreeTable.exists_router`
  with the silent rows and tidiness carried through the induction. The
  router table and the map of states are given by existence.
* `Router.ofSpin_entry_bit`: entering a silent row does not depend on the
  Bit.

## The opt-in quotient: every entry of a mixed table

A mixed table has request rows of the environment fragment, with any
number of nested requests, and request-free rows. No ranking and no
condition on cycles is assumed: `mixed_classed` gives a classification.

* `mixWritten_tlanded`: row `j` entered with the constant `q` is a
  returned Bit, or `nestTrees` entered at the split state its silent path
  reaches. The steps are the fold and the elimination of silent paths,
  the dulled table of the cycle lemma, a bisimulation to the table of
  written request rows and silent rows, and the environment
  specialization of each request row at the Bit of its split state.
* `nestTrees_spun`: that table is one of labelled rows with tidy trees
  and silent rows.
* `mixWritten_slanded`: so every entry has landings in the family of
  `SLanding`: a returned Bit, or a tidy router table of labelled rows and
  canonical silent rows entered at a labelled row (a request) or at a
  silent row (silent divergence). Entries at request-free rows are
  included.
* `SLanded.case`: on an arbitrary state, a loop is its two landings
  entered by a case on that state.

## The opt-in quotient: completeness

* `SLanded.complete`: two loops with tidy landings are equal exactly when
  they are valid in every supported model. The converse reads the
  query-aware model: a return has an observation with an empty log and a
  table has none; a labelled row shows its label and query; silent rows
  have no observation, and entering one does not depend on the Bit.
* `mixWritten_complete_all`: two mixed tables are equal at given original
  entries exactly when they are valid in every supported model. There is
  no hypothesis on the tables.

## Regression

`stashRow l₁ l₂ s` with `stashAct n f`: a second request is sent after
the first left reply, queried with the stored first reply or, when `s`,
with the entry Bit. Both of its replies lead into a silent cycle.

* `stash_blind`: the second request is blind.
* `stash_pointed`: the written table is the explicit table
  `Router.ofSpin (stashLabel l₁ l₂) (stashSpun s n)` at each constant.
* `stash_eqv`: equivalent divergent continuations are equal: whichever
  Bit the blind request enters the cycle with, and whether the cycle
  negates the Bit.
* `stash_ne_slot`: the blind request queried with the stored reply
  differs from the blind request queried with the entry Bit.

## Scope

The request rows are rows of the environment fragment: the entry state is
one Bit and the environment holds Bits. Tables of written code with lets
are treated in `Composite.Written`. Nothing is claimed for packed
dispatchers in general, and no completeness is claimed for default Paper.
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


variable {K K₁ K₂ M : Nat}

/-! ## Default Paper: from request trees to a tidy router table -/

/-- Moving an inner request into a new state keeps the table one of
labelled rows with tidy trees and silent rows. -/
theorem TreeTable.outlineAt_spun (t : TreeTable K) (i : Fin (K + 1)) (x y q : Bool) (p : Program)
    (ks : Bool → Bool → Tree K) (h : t.kids i x y = .ask q p ks) (hs : t.Spun) :
    (t.outlineAt i x y q p ks).Spun :=
  Tables.outline_spun t i x y q p ks h hs

/-- Every table of labelled request trees and canonical silent rows has a
tidy router table of labelled rows and canonical silent rows with the
same entered loops, in default Paper. -/
theorem TreeTable.spun_router (t : TreeTable K) (hs : t.Spun) :
    ∃ (M : Nat) (label : Fin (M + 1) → Option Bool) (act : Fin (M + 1) → Bool → Bool → Act M)
      (e : Fin (K + 1) → Fin (M + 1)), Tidy label act ∧
      ∀ j, ofRegion (t.entered_typed j) = ofRegion ((Router.ofSpin label act).entered_typed (e j)) :=
  Tables.spun_router t.asks t (Nat.le_refl _) hs

/-- Entering a silent row does not depend on the Bit, in default Paper. -/
theorem Router.ofSpin_entry_bit (label : Fin (M + 1) → Option Bool) (act : Fin (M + 1) → Bool → Bool → Act M)
    (x : Fin (M + 1)) (hn : label x = none) (q : Bool) :
    ofRegion (const_typed q) ≫ ofRegion ((Router.ofSpin label act).entered_typed x) =
      ofRegion (const_typed false) ≫ ofRegion ((Router.ofSpin label act).entered_typed x) :=
  Tables.spin_entry_bit label act x hn q

/-! ## The opt-in quotient: every entry of a mixed table -/

section Entries

variable {row : Fin (K + 1) → MixRow} {act : Fin (K + 1) → Bool → Bool → Act K}
  {cyc : Fin (K + (K + 1) + 1) → Bool} {fuel : Nat} (hcl : Classed row act cyc fuel)

include hcl in
/-- A mixed table entered with each constant is a returned Bit or the
table of request trees and silent rows at the state its silent path
reaches. -/
theorem mixWritten_tlanded (j : Fin (K + 1)) :
    TLanded ((mixWritten row act).entered j) (nestLanding row act cyc fuel j) :=
  Tables.nest_written_landed row act hcl j

include hcl in
/-- That table is one of labelled rows with tidy trees and silent rows. -/
theorem nestTrees_spun : (nestTrees row act cyc fuel).Spun :=
  Tables.nestTrees_spun row act hcl

end Entries

/-- Every entry of a mixed table has tidy landings: a returned Bit, or a
router table of labelled rows and canonical silent rows. -/
theorem mixWritten_slanded (row : Fin (K + 1) → MixRow) (act : Fin (K + 1) → Bool → Bool → Act K)
    (j : Fin (K + 1)) :
    ∃ L : Bool → SLanding, (∀ q, (L q).Tidy) ∧ SLanded ((mixWritten row act).entered j) L :=
  let ⟨_, _, hcl⟩ := mixed_classed row act
  Tables.mix_slanded row act hcl j

/-- On an arbitrary state, a loop is its two landings entered by a case
on that state. -/
theorem SLanded.case {r : Region signature.Instr} {L : Bool → SLanding} (hl : SLanded r L)
    (h : ValueBranches [State] r [Bit]) :
    Eqv false [State] r (caseEntry (L false).region (L true).region) [Bit] :=
  Tables.slanded_case h hl

/-! ## The opt-in quotient: completeness -/

/-- Two loops with tidy landings are equal exactly when they are valid in
every supported model. -/
theorem SLanded.complete {r r' : Region signature.Instr} {L L' : Bool → SLanding} (hl : SLanded r L)
    (hl' : SLanded r' L') (ht : ∀ q, (L q).Tidy) (ht' : ∀ q, (L' q).Tidy) (h : ValueBranches [State] r [Bit])
    (h' : ValueBranches [State] r' [Bit]) : Eqv false [State] r r' [Bit] ↔ Valid h.hasType h'.hasType :=
  Tables.slanded_complete h h' hl hl' ht ht'

/-- Two mixed tables are equal at given original entries exactly when
they are valid in every supported model. -/
theorem mixWritten_complete_all (row : Fin (K₁ + 1) → MixRow) (act : Fin (K₁ + 1) → Bool → Bool → Act K₁)
    (row' : Fin (K₂ + 1) → MixRow) (act' : Fin (K₂ + 1) → Bool → Bool → Act K₂) (i₁ : Fin (K₁ + 1))
    (i₂ : Fin (K₂ + 1)) :
    Eqv false [State] ((mixWritten row act).entered i₁) ((mixWritten row' act').entered i₂) [Bit] ↔
      Valid ((mixWritten row act).entered_typed i₁).hasType ((mixWritten row' act').entered_typed i₂).hasType :=
  Tables.mix_complete_all row act row' act' i₁ i₂

/-! ## Regression -/

/-- The second request is blind: all of its replies lead to silent rows. -/
theorem stash_blind (l₁ l₂ s n : Bool) (c y tag pl : Bool) :
    ∃ j q, stashSpun s n (stashInner c y) tag pl = .go j q ∧ stashLabel l₁ l₂ j = none :=
  Tables.stash_blind l₁ l₂ s n c y tag pl

theorem stash_tidy (l₁ l₂ s n : Bool) : Tidy (stashLabel l₁ l₂) (stashSpun s n) :=
  Tables.stash_tidy l₁ l₂ s n

/-- The written table entered at the request row with each constant is
the explicit table of labelled rows and silent rows, entered at the copy
of the request row for that constant. -/
theorem stash_pointed (l₁ l₂ s n f : Bool) :
    SpinPointed ((mixWritten (stashRow l₁ l₂ s) (stashAct n f)).entered 0) (stashLabel l₁ l₂) (stashSpun s n)
      stashEntry :=
  Tables.stash_pointed l₁ l₂ s n f

/-- Equivalent divergent continuations are equal. -/
theorem stash_eqv (l₁ l₂ s n f n' f' : Bool) :
    Eqv false [State] ((mixWritten (stashRow l₁ l₂ s) (stashAct n f)).entered 0)
      ((mixWritten (stashRow l₁ l₂ s) (stashAct n' f')).entered 0) [Bit] :=
  Tables.stash_eqv l₁ l₂ s n f n' f'

/-- The blind request queried with the stored first reply differs from
the blind request queried with the entry Bit. -/
theorem stash_ne_slot (l₁ l₂ n f n' f' : Bool) :
    ¬ Eqv false [State] ((mixWritten (stashRow l₁ l₂ false) (stashAct n f)).entered 0)
      ((mixWritten (stashRow l₁ l₂ true) (stashAct n' f')).entered 0) [Bit] :=
  Tables.stash_ne_slot l₁ l₂ n f n' f'

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable

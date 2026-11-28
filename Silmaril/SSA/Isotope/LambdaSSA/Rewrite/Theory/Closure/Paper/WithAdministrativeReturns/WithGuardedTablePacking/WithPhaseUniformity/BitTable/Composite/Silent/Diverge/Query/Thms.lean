module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Silent.Diverge.Query.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Silent.Diverge.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.QueryTables

/-! # Blind requests: a model whose pending observation carries the query

No seed is added and the quotient is unchanged. No equality of the
quotient is inferred from a model: equalities are replayed from
bisimulations, and the models give the converse.

## The model is supported

`queryModel` differs from the request-prefix model in one place: the log
of a pending request ends with the mark of that request, which carries
its query. `queryCoherent` is its region typing coherence. It has the
monad and iterator of the request-prefix model, so it is in the class of
models that `Valid` ranges over, and every equation of the unchanged
quotient holds in it (`Router.query_of_valid`, `Router.query_of_eqv`).
No law of the quotient had to be checked against it separately, and none
forces a pending query to be erased.

## Reflection without sightedness

* `Router.ofSpin_queryObservations`: the observation law at a labelled
  row: the pending request with its mark, or one completed exchange
  followed by what its action allows.
* `Router.ofSpin_queryObservations_none`: a silent row has no
  observation.
* `Router.ofSpin_query_bisimulation`: for tidy tables, equal observations
  are a bisimulation. The pending request shows the label and the query,
  so no reply has to be observed after.
* `Router.ofSpin_eqv_iff_query`, `Router.ofSpin_eqv_iff_valid`: tidy
  tables have equal entered loops exactly when their observations in this
  model are equal, and exactly when they are valid in every supported
  model.
* `SpinPointed.complete_tidy`, `mixWritten_complete_tidy`: the
  completeness theorems of `Composite.Silent.Diverge` without `Sighted`.

## Regression: a blind request

`blindLabel m l` with `blindAct s`: a labelled row repeats with the query
`s` to a blind request, all of whose replies lead to a silent row.

* `blind_prefix_observations`: the request-prefix model gives the two
  tables the same observations for every `s`.
* `blind_queryObservations`: in the query-aware model the blind request
  shows its label and its query.
* `blind_eqv_iff`: the two loops are equal in the quotient exactly when
  the queries are equal. So the tables with different queries are
  separated in the quotient, by a supported model.

Equal divergent continuations stay equal: `veer_eqv` and
`Router.ofSpin_congr` are equalities of the quotient and do not depend on
a model. `veer_queryObservations`: the four presentations of a reply that
leads into a silent cycle have the same observations in the query-aware
model too.

## Scope

The tables are router tables of labelled rows and canonical silent rows,
and mixed tables whose request rows are single requests. Request rows
with nested requests are treated in `Composite.Silent.Diverge.Nested`.
Nothing is claimed for default Paper.
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

open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree (Word event)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli (value)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (bit)

variable {K K₁ K₂ M M' : Nat}

/-! ## The model is supported -/

/-- Valid loops have the same observations in the query-aware model. -/
theorem Router.query_of_valid {t : Router M} {t' : Router M'} {i : Fin (M + 1)} {i' : Fin (M' + 1)}
    (h : Valid (t.entered_typed i).hasType (t'.entered_typed i').hasType) (g : Bool) :
    t.queryObservations i g = t'.queryObservations i' g :=
  TableModel.query_obs_of_valid h g

/-- So do loops that are equal in the quotient. -/
theorem Router.query_of_eqv {t : Router M} {t' : Router M'} {i : Fin (M + 1)} {i' : Fin (M' + 1)}
    (e : Eqv false [State] (t.entered i) (t'.entered i') [Bit]) (g : Bool) :
    t.queryObservations i g = t'.queryObservations i' g :=
  Router.query_of_valid (valid_of_eqv false e _ _) g

/-! ## Reflection without sightedness -/

section Observations

variable (label : Fin (M + 1) → Option Bool) (act : Fin (M + 1) → Bool → Bool → Act M)

/-- The observation law at a labelled row. -/
theorem Router.ofSpin_queryObservations (i : Fin (M + 1)) {l : Bool} (hl : label i = some l) (g : Bool)
    (r : Except Bool (value Bit)) (w : Word) :
    (r, w) ∈ (Router.ofSpin label act).queryObservations i g ↔
      (r = .error l ∧ w = pendingWord l g) ∨
        ∃ tag pl v, w = FreeMonoid.of (event l g (tag, pl)) * v ∧
          (Router.ofSpin label act).QueryCont (act i tag pl) r v :=
  TableModel.query_unfold label act i hl g r w

/-- A silent row has no observation. -/
theorem Router.ofSpin_queryObservations_none (i : Fin (M + 1)) (hn : label i = none) (g : Bool) :
    (Router.ofSpin label act).queryObservations i g = ∅ :=
  TableModel.query_empty label act i hn g

/-- A blind row shows its pending request with its query. -/
theorem Router.ofSpin_query_blind (i : Fin (M + 1)) {l : Bool} (hl : label i = some l)
    (blind : ∀ tag pl, ∃ j q, act i tag pl = .go j q ∧ label j = none) (g : Bool) :
    (Router.ofSpin label act).queryObservations i g = {(Except.error l, pendingWord l g)} :=
  TableModel.query_blind label act i hl blind g

end Observations

section Reflection

variable {label : Fin (M + 1) → Option Bool} {act : Fin (M + 1) → Bool → Bool → Act M}
  {label' : Fin (M' + 1) → Option Bool} {act' : Fin (M' + 1) → Bool → Bool → Act M'}
  (ht : Tidy label act) (ht' : Tidy label' act')

include ht ht' in
/-- Equal observations in the query-aware model are a bisimulation. -/
theorem Router.ofSpin_query_bisimulation :
    Router.Bisimulation (Router.ofSpin label act) (Router.ofSpin label' act')
      (fun j j' => ∃ q, (Router.ofSpin label act).queryObservations j q =
        (Router.ofSpin label' act').queryObservations j' q) :=
  TableModel.query_bisim label act label' act' ht ht'

include ht ht' in
/-- Tidy tables have equal entered loops exactly when their observations
in the query-aware model are equal. -/
theorem Router.ofSpin_eqv_iff_query (i : Fin (M + 1)) (i' : Fin (M' + 1)) :
    Eqv false [State] ((Router.ofSpin label act).entered i) ((Router.ofSpin label' act').entered i') [Bit] ↔
      (Router.ofSpin label act).queryObservations i false =
        (Router.ofSpin label' act').queryObservations i' false :=
  Tables.tidy_eqv_iff_query ht ht' i i'

include ht ht' in
/-- And exactly when they are valid in every supported model. -/
theorem Router.ofSpin_eqv_iff_valid (i : Fin (M + 1)) (i' : Fin (M' + 1)) :
    Eqv false [State] ((Router.ofSpin label act).entered i) ((Router.ofSpin label' act').entered i') [Bit] ↔
      Valid ((Router.ofSpin label act).entered_typed i).hasType
        ((Router.ofSpin label' act').entered_typed i').hasType :=
  Tables.tidy_eqv_iff_valid ht ht' i i'

end Reflection

/-- Two loops that are tidy tables with silent rows at each constant are
equal exactly when they are valid in every supported model. -/
theorem SpinPointed.complete_tidy {label : Fin (M + 1) → Option Bool}
    {act : Fin (M + 1) → Bool → Bool → Act M} {label' : Fin (M' + 1) → Option Bool}
    {act' : Fin (M' + 1) → Bool → Bool → Act M'} {r r' : Region signature.Instr} {x : Bool → Fin (M + 1)}
    {x' : Bool → Fin (M' + 1)} (hp : SpinPointed r label act x) (hp' : SpinPointed r' label' act' x')
    (ht : Tidy label act) (ht' : Tidy label' act') (h : ValueBranches [State] r [Bit])
    (h' : ValueBranches [State] r' [Bit]) : Eqv false [State] r r' [Bit] ↔ Valid h.hasType h'.hasType :=
  Tables.tidy_pointed_complete ht ht' h h' hp hp'

/-- Two classified mixed tables of single requests are equal at given
request rows exactly when they are valid in every supported model. -/
theorem mixWritten_complete_tidy {row : Fin (K₁ + 1) → MixRow} {act : Fin (K₁ + 1) → Bool → Bool → Act K₁}
    {cyc : Fin (K₁ + (K₁ + 1) + 1) → Bool} {fuel : Nat} (hcl : Classed row act cyc fuel) (hp : Polled row)
    {row' : Fin (K₂ + 1) → MixRow} {act' : Fin (K₂ + 1) → Bool → Bool → Act K₂}
    {cyc' : Fin (K₂ + (K₂ + 1) + 1) → Bool} {fuel' : Nat} (hcl' : Classed row' act' cyc' fuel')
    (hp' : Polled row') (i₁ : Fin (K₁ + 1)) {r₁ : EnvRow} (h₁ : row i₁ = .ask r₁) (i₂ : Fin (K₂ + 1))
    {r₂ : EnvRow} (h₂ : row' i₂ = .ask r₂) :
    Eqv false [State] ((mixWritten row act).entered i₁) ((mixWritten row' act').entered i₂) [Bit] ↔
      Valid ((mixWritten row act).entered_typed i₁).hasType ((mixWritten row' act').entered_typed i₂).hasType :=
  (mixWritten_spinPointed hcl hp i₁ h₁).complete_tidy (mixWritten_spinPointed hcl' hp' i₂ h₂)
    (spunRouter_tidy hcl) (spunRouter_tidy hcl') ((mixWritten row act).entered_typed i₁)
    ((mixWritten row' act').entered_typed i₂)

/-! ## Regression: a blind request -/

/-- The request-prefix model gives the two tables the same observations. -/
theorem blind_prefix_observations (m l s s' g : Bool) :
    (Router.ofSpin (blindLabel m l) (blindAct s)).prefixObservations 0 g =
      (Router.ofSpin (blindLabel m l) (blindAct s')).prefixObservations 0 g :=
  Tables.blind_prefix_obs m l s s' g

/-- In the query-aware model the blind request shows its query. -/
theorem blind_queryObservations (m l s g : Bool) :
    (Router.ofSpin (blindLabel m l) (blindAct s)).queryObservations 1 g = {(Except.error l, pendingWord l g)} :=
  Tables.blind_query_obs m l s g

/-- The same blind request with different queries: the loops are equal
exactly when the queries are. -/
theorem blind_eqv_iff (m l s s' : Bool) :
    Eqv false [State] ((Router.ofSpin (blindLabel m l) (blindAct s)).entered 0)
      ((Router.ofSpin (blindLabel m l) (blindAct s')).entered 0) [Bit] ↔ s = s' :=
  Tables.blind_eqv_iff m l s s'

/-- The presentations of a reply that leads into a silent cycle have the
same observations in the query-aware model. -/
theorem veer_queryObservations (l n f n' f' g : Bool) :
    (mixWritten (veerRow l) (veerAct n f)).queryObservations 0 g =
      (mixWritten (veerRow l) (veerAct n' f')).queryObservations 0 g :=
  Router.query_of_eqv (veer_eqv l n f n' f') g

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable

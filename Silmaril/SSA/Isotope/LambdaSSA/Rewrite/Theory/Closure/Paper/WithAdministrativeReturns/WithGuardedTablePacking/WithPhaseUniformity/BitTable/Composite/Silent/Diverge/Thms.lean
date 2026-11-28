module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Silent.Diverge.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Silent.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.SpinTables

/-! # Silent divergence after a visible request

No seed is added. Nothing here is inferred from a model: the equalities
are replayed from bisimulations, and the model is used only for the
converse.

## Tables with the canonical silent row

`Router.ofSpin label act` has labelled rows and canonical silent rows. A
reply that leads to silent divergence repeats to a silent row.

* `Router.ofSpin_observations`: the observation law at a labelled row, in
  the request-prefix model: the pending request, or one completed
  exchange followed by what its action allows.
* `Router.ofSpin_observations_none`: a silent row has no observation.
* `Router.ofSpin_bisimulation`: prefix reflection. For tidy tables, the
  first of them sighted, equal prefix observations are a bisimulation.
  The pending request gives the label. Each reply gives the same returned
  Bit, successors with equal observations, or silent rows on both sides,
  whose observations are empty.
* `Router.ofSpin_eqv_iff_prefix`: so the entered loops are equal exactly
  when their prefix observations are equal.
* `Router.ofSpin_congr`: two presentations whose labelled rows agree up
  to which silent row a diverging reply repeats to are equal.

## The failed observation: a blind request

`Router.ofSpin_blind`: a labelled row all of whose replies lead to silent
rows shows only its pending request, and `Router.ofSpin_blind_query`: its
observations do not depend on its query. The request-prefix model records
the label of a pending request and records a query only in a completed
exchange after which something is observed. So two loops that send the
same blind request with different queries have the same observations in
that model, and no equation of the quotient relating them is proved
here. `Sighted` excludes this case in this file.
`Composite.Silent.Diverge.Query` removes the condition with a model whose
pending observation carries the query.

## Mixed tables of single requests, without `quiet`

* `mixed_classed`: every mixed table has a classification `Classed`.
  This is `silent_classification`.
* `mixWritten_spinPointed`: a classified mixed table whose request rows
  are single requests, entered at a request row with each constant, is
  `spunRouter` entered with that constant. The steps are the fold and the
  elimination of the earlier files, the dulled table of the cycle lemma
  (default Paper), and a bisimulation from the dulled table to
  `spunRouter`.
* `spunRouter_tidy`: that table is tidy.
* `SpinPointed.complete`: two such loops, tidy and the first sighted, are
  equal exactly when they are valid in every supported model.
* `mixWritten_complete_spun`: the instance for mixed tables of single
  requests at request rows. A request row may repeat into a silent cycle.

## Regression

`veerRow` with `veerAct n f`: the left reply of a request leads into a
silent cycle; `f` makes the cycle negate the Bit and `n` negates the Bit
on the way in.

* `veer_eqv`: all four presentations are equal.
* `veer_ne_ret`: they differ from the table whose left reply returns.
* `veer_ne_again`: and from the table whose left reply sends the request
  again.

## What remains

Request rows with nested requests and entries at request-free rows are
not covered in this file. `Composite.Silent.Diverge.Nested` treats both,
with one family of landings. No completeness is claimed for default
Paper.
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

/-! ## Tables with the canonical silent row -/

/-- A table of labelled rows is a table with no silent row. -/
theorem Router.ofLabels_eq_ofSpin (label : Fin (M + 1) → Bool) (act : Fin (M + 1) → Bool → Bool → Act M) :
    Router.ofLabels label act = Router.ofSpin (fun i => some (label i)) act := rfl

section Observations

variable (label : Fin (M + 1) → Option Bool) (act : Fin (M + 1) → Bool → Bool → Act M)

/-- The observation law at a labelled row. -/
theorem Router.ofSpin_observations (i : Fin (M + 1)) {l : Bool} (hl : label i = some l) (g : Bool)
    (r : Except Bool (value Bit)) (w : Word) :
    (r, w) ∈ (Router.ofSpin label act).prefixObservations i g ↔
      (r = .error l ∧ w = 1) ∨
        ∃ tag pl v, w = FreeMonoid.of (event l g (tag, pl)) * v ∧
          (Router.ofSpin label act).PrefixCont (act i tag pl) r v :=
  TableModel.spin_unfold label act i hl g r w

/-- A silent row has no observation. -/
theorem Router.ofSpin_observations_none (i : Fin (M + 1)) (hn : label i = none) (g : Bool) :
    (Router.ofSpin label act).prefixObservations i g = ∅ :=
  TableModel.spin_empty label act i hn g

/-- A blind row shows only its pending request. -/
theorem Router.ofSpin_blind (i : Fin (M + 1)) {l : Bool} (hl : label i = some l)
    (blind : ∀ tag pl, ∃ j q, act i tag pl = .go j q ∧ label j = none) (g : Bool) :
    (Router.ofSpin label act).prefixObservations i g = {(Except.error l, 1)} :=
  TableModel.blind_obs label act i hl blind g

/-- The query of a blind request is not observed. -/
theorem Router.ofSpin_blind_query (i : Fin (M + 1)) {l : Bool} (hl : label i = some l)
    (blind : ∀ tag pl, ∃ j q, act i tag pl = .go j q ∧ label j = none) (g g' : Bool) :
    (Router.ofSpin label act).prefixObservations i g = (Router.ofSpin label act).prefixObservations i g' :=
  (Router.ofSpin_blind label act i hl blind g).trans (Router.ofSpin_blind label act i hl blind g').symm

end Observations

section Reflection

variable {label : Fin (M + 1) → Option Bool} {act : Fin (M + 1) → Bool → Bool → Act M}
  {label' : Fin (M' + 1) → Option Bool} {act' : Fin (M' + 1) → Bool → Bool → Act M'}
  (ht : Tidy label act) (ht' : Tidy label' act') (hs : Sighted label act)

include ht ht' hs in
/-- Equal prefix observations are a bisimulation. -/
theorem Router.ofSpin_bisimulation :
    Router.Bisimulation (Router.ofSpin label act) (Router.ofSpin label' act')
      (fun j j' => ∃ q, (Router.ofSpin label act).prefixObservations j q =
        (Router.ofSpin label' act').prefixObservations j' q) :=
  TableModel.spin_bisim label act label' act' ht ht' hs

include ht ht' hs in
/-- The entered loops are equal exactly when their prefix observations
are equal. -/
theorem Router.ofSpin_eqv_iff_prefix (i : Fin (M + 1)) (i' : Fin (M' + 1)) :
    Eqv false [State] ((Router.ofSpin label act).entered i) ((Router.ofSpin label' act').entered i') [Bit] ↔
      (Router.ofSpin label act).prefixObservations i false =
        (Router.ofSpin label' act').prefixObservations i' false :=
  ⟨fun e => TableModel.prefix_obs_of_eqv e false,
    fun h => TableModel.spin_eqv_of_obs label act label' act' ht ht' hs i i' false h⟩

end Reflection

/-- Two presentations whose labelled rows agree up to which silent row a
diverging reply repeats to are equal. -/
theorem Router.ofSpin_congr (label : Fin (M + 1) → Option Bool) (act act' : Fin (M + 1) → Bool → Bool → Act M)
    (h : ∀ x l, label x = some l → ∀ a b,
      Act.Rel (fun j j' => j = j' ∨ (label j = none ∧ label j' = none)) (act x a b) (act' x a b))
    (x : Fin (M + 1)) :
    Eqv false [State] ((Router.ofSpin label act).entered x) ((Router.ofSpin label act').entered x) [Bit] :=
  Tables.spin_router_congr label act act' h x

/-! ## Mixed tables of single requests -/

/-- Every mixed table has a classification. -/
theorem mixed_classed (row : Fin (K + 1) → MixRow) (act : Fin (K + 1) → Bool → Bool → Act K) :
    ∃ cyc fuel, Classed row act cyc fuel :=
  let ⟨cyc, fuel, hc, hs⟩ := silent_classification (mixSil row act)
  ⟨cyc, fuel, hc, hs⟩

section Spun

variable {row : Fin (K + 1) → MixRow} {act : Fin (K + 1) → Bool → Bool → Act K}
  {cyc : Fin (K + (K + 1) + 1) → Bool} {fuel : Nat} (hcl : Classed row act cyc fuel)

include hcl in
/-- The table of labelled and silent rows of a mixed table is tidy. -/
theorem spunRouter_tidy : Tidy (spunLabel row) (spunAct row act cyc fuel) :=
  Tables.spun_tidy row act hcl

include hcl in
/-- A mixed table of single requests, entered at a request row with each
constant, is its table of labelled rows and canonical silent rows. -/
theorem mixWritten_spinPointed (hp : Polled row) (j : Fin (K + 1)) {r : EnvRow} (hj : row j = .ask r) :
    SpinPointed ((mixWritten row act).entered j) (spunLabel row) (spunAct row act cyc fuel) (splitIdx j) :=
  Tables.spin_pointed_congr ((mixWritten row act).entered_typed j) ((mixRouter row act).entered_typed j)
    (.paper ((Paper.TypeCategory.ofRegion_eq_iff _ _).mp (mixWritten_arrow_mixRouter row act j)))
    (Tables.spun_pointed row act hcl hp j hj)

end Spun

/-- Tidy tables with silent rows, the first sighted: two loops that are
such tables at each constant are equal exactly when they are valid in
every supported model. -/
theorem SpinPointed.complete {label : Fin (M + 1) → Option Bool} {act : Fin (M + 1) → Bool → Bool → Act M}
    {label' : Fin (M' + 1) → Option Bool} {act' : Fin (M' + 1) → Bool → Bool → Act M'}
    {r r' : Region signature.Instr} {x : Bool → Fin (M + 1)} {x' : Bool → Fin (M' + 1)}
    (hp : SpinPointed r label act x) (hp' : SpinPointed r' label' act' x') (ht : Tidy label act)
    (ht' : Tidy label' act') (hs : Sighted label act) (h : ValueBranches [State] r [Bit])
    (h' : ValueBranches [State] r' [Bit]) : Eqv false [State] r r' [Bit] ↔ Valid h.hasType h'.hasType :=
  Tables.spin_pointed_complete ht ht' hs h h' hp hp'

/-- Two classified mixed tables of single requests, the first sighted,
are equal at given request rows exactly when they are valid in every
supported model. A request row may repeat into a silent cycle. -/
theorem mixWritten_complete_spun {row : Fin (K₁ + 1) → MixRow} {act : Fin (K₁ + 1) → Bool → Bool → Act K₁}
    {cyc : Fin (K₁ + (K₁ + 1) + 1) → Bool} {fuel : Nat} (hcl : Classed row act cyc fuel) (hp : Polled row)
    (hs : Sighted (spunLabel row) (spunAct row act cyc fuel))
    {row' : Fin (K₂ + 1) → MixRow} {act' : Fin (K₂ + 1) → Bool → Bool → Act K₂}
    {cyc' : Fin (K₂ + (K₂ + 1) + 1) → Bool} {fuel' : Nat} (hcl' : Classed row' act' cyc' fuel')
    (hp' : Polled row') (i₁ : Fin (K₁ + 1)) {r₁ : EnvRow} (h₁ : row i₁ = .ask r₁) (i₂ : Fin (K₂ + 1))
    {r₂ : EnvRow} (h₂ : row' i₂ = .ask r₂) :
    Eqv false [State] ((mixWritten row act).entered i₁) ((mixWritten row' act').entered i₂) [Bit] ↔
      Valid ((mixWritten row act).entered_typed i₁).hasType ((mixWritten row' act').entered_typed i₂).hasType :=
  (mixWritten_spinPointed hcl hp i₁ h₁).complete (mixWritten_spinPointed hcl' hp' i₂ h₂) (spunRouter_tidy hcl)
    (spunRouter_tidy hcl') hs ((mixWritten row act).entered_typed i₁) ((mixWritten row' act').entered_typed i₂)

/-! ## Regression -/

/-- Two presentations of the same divergent continuation: whichever Bit
the reply enters the cycle with, and whether the cycle negates the Bit. -/
theorem veer_eqv (l n f n' f' : Bool) :
    Eqv false [State] ((mixWritten (veerRow l) (veerAct n f)).entered 0)
      ((mixWritten (veerRow l) (veerAct n' f')).entered 0) [Bit] :=
  Tables.veer_eqv l n f n' f'

/-- A reply that leads into the silent cycle is not a reply that returns. -/
theorem veer_ne_ret (l n f : Bool) :
    ¬ Eqv false [State] ((mixWritten (veerRow l) (veerAct n f)).entered 0)
      ((mixWritten (veerRow l) veerRet).entered 0) [Bit] :=
  Tables.veer_ne_ret l n f

/-- Nor a reply after which the request is sent again. -/
theorem veer_ne_again (l n f : Bool) :
    ¬ Eqv false [State] ((mixWritten (veerRow l) (veerAct n f)).entered 0)
      ((mixWritten (veerRow l) veerAgain).entered 0) [Bit] :=
  Tables.veer_ne_again l n f

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
